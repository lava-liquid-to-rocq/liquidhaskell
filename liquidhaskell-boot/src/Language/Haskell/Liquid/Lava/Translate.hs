{-# LANGUAGE GADTs #-}

module Language.Haskell.Liquid.Lava.Translate (runLava, SrcInfo (..)) where

import Control.Monad (when)
import qualified Data.Bifunctor as B
import Data.Char (isSpace)
import Data.List
import qualified Data.Map as M
import GHC.Core
import GHC.Plugins hiding (Id, split)
import qualified Language.Fixpoint.Types as F (val)
import qualified Language.Haskell.Liquid.Lava.CoreToLH as CLH
import Language.Haskell.Liquid.Lava.Parse
import Language.Haskell.Liquid.Lava.Preamble (preamble)
import Language.Haskell.Liquid.Lava.Print
import Language.Haskell.Liquid.Lava.Simplify (simplify)
import qualified Language.Haskell.Liquid.Lava.SpecToLH as SLH
import Language.Haskell.Liquid.Types.RType (SpecType)
import qualified Language.Haskell.Liquid.Types.Specs as Specs
import Language.Haskell.Liquid.Types.Types (AnnInfo (..))
import qualified Lava.Coq as Coq (Decl)
import qualified Lava.InternalLH as InternalLH (ArrType, LHDecl (Import))
import Lava.LH
import Lava.Misc (isIgnoredBind, stripLegalName)
import Lava.TypedTranslation (translateTyping)
import Lava.Util
import System.Directory
import Prelude

-- ^ Contains all information about the source Liquid Haskell file to translate

data SrcInfo = SrcInfo
  { -- | the name of the module associated to the file (exactly one)
    s_moduleName :: ModuleName,
    -- | GHC's information about the module
    s_summary :: ModSummary,
    -- | Liquid Haskell's TargetInfo structure
    s_targetInfo :: Specs.TargetInfo,
    -- | Liquid Haskell's location to inferred types map
    s_infTypes :: AnnInfo SpecType
  }

-- | The main function of the plugin
runLava :: SrcInfo -> IO ()
runLava sinfo = do
  let filepath = Specs.giTarget $ Specs.giSrc $ s_targetInfo sinfo
  _ <- translateFile True sinfo filepath
  return ()

-- | parses file into [InternalLH.LHDecl]
parseFile ::
  -- | Whether output files for ILH should be generated
  Bool ->
  -- | All information about the Liquid Haskell file to translate
  SrcInfo ->
  -- | Complete file name
  String ->
  IO ([InternalLH.LHDecl], ([InternalLH.LHDecl], Id, Id))
parseFile writeFlag sinfo filename = do
  -- \| Step 1: Setting up the environment
  workingPath <- getCurrentDirectory
  let moduleId = takeWhile (not . isSpace) $ moduleNameString (s_moduleName sinfo)
  let modulename = last $ split '.' moduleId
  let examplesFolder = getSrcFolder moduleId filename workingPath

  -- \| Step 2: Get information from LH:
  let (src, vars, decls, binds, specs) = B.first (filter (not . isIgnoredBind)) $ getBindsAndSpecs moduleId sinfo
  let importNames = getModIdsAndImports src

  -- \| Step 3: Get the ILH source and the imported files
  -- This "translates" from Liquid Haskell and GHC data structures to lh-to-coq.InternalLH data structures,
  -- furthermore transSig removes LH internal refinements from data constructors (like no-junk and no-confusion refinements)
  -- and parseSourceContent gives arguments a unique name in specs

  -- \| translate the LH type constructors to ILH type constructors
  let dataDecls = parsePData moduleId decls
  -- \| translate the LH specs of function/theorem definitions to ILH data structures
  let specMap = SLH.transSig moduleId Nothing <$> M.fromList specs
  -- \| translate the GHC binds of function/theorem definitions to ILH data structures
  let lhDefs = map (CLH.transBind moduleId (s_infTypes sinfo)) (simplify <$> binds)
  -- \| combine the translated LH specs and GHC binds for function/theorem definitions into ILH declarations
  let defDecls = combineDefsAndLemmas $ pairLHDefsWithSigs moduleId lhDefs specMap vars

  -- \| figure out the ILH import declarations for the imported lhExample modules and their files
  importedSourceFiles <- getImportFiles examplesFolder importNames
  importedDecls <- map fst <$> mapM (parseFile False sinfo) importedSourceFiles
  let imports = zipWith InternalLH.Import importNames importedDecls

  -- \| Step 3: Do the translation to ECoq
  putStrLn $ "Input file: " ++ filename

  -- Thanks to sinfo, this will also produce declarations from this rather than from the imported modules
  _ <- concat <$> mapM (translateFile False sinfo) importedSourceFiles

  let hasImports = not $ null imports
      sortedImports = topologicalSort imports
      ilhSource :: [InternalLH.LHDecl]
      ilhSource = sortedImports ++ topologicalSort (dataDecls ++ defDecls)

      outputFolder = getOutputFolder moduleId filename workingPath

  when hasImports $ putStrLn ("Imported external files: " ++ intercalate ", " importedSourceFiles)

  when
    writeFlag
    ( do
        createDirectoryIfMissing True outputFolder
        writeOut outputFolder modulename ILH [] ilhSource
    )
  putStrLn ""

  pure (ilhSource, (sortedImports, outputFolder, modulename))

-- | Calls translation function on source file and (optionally) writes (intermediate) output files in output folder
translateFile ::
  -- | Whether output files for ILH, ECoq and Coq should be generated
  Bool ->
  -- | All information about the Liquid Haskell file to translate
  SrcInfo ->
  -- | Complete file name
  String ->
  IO [Coq.Decl]
translateFile writeFlag sinfo arg = do
  (ilhSource, (imports, outputFolder, modulename)) <- parseFile writeFlag sinfo arg

  let hasImports = not $ null imports

      extendedCoqContent :: IO [Coq.Decl]
      extendedCoqContent = case translateTyping ilhSource of
        Left err ->
          print err >> return []
        Right paper ->
          putStrLn "—— Typechecking OK ——"
            >> return paper

  -- \| Step 4: Write output files
  when
    writeFlag
    ( do
        let coqPreamble = if hasImports then [] else preamble
        output <- extendedCoqContent
        writeOut outputFolder modulename Coq coqPreamble output
    )
  putStrLn ""

  extendedCoqContent

writeOut :: (Show a) => String -> String -> OUT -> [String] -> [a] -> IO ()
writeOut outputFolder modulename outType pre ilhSource = do
  let ilhOutputPath = outputFolder ++ modulename ++ outPostfix outType
  putStrLn ("Writing " ++ show outType ++ " output to file at " ++ ilhOutputPath)
  let ilhOutput = intercalate "\n" (pre ++ map show ilhSource)
  writeFile ilhOutputPath ilhOutput

-- | Get the stuff that we need from LH parser, namely: Binds and Specs.
getBindsAndSpecs ::
  Id ->
  SrcInfo ->
  ( Specs.TargetSrc,
    -- \^ TargetSrc contained in the input
    [Var],
    -- \^ Binders for reflected functions
    PData,
    -- \^ Refined types of (data, type) constructors
    [CoreBind],
    -- \^ Source code (list of top-level bindings)
    [SpecPair]
  )
-- \^ ?? LP:What are the variables for which we get the refined types?

getBindsAndSpecs modId sinfo =
  let (Specs.TargetInfo src specs) = s_targetInfo sinfo
      refls = Specs.gsReflects $ Specs.gsRefl specs
   in (src, refls, getDataDecls (Specs.gsData specs, Specs.gsName specs), Specs.giCbs src, getSpecPairs specs)
  where
    getSpecPairs :: Specs.TargetSpec -> [SpecPair]
    getSpecPairs = map (B.bimap (stripLegalName modId . show) F.val) . Specs.gsTySigs . Specs.gsSig

    getDataDecls :: (Specs.GhcSpecData, Specs.GhcSpecNames) -> PData
    getDataDecls (spdata, spnames) =
      -- NV TODO: filter out the data constructors and type constructors that are not defined in t
      -- the currect module.
      (Specs.gsCtors spdata, Specs.gsTconsP spnames) -- , Specs.gsDconsP spnames, Specs.gsADTs spnames)

-- | Returns the absolute path of the root directory of the files to translate as a list
getSrcPath :: String -> String -> String -> [String]
getSrcPath moduleId filename workingPath = removeSuffix modulePrefixes folderPath
  where
    modulePrefixes = init $ split '.' moduleId

    inputFilePath = split '/' (workingPath ++ "/" ++ filename)
    folderPath = init inputFilePath

-- | Return the absolute path of the root directory of the files to translate
getSrcFolder :: String -> String -> String -> String
getSrcFolder moduleId filename workingPath = concatMap (++ "/") $ getSrcPath moduleId filename workingPath

-- | Returns the output directory for generated files
getOutputFolder :: String -> String -> String -> String
getOutputFolder moduleId filename workingPath = outputFolder
  where
    modulePrefixes = init $ split '.' moduleId

    exampleFolderPath = getSrcPath moduleId filename workingPath
    implementationFolder = intercalate "/" . init . init $ exampleFolderPath
    subfolder = concatMap (++ "/") modulePrefixes
    outputFolder = implementationFolder ++ "/lava/out/" ++ subfolder

-- TODO: gsAllImps does not exist anymore (since commit 99f6d787b15e63bbc4b939a950d8babce97469cd)
-- maybe use allImports instead of Specs.gsAllImps (see Plugin.hs)
getModIdsAndImports :: Specs.TargetSrc -> [String]
-- getModIdsAndImports src = map symbolString . H.toList $ Specs.gsAllImps src
-- getModIdsAndImports src = error $ "TODO: imports"
getModIdsAndImports _ = []

pairLHDefsWithSigs :: Id -> [Def] -> M.Map Id InternalLH.ArrType -> [Var] -> [(Def, Maybe InternalLH.ArrType, Bool)]
pairLHDefsWithSigs modId defs specMap reflectedDecls = map single defs
  where
    single :: Def -> (Def, Maybe InternalLH.ArrType, Bool)
    single def@(x, _, _, _) = (def, M.lookup x specMap, any ((== x) . stripLegalName modId . show . varName) reflectedDecls)
