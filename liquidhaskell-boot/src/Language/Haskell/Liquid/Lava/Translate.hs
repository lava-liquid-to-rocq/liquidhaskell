{-# OPTIONS_GHC -Wall #-}

module Language.Haskell.Liquid.Lava.Translate (runLava, SrcInfo (..)) where

import           Control.Monad (void, unless, when)
import           Data.Bifunctor (bimap)
import           Data.Char (isSpace)
import           Data.Foldable (traverse_)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import           System.Directory (createDirectoryIfMissing, getCurrentDirectory)
import           System.FilePath ((</>), joinPath, splitDirectories, takeDirectory)

import           GHC.Core
import           GHC.Plugins hiding (Id, split)

import qualified Language.Fixpoint.Types as F (val)
import           Language.Haskell.Liquid.Types.RType (SpecType)
import qualified Language.Haskell.Liquid.Types.Specs as Specs
import           Language.Haskell.Liquid.Types.Types (AnnInfo (..))

import qualified Lava.Calculus as Calc
import qualified Lava.Coq as Coq (Decl, Decl (..))
import           Lava.Declaration (trDecl)
import           Lava.LH
import           Lava.Misc (isIgnoredBind, stripLegalName)
import           Lava.Util

import           Language.Haskell.Liquid.Lava.Preamble (preamble)
import           Language.Haskell.Liquid.Lava.Print
import qualified Language.Haskell.Liquid.Lava.SpecToLH as SLH
import qualified Language.Haskell.Liquid.Lava.CoreToLH as CLH
import           Language.Haskell.Liquid.Lava.Parse
import           Language.Haskell.Liquid.Lava.Simplify (simplify)

-- | Contains all information about the source Liquid Haskell file to translate
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
  void $ translateFile True sinfo filepath

-- | parses file into [Calc.Decl]
parseFile ::
  -- | Whether output files should be generated
  Bool ->
  -- | All information about the Liquid Haskell file to translate
  SrcInfo ->
  -- | Complete file name
  String ->
  IO ([Calc.Decl], ([String], Id, Id))
parseFile writeFlag sinfo filename = do
  -- \| Step 1: Setting up the environment
  workingPath <- getCurrentDirectory
  let moduleId       = takeWhile (not . isSpace) $ moduleNameString (s_moduleName sinfo)
      modulename     = last $ split '.' moduleId
      examplesFolder = getSrcFolder moduleId filename workingPath

  -- \| Step 2: Get information from LH:
  let pb          = getBindsAndSpecs moduleId sinfo
      importNames = getModIdsAndImports (pb_src pb)

  -- \| Step 3: Get the Calculus source and the imported files
  -- This translates from Liquid Haskell and GHC data structures to Calculus data structures,
  -- furthermore transSig removes LH internal refinements from data constructors (like no-junk and no-confusion refinements)
  -- and parseSourceContent gives arguments a unique name in specs

  -- \| Translate the LH type constructors to Calculus declarations
  let dataDecls = parsePData moduleId (pb_decls pb)
      -- \| Translate the LH specs of function/theorem definitions to Calculus types
      specMap   = SLH.transSig moduleId Nothing <$> M.fromList (pb_specs pb)
      -- \| Translate the GHC binds of function/theorem definitions to Calculus expressions
      lhDefs    = CLH.transBind moduleId (s_infTypes sinfo) . simplify <$> filter (not . isIgnoredBind) (pb_binds pb)
      -- \| Combine the translated LH specs and GHC binds for function/theorem definitions into Calculus declarations
      defDecls  = combineDefsAndLemmas $ pairLHDefsWithSigs moduleId lhDefs specMap (pb_vars pb)

  -- \| Figure out the import declarations for the imported lhExample modules and their files
  importedSourceFiles <- getImportFiles examplesFolder importNames

  -- \| Step 4: Do the translation to Coq
  putStrLn $ "Input file: " ++ filename

  -- Thanks to sinfo, this will also produce declarations from this rather than from the imported modules
  traverse_ (translateFile False sinfo) importedSourceFiles

  let calcSource :: [Calc.Decl]
      calcSource = topologicalSort (dataDecls ++ defDecls)

      outputFolder = getOutputFolder moduleId filename workingPath

  unless (null importNames) $ putStrLn ("Imported external files: " ++ intercalate ", " importedSourceFiles)

  when writeFlag $ do
    createDirectoryIfMissing True outputFolder
    writeOut outputFolder modulename ILHC [] calcSource
  putStrLn ""

  pure (calcSource, (importNames, outputFolder, modulename))

-- | Calls translation function on source file and (optionally) writes (intermediate) output files in output folder
translateFile ::
  -- | Whether output files for Calculus and Coq should be generated
  Bool ->
  -- | All information about the Liquid Haskell file to translate
  SrcInfo ->
  -- | Complete file name
  String ->
  IO [Coq.Decl]
translateFile writeFlag sinfo arg = do
  (calcSource, (importNames, outputFolder, modulename)) <- parseFile writeFlag sinfo arg

  let hasImports = not $ null importNames

  -- Translate Calculus declarations to Coq declarations
  let coqImports = map Coq.Load importNames
      coqResult  = coqImports ++ concatMap trDecl calcSource

  -- | Step 5: Write output files
  when writeFlag $ do
    let coqPreamble = if hasImports then [] else preamble
    writeOut outputFolder modulename Coq coqPreamble coqResult
  putStrLn ""

  pure coqResult

writeOut :: (Show a) => FilePath -> String -> OUT -> [String] -> [a] -> IO ()
writeOut outputFolder modulename outType pre ilhSource = do
  let ilhOutputPath = outputFolder </> (modulename ++ outPostfix outType)
  putStrLn ("Writing " ++ show outType ++ " output to file at " ++ ilhOutputPath)
  let ilhOutput = intercalate "\n" (pre ++ map show ilhSource)
  writeFile ilhOutputPath ilhOutput

-- | Parsed binds and specs extracted from LH.
data ParsedBinds = ParsedBinds
  { -- | TargetSrc contained in the input
    pb_src :: Specs.TargetSrc,
    -- | Binders for reflected functions
    pb_vars :: [Var],
    -- | Refined types of (data, type) constructors
    pb_decls :: PData,
    -- | Source code (list of top-level bindings)
    pb_binds :: [CoreBind],
    -- | Specs: variables with refined types
    pb_specs :: [SpecPair]
  }
-- \^ ?? LP:What are the variables for which we get the refined types?

-- | Get the stuff that we need from LH parser, namely: Binds and Specs.
getBindsAndSpecs :: Id -> SrcInfo -> ParsedBinds
getBindsAndSpecs modId sinfo =
  let (Specs.TargetInfo src specs) = s_targetInfo sinfo
      refls = Specs.gsReflects $ Specs.gsRefl specs
   in ParsedBinds
        { pb_src   = src
        , pb_vars  = refls
        , pb_decls = getDataDecls (Specs.gsData specs, Specs.gsName specs)
        , pb_binds = Specs.giCbs src
        , pb_specs = getSpecPairs specs
        }
  where
    getSpecPairs :: Specs.TargetSpec -> [SpecPair]
    getSpecPairs = map (bimap (stripLegalName modId . show) F.val) . Specs.gsTySigs . Specs.gsSig

    getDataDecls :: (Specs.GhcSpecData, Specs.GhcSpecNames) -> PData
    getDataDecls (spdata, spnames) =
      -- NV TODO: filter out the data constructors and type constructors that are not defined in
      -- the currect module.
      PData (Specs.gsCtors spdata) (Specs.gsTconsP spnames) -- , Specs.gsDconsP spnames, Specs.gsADTs spnames)

-- | Returns the absolute path of the root directory of the files to translate as a list of path components
getSrcPath :: String -> String -> String -> [String]
getSrcPath moduleId filename workingPath = removeSuffix modulePrefixes folderPath
  where
    modulePrefixes = init $ split '.' moduleId
    folderPath = splitDirectories $ takeDirectory (workingPath </> filename)

-- | Return the absolute path of the root directory of the files to translate
getSrcFolder :: String -> String -> String -> FilePath
getSrcFolder moduleId filename workingPath = joinPath (getSrcPath moduleId filename workingPath)

-- | Returns the output directory for generated files
getOutputFolder :: String -> String -> String -> FilePath
getOutputFolder moduleId filename workingPath =
    implementationFolder </> "lava" </> "out" </> subfolder
  where
    modulePrefixes = init $ split '.' moduleId
    exampleFolderPath = getSrcPath moduleId filename workingPath
    implementationFolder = joinPath . init . init $ exampleFolderPath
    subfolder = joinPath modulePrefixes

-- TODO: gsAllImps does not exist anymore (since commit 99f6d787b15e63bbc4b939a950d8babce97469cd)
-- maybe use allImports instead of Specs.gsAllImps (see Plugin.hs)
getModIdsAndImports :: Specs.TargetSrc -> [String]
-- getModIdsAndImports src = map symbolString . H.toList $ Specs.gsAllImps src
-- getModIdsAndImports src = error $ "TODO: imports"
getModIdsAndImports _ = []

pairLHDefsWithSigs :: Id -> [Def] -> M.Map Id Calc.RefType -> [Var] -> [(Def, Maybe Calc.RefType, Bool)]
pairLHDefsWithSigs modId defs specMap reflectedDecls = map single defs
  where
    reflectedNames :: S.Set Id
    reflectedNames = S.fromList $ map (stripLegalName modId . show . varName) reflectedDecls
    single :: Def -> (Def, Maybe Calc.RefType, Bool)
    single def = (def, M.lookup (defName def) specMap, defName def `S.member` reflectedNames)
