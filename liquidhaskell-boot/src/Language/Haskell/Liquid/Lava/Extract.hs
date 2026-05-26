{-# LANGUAGE OrPatterns #-}
{-# OPTIONS_GHC -Wall #-}

-- | Pulls Calculus declarations out of LiquidHaskell's TargetInfo + GHC core
--   binds. Output of this module is the boundary between liquidhaskell-boot
--   and downstream tools (e.g. lava) that consume Calculus declarations.
module Language.Haskell.Liquid.Lava.Extract
  ( SrcInfo (..)
  , CalcMeta (..)
  , extractCalculus
  , writeIlh
  , writeOut
  , calcMetaFor
  , ilhPath
  , writeIlhBin
  , readIlhBin
  , ilhBinPath
  ) where

import Control.Monad (unless)
import qualified Data.Binary as Bin
import Data.Bifunctor (bimap)
import Data.Char (isSpace)
import Data.List (intercalate, isPrefixOf)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import System.Directory (createDirectoryIfMissing, getCurrentDirectory)
import System.FilePath (joinPath, splitDirectories, takeDirectory, (</>))
import qualified Text.PrettyPrint.HughesPJClass as PP

import GHC.Core
import GHC.Plugins hiding (Id, split)
import qualified Language.Fixpoint.Types as F (Located, val)
import           Language.Haskell.Liquid.Types.RType (SpecType, TyConP (..))
import qualified Language.Haskell.Liquid.Types.Specs as Specs
import           Language.Haskell.Liquid.Types.Types (AnnInfo (..))
import           Language.Haskell.Liquid.Lava.Misc (isIgnoredBind, removeSuffix, split, stripLegalName)
import           Language.Haskell.Liquid.Lava.Names (Id, OUT (..), outPostfix)
import qualified Language.Haskell.Liquid.Lava.Calculus as Calc
import qualified Language.Haskell.Liquid.Lava.CoreToLH as CLH
import           Language.Haskell.Liquid.Lava.Parse
import           Language.Haskell.Liquid.Lava.Simplify (simplify)
import qualified Language.Haskell.Liquid.Lava.SpecToLH as SLH

-- | Contains all information about the source Liquid Haskell file to translate
data SrcInfo = SrcInfo
  { s_moduleName :: ModuleName
  , s_summary    :: ModSummary
  , s_targetInfo :: Specs.TargetInfo
  , s_infTypes   :: AnnInfo SpecType
  , s_imports    :: [Module]
  }

-- | Metadata about the extracted Calculus that downstream tools need to drive
--   their output. Independent of LH/GHC types so it can be re-derived on the
--   consumer side (e.g. when reading an .ilh file from disk).
data CalcMeta = CalcMeta
  { cmOutputFolder :: FilePath
  , cmModuleName   :: String
  , cmHasImports   :: Bool
  }

-- | Extract the Calculus declarations for a module.
extractCalculus :: SrcInfo -> IO ([Calc.Decl], CalcMeta)
extractCalculus sinfo = do
    workingPath <- getCurrentDirectory
    let moduleId = takeWhile (not . isSpace) $ moduleNameString (s_moduleName sinfo)
        modulename = last $ split '.' moduleId
        examplesFolder = getSrcFolder moduleId filename workingPath
        outputFolder = getOutputFolder moduleId filename workingPath
        pb = getBindsAndSpecs moduleId sinfo
        importNames = getModIdsAndImports sinfo
        localDecls = filterLocalPData (s_moduleName sinfo) (pb_decls pb)
        dataDecls = parsePData moduleId localDecls
        specMap = SLH.transSig moduleId Nothing <$> M.fromList (pb_specs pb)
        lhDefs = CLH.transBind moduleId (s_infTypes sinfo) . simplify <$> filter (not . isIgnoredBind) (pb_binds pb)
        defDecls = combineDefsAndLemmas $ pairLHDefsWithSigs moduleId lhDefs specMap (pb_vars pb)
        specSig = Specs.gsSig . Specs.giSpec $ s_targetInfo sinfo
        rawSpecs = Specs.gsTySigs specSig
        asmSpecs = Specs.gsAsmSigs specSig
        refSpecs = Specs.gsRefSigs specSig
        allSpecs = rawSpecs ++ asmSpecs ++ refSpecs
        importDecls = map (mkImportDecl moduleId (pb_decls pb) allSpecs) importNames
        -- Note: declarations are emitted in source order. The consumer
        -- (lava driver) topologically sorts before elaboration.
        calcSource = importDecls ++ dataDecls ++ defDecls
        meta = CalcMeta outputFolder modulename (not (null importNames))
    importedSourceFiles <- getImportFiles examplesFolder importNames
    putStrLn $ "Input file: " ++ filename
    unless (null importNames) $
      putStrLn ("Imported external files: " ++ intercalate ", " importedSourceFiles)
    pure (calcSource, meta)
  where
    filename = Specs.giTarget $ Specs.giSrc $ s_targetInfo sinfo

-- | Write the un-elaborated Calculus declarations to .ilh_no_elab file.
writeIlh :: CalcMeta -> [Calc.Decl] -> IO ()
writeIlh meta calcSource = do
    createDirectoryIfMissing True (cmOutputFolder meta)
    writeOut (cmOutputFolder meta) (cmModuleName meta) ILHNoElab PP.empty calcSource

-- | Reconstruct the 'CalcMeta' that @writeIlh@ used, given just the module
--   name and the source file path. Used by downstream tools that want to
--   locate the .ilh file without re-running extraction.
--
--   Note: 'cmHasImports' is set to 'False' here. Consumers that need the
--   correct value should derive it from the parsed .ilh contents.
calcMetaFor :: ModuleName -> FilePath -> IO CalcMeta
calcMetaFor modName filename = do
    workingPath <- getCurrentDirectory
    let moduleId = moduleNameString modName
        modulename = last (split '.' moduleId)
        outputFolder = getOutputFolder moduleId filename workingPath
    pure (CalcMeta outputFolder modulename False)

-- | Path that 'writeIlh' wrote to.
ilhPath :: CalcMeta -> FilePath
ilhPath meta = cmOutputFolder meta </> (cmModuleName meta ++ outPostfix ILHNoElab)

-- | Binary-serialized companion to the .ilh file.
ilhBinPath :: CalcMeta -> FilePath
ilhBinPath meta = ilhPath meta ++ ".bin"

writeIlhBin :: CalcMeta -> [Calc.Decl] -> IO ()
writeIlhBin meta calcSource = do
    createDirectoryIfMissing True (cmOutputFolder meta)
    let path = ilhBinPath meta
    putStrLn ("Writing serialized Calculus to " ++ path)
    Bin.encodeFile path calcSource

readIlhBin :: FilePath -> IO [Calc.Decl]
readIlhBin = Bin.decodeFile

-- | Pretty-print a list of declarations to a file. Used by both extract (.ilh)
--   and the lava driver (.ilh after elaboration, .v Coq output).
writeOut :: (PP.Pretty a) => FilePath -> String -> OUT -> PP.Doc -> [a] -> IO ()
writeOut outputFolder modulename outType pre decls = do
    let outputPath = outputFolder </> (modulename ++ outPostfix outType)
    putStrLn ("Writing " ++ show outType ++ " output to file at " ++ outputPath)
    let body = PP.vcat (pre PP.<> PP.char '\n' : map ((PP.<> PP.char '\n') . PP.pPrint) decls)
        style = PP.Style {PP.mode = PP.PageMode, PP.lineLength = 120, PP.ribbonsPerLine = 1.2}
    writeFile outputPath (PP.renderStyle style body)
    putStrLn ""

-- | Parsed binds and specs extracted from LH.
data ParsedBinds = ParsedBinds
  { pb_src   :: Specs.TargetSrc
  , pb_vars  :: [Var]
  , pb_decls :: PData
  , pb_binds :: [CoreBind]
  , pb_specs :: [SpecPair]
  }

getBindsAndSpecs :: Id -> SrcInfo -> ParsedBinds
getBindsAndSpecs modId sinfo = ParsedBinds
        { pb_src = src
        , pb_vars = refls
        , pb_decls = getDataDecls (Specs.gsData specs, Specs.gsName specs)
        , pb_binds = Specs.giCbs src
        , pb_specs = getSpecPairs specs
        }
  where
    Specs.TargetInfo src specs = s_targetInfo sinfo
    refls = Specs.gsReflects $ Specs.gsRefl specs
    getSpecPairs = map (bimap (stripLegalName modId . show) F.val) . Specs.gsTySigs . Specs.gsSig
    getDataDecls (spdata, spnames) = PData (Specs.gsCtors spdata) (Specs.gsTconsP spnames)

getSrcPath :: String -> String -> String -> [String]
getSrcPath moduleId filename workingPath = removeSuffix modulePrefixes folderPath where
    modulePrefixes = init $ split '.' moduleId
    folderPath = splitDirectories $ takeDirectory (workingPath </> filename)

getSrcFolder :: String -> String -> String -> FilePath
getSrcFolder moduleId filename workingPath = joinPath (getSrcPath moduleId filename workingPath)

getOutputFolder :: String -> String -> String -> FilePath
getOutputFolder moduleId filename workingPath =
    implementationFolder </> "lava" </> "out" </> subfolder
  where
    modulePrefixes = init $ split '.' moduleId
    exampleFolderPath = getSrcPath moduleId filename workingPath
    implementationFolder = joinPath . init . init $ exampleFolderPath
    subfolder = joinPath modulePrefixes

getModIdsAndImports :: SrcInfo -> [String]
getModIdsAndImports sinfo = map modNameString $ filter (not . isStdLibModule) (s_imports sinfo)
  where
    modNameString = moduleNameString . moduleName
    isStdLibModule m = any (`isPrefixOf` modNameString m) stdLibPrefixes
    stdLibPrefixes = ["GHC.", "Data.", "Control.", "System.", "Prelude", "Foreign.", "Text.", "Numeric.", "Language."]

filterLocalPData :: ModuleName -> PData -> PData
filterLocalPData modName pd = pd {pdTyCons = filteredTyCons, pdCtors = filteredCtors}
  where
    filteredTyCons = filter isLocalTC (pdTyCons pd)
    filteredCtors = filter (isLocalCtor . fst) (pdCtors pd)
    isLocalTC tcp = maybe True ((== modName) . moduleName) $ nameModule_maybe (tyConName (tcpCon tcp))
    isLocalCtor v = maybe True ((== modName) . moduleName) $ nameModule_maybe (varName v)

filterPDataForModule :: String -> PData -> PData
filterPDataForModule modStr pd = pd {pdTyCons = filter isFromMod (pdTyCons pd), pdCtors = filter (isFromMod' . fst) (pdCtors pd)}
  where
    isFromMod tcp = maybe False ((== modStr) . moduleNameString . moduleName) $ nameModule_maybe (tyConName (tcpCon tcp))
    isFromMod' v = maybe False ((== modStr) . moduleNameString . moduleName) $ nameModule_maybe (varName v)

mkImportDecl :: Id -> PData -> [(Var, F.Located SpecType)] -> String -> Calc.Decl
mkImportDecl moduleId allPData rawSpecs modName = Calc.Import modName (dataDs ++ defDs)
  where
    dataDs = parsePData moduleId (filterPDataForModule modName allPData)
    defDs = map mkDefStub $ filter (isFromModule modName . fst) rawSpecs
    mkDefStub (v, locSpec) =
      Calc.Definition
        (stripLegalName moduleId (show (varName v)))
        (SLH.transSig moduleId Nothing (F.val locSpec))
        (Calc.Reft (Calc.Var "imported" Nothing Calc.Global))
        False
    isFromModule modStr v = maybe False ((== modStr) . moduleNameString . moduleName) $ nameModule_maybe (varName v)

pairLHDefsWithSigs :: Id -> [CLH.Def] -> M.Map Id Calc.RefType -> [Var] -> [(CLH.Def, Maybe Calc.RefType, Bool)]
pairLHDefsWithSigs modId defs specMap reflectedDecls = map single defs
  where
    reflectedNames :: S.Set Id
    reflectedNames = S.fromList $ map (stripLegalName modId . show . varName) reflectedDecls
    single def = (def, M.lookup (CLH.defName def) specMap, CLH.defName def `S.member` reflectedNames)
