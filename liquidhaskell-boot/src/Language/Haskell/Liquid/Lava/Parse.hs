{-# OPTIONS_GHC -Wall #-}
module Language.Haskell.Liquid.Lava.Parse
  ( -- ** type aliases for intermediate data
    SpecPair,
    PData (..),

    -- ** "parsers" for the specification data extracted from LH
    parseToSpecPair,
    parsePData,

    -- ** combine "parsed" LH specification data with GHC
    getImportFiles,
    combineDefsAndLemmas,

    -- ** utility function
    signatureToArgsRet,
  )
where

import           Control.Monad (filterM)
import           Data.List (sortOn)
import           System.Directory (doesFileExist)
import           System.FilePath ((</>), (<.>), joinPath)

-- import GHC.Core.DataCon
import           GHC.Types.Var (Var, varName)
import qualified Language.Fixpoint.Types as F (Located (..))
import qualified Language.Haskell.Liquid.Types.RType as LhLib

import           Lava.InternalLH (ArrType (..), LHDecl (..), LHSimpleTerm (..), LHType (Buildin, Pi, TDat), RefType (..), unitTp)
import           Lava.LH
import           Lava.Misc
import           Lava.Util

import qualified Language.Haskell.Liquid.Lava.SpecToLH as SLH


-- ** LH -> ILH parsing

type SpecPair = (Id, LhLib.SpecType)

-- | Parsed data declarations extracted from Liquid Haskell
data PData = PData
  { pdCtors  :: [(Var, F.Located LhLib.SpecType)]  -- ^ refined types of data constructors
  , pdTyCons :: [LhLib.TyConP]                     -- ^ refined types of type constructors
  }

-- , [LhLib.Located DataCon], [F.DataDecl]) -- more data type info, in case they are needed
parseToSpecPair :: Id -> (Var, F.Located LhLib.SpecType) -> SpecPair
parseToSpecPair modId (v, F.Loc _ _ spec) = (stripLegalName modId $ show (varName v), spec)

-- | Parse refined type constructors into LH type constructors
parsePData :: Id -> PData -> [LHDecl]
parsePData modId (PData cs typConstrs) =
  {- trace ("parsePData " ++ modId ++ "\n("++show constrs++", "++show typConstrs++")") $ -}
  map mkData (filter (not . isBuiltinDatatype) typeNames)
  where
    -- translate each branch
    constrs :: [(Id, ArrType)]
    constrs = map (parseSpec . parseToSpecPair modId) cs
    parseSpec (c, sig) =
      let sigT = SLH.transSig modId (Just c) sig
          (args', ret) = signatureToArgsRet sigT
          args_ = map SLH.defaultBind args'
          args = mkDistinct args_    -- TODO comes from Lava.Util
       in (c, ArrType args ret)
    -- we translate every type constructor that is not already built-in
    typeNames = map (\(LhLib.TyConP _ con _ _ _ _ _) -> SLH.showppStripped modId con) typConstrs
    -- find the translated branches corresponding to typeName
    getConstrs :: Id -> [(Id, ArrType)]
    getConstrs typeName = filter (isConstrOf typeName . argTp . retTp . snd) constrs
    isConstrOf typeName (TDat n) = n == typeName
    isConstrOf _ (Buildin _) = False
    isConstrOf _ (Pi _ _) = False
    -- Assemble typeName and the corresponding translated branches
    mkData typeName = Data typeName (sortOn fst (getConstrs typeName))

-- ** translating the intermediate data structures (using ILH object-level data structures) to 'LHDecl's

-- | combine the defs and lemmas into a list of 'LHDecl' and sort them in dependency order
combineDefsAndLemmas :: [(Def, Maybe ArrType, Bool)] -> [LHDecl]
combineDefsAndLemmas = map parseDef

-- | compute the file path of the module with given name
getImportFile :: FilePath -> String -> FilePath
getImportFile examplesFolder moduleName = examplesFolder </> joinPath (split '.' moduleName) <.> "hs"

-- | filter out only those imported module names that correspond to files in the lhExamples folder
filterImports :: String -> [String] -> IO [String]
filterImports examplesFolder =
  filterM (doesFileExist . getImportFile examplesFolder)

-- | Get the imported filenames and the import declarations for the specified module names
getImportFiles :: String -> [String] -> IO [String]
getImportFiles examplesFolder potentialImports =
  map (getImportFile examplesFolder) <$> filterImports examplesFolder potentialImports

isLemma :: ArrType -> Bool
isLemma = (== "()") . typeName . argTp . retTp
  where
    typeName :: LHType -> String
    typeName (Buildin c) = show c
    typeName (TDat n) = n
    typeName piTp@Pi {} = show piTp

parseDef :: (Def, Maybe ArrType, Bool) -> LHDecl
parseDef (Def dname args body _, Just sig, b) =
  Definition dname (ArrType (map SLH.defaultBind sigArgs) tp) (runRename body) b
  where
    tp =
      if isLemma sig
        then RefType (dname ++ "_claim") unitTp reft
        else sRes
    (sigArgs, sRes@(RefType _ _ reft)) = signatureToArgsRet sig
    substs = zipWith (\n (RefType argId _ _) -> (n, Var argId)) args sigArgs
    runRename = subst substs
parseDef (Def dname _ _ _, Nothing, _) = error $ "Top-level definition or lemma " ++ dname ++ " without signature is forbidden."

-- | replace the names of variables v in refinement types {v:A|p} of arguments x by x
signatureToArgsRet :: ArrType -> ([RefType], RefType)
signatureToArgsRet (ArrType sigArgs sRes) = (args, ret)
  where
    names = map fst sigArgs
    v0 = argName sRes
    v = mkFresh v0 names
    ret = sub v0 (Var v) . sub (argName sRes) (Var v) $ sRes
    args = map renameArg sigArgs
    renameArg (n, RefType x tp reft) = RefType m tp (sub x (Var m) reft)
      where
        m = if n /= "" then n else x
