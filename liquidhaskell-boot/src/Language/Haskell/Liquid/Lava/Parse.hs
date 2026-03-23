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

import qualified Lava.Calculus as Calc
import           Lava.LH
import           Lava.Misc
import           Lava.Util

import qualified Language.Haskell.Liquid.Lava.SpecToLH as SLH


-- ** LH -> Calculus parsing

type SpecPair = (Id, LhLib.SpecType)

-- | Parsed data declarations extracted from Liquid Haskell
data PData = PData
  { pdCtors  :: [(Var, F.Located LhLib.SpecType)]  -- ^ refined types of data constructors
  , pdTyCons :: [LhLib.TyConP]                     -- ^ refined types of type constructors
  }

-- , [LhLib.Located DataCon], [F.DataDecl]) -- more data type info, in case they are needed
parseToSpecPair :: Id -> (Var, F.Located LhLib.SpecType) -> SpecPair
parseToSpecPair modId (v, F.Loc _ _ spec) = (stripLegalName modId $ show (varName v), spec)

-- | Parse refined type constructors into Calculus declarations
parsePData :: Id -> PData -> [Calc.Decl]
parsePData modId (PData cs typConstrs) =
  {- trace ("parsePData " ++ modId ++ "\n("++show constrs++", "++show typConstrs++")") $ -}
  map mkData (filter (not . isBuiltinDatatype) typeNames)
  where
    -- translate each branch
    constrs :: [(Id, Calc.RefType)]
    constrs = map (parseSpec . parseToSpecPair modId) cs
    parseSpec (c, sig) =
      let sigT = SLH.transSig modId (Just c) sig
          (args', ret) = signatureToArgsRet sigT
          args_ = map SLH.defaultBind args'
          args = mkDistinct args_    -- TODO comes from Lava.Util
       in (c, foldr (\(n, t) acc -> Calc.ArrType n t acc) ret args)
    -- we translate every type constructor that is not already built-in
    typeNames = map (\(LhLib.TyConP _ con _ _ _ _ _) -> SLH.showppStripped modId con) typConstrs
    -- find the translated branches corresponding to typeName
    getConstrs :: Id -> [(Id, Calc.RefType)]
    getConstrs typeName = filter (isConstrOf typeName . Calc.argTp . snd . Calc.arrs . snd) constrs
    isConstrOf typeName (Calc.TC n) = n == typeName
    isConstrOf _ (Calc.Builtin _) = False
    -- Assemble typeName and the corresponding translated branches
    mkData typeName = Calc.Data typeName (sortOn fst (getConstrs typeName))

-- ** translating the intermediate data structures to 'Calc.Decl's

-- | combine the defs and lemmas into a list of 'Calc.Decl' and sort them in dependency order
combineDefsAndLemmas :: [(Def, Maybe Calc.RefType, Bool)] -> [Calc.Decl]
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

isLemma :: Calc.RefType -> Bool
isLemma = (== "()") . typeName . Calc.argTp . snd . Calc.arrs
  where
    typeName :: Calc.BaseType -> String
    typeName (Calc.Builtin c) = show c
    typeName (Calc.TC n) = n

parseDef :: (Def, Maybe Calc.RefType, Bool) -> Calc.Decl
parseDef (Def dname args body _, Just sig, b) =
  Calc.Definition dname fullTp (Calc.substs renSubs body) b
  where
    fullTp = foldr (\(n, t) acc -> Calc.ArrType n t acc) tp (map SLH.defaultBind sigArgs)
    tp =
      if isLemma sig
        then case sRes of
          Calc.RefType _ _ reft -> Calc.RefType (dname ++ "_claim") Calc.unitTp reft
          _ -> error $ "Lemma " ++ dname ++ " has unexpected arrow return type"
        else sRes
    (sigArgs, sRes) = signatureToArgsRet sig
    renSubs = zipWith (\n arg -> (Calc.mkVar (refName arg), n)) args sigArgs
    refName (Calc.RefType x _ _) = x
    refName (Calc.ArrType x _ _) = x
parseDef (Def dname _ _ _, Nothing, _) = error $ "Top-level definition or lemma " ++ dname ++ " without signature is forbidden."

-- | replace the names of variables v in refinement types {v:A|p} of arguments x by x
signatureToArgsRet :: Calc.RefType -> ([Calc.RefType], Calc.RefType)
signatureToArgsRet sig = (args, ret)
  where
    (sigArgs, sRes) = Calc.arrs sig
    names = map fst sigArgs
    v0 = Calc.argName sRes
    v = mkFresh v0 names
    ret = Calc.subst (Calc.mkVar v) v0 . Calc.subst (Calc.mkVar v) (Calc.argName sRes) $ sRes
    args = map renameArg sigArgs
    renameArg (n, Calc.RefType x tp reft) = Calc.RefType m tp (Calc.subst (Calc.mkVar m) x reft)
      where
        m = if n /= "" then n else x
    renameArg (_, arr@Calc.ArrType{}) = arr
