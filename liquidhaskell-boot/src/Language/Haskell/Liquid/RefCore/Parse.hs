{-# LANGUAGE OrPatterns #-}
{-# OPTIONS_GHC -Wall #-}

module Language.Haskell.Liquid.RefCore.Parse
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

import Control.Monad (filterM)
import Data.Bifunctor (first)
import Data.List (sortOn)
import Data.Set (fromList)
import Data.Tuple.Extra (snd3, thd3)
import GHC.Types.Var (Var, varName)
import GHC.Types.Name (getOccString)
import qualified Language.Fixpoint.Types as F (Located (..))
import qualified Language.Haskell.Liquid.RefCore.Calculus as Calc
import Language.Haskell.Liquid.RefCore.CoreToLH (Def (..))
import Language.Haskell.Liquid.RefCore.Misc
import Language.Haskell.Liquid.RefCore.Names (Id, freshVar)
import qualified Language.Haskell.Liquid.RefCore.SpecToLH as SLH
import qualified Language.Haskell.Liquid.Types.RType as LhLib
import System.Directory (doesFileExist)
import System.FilePath (joinPath, (<.>), (</>))

-- ** LH -> Calculus parsing

type SpecPair = (Id, LhLib.SpecType)

-- | Parsed data declarations extracted from Liquid Haskell
data PData = PData
  { -- | refined types of data constructors
    pdCtors :: [(Var, F.Located LhLib.SpecType)],
    -- | refined types of type constructors
    pdTyCons :: [LhLib.TyConP]
  }

-- , [LhLib.Located DataCon], [F.DataDecl]) -- more data type info, in case they are needed
parseToSpecPair :: Id -> (Var, F.Located LhLib.SpecType) -> SpecPair
parseToSpecPair modId (v, F.Loc _ _ spec) = (stripLegalName modId $ show (varName v), spec)

-- | Parse refined type constructors into Calculus declarations
parsePData :: Id -> PData -> [Calc.Decl]
parsePData modId (PData cs typConstrs) =
  {- trace ("parsePData " ++ modId ++ "\n("++show constrs++", "++show typConstrs++")") $ -}
  map mkData (filter (not . isBuiltinDatatype . fst) typeNames)
  where
    -- translate each branch
    constrs :: [(Id, Calc.RefType)]
    constrs = map (parseSpec . parseToSpecPair modId) cs
    parseSpec (c, sig) =
      let sigT = SLH.transSig modId (Just c) sig
          (αs, args', ret) = signatureToArgsRet sigT
          args_ = map defaultBind args'
          args = mkDistinct args_
       in (c, Calc.mkArrows (αs, args, ret))
    mkDistinct [] = []
    mkDistinct ((x, xData) : tl) = (x, xData) : mkDistinct (map (first (\y -> if y == x then y ++ "_" else y)) tl)
    -- we translate every type constructor that is not already built-in
    typeNames =
      map
         (\(LhLib.TyConP _ con αs _ _ _ _) -> (SLH.showppStripped modId con, map (\(LhLib.RTV α) -> getOccString α) αs))
        typConstrs
    -- find the translated branches corresponding to typeName
    getConstrs :: Id -> [(Id, Calc.RefType)]
    getConstrs typeName = filter (isConstrOf typeName . snd3 . thd3 . Calc.arrs . snd) constrs
    isConstrOf typeName (Calc.TC n _) = n == typeName
    isConstrOf _ (Calc.Builtin _; Calc.TyVar _) = False
    -- Assemble typeName and the corresponding translated branches
    mkData (typeName, vars) = Calc.Data typeName vars (sortOn fst (getConstrs typeName))

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
isLemma = (== "()") . typeName . snd3 . thd3 . Calc.arrs
  where
    typeName :: Calc.BaseType -> String
    typeName (Calc.Builtin c) = show c
    typeName (Calc.TC n _) = n
    typeName (Calc.TyVar α) = α

parseDef :: (Def, Maybe Calc.RefType, Bool) -> Calc.Decl
parseDef (Def dname args body _, Just sig, b) =
  Calc.Definition dname fullTp body b
  where
    sig' = Calc.renameParams args sig
    (αs, sigArgs, sRes) = signatureToArgsRet sig'
    retTp =
      if isLemma sig'
        then case sRes of
          Calc.RefType _ _ reft -> Calc.RefType (dname ++ "_claim") Calc.unitTp reft
          _ -> error $ "Lemma " ++ dname ++ " has unexpected arrow return type"
        else sRes
    fullTp = Calc.mkArrows (αs, zip args sigArgs, retTp)
parseDef (Def dname _ _ _, Nothing, _) = error $ "Top-level definition or lemma " ++ dname ++ " without signature is forbidden."

-- | replace the names of variables v in refinement types {v:A|p} of arguments x by x
signatureToArgsRet :: Calc.RefType -> ([Id], [Calc.RefType], Calc.RefType)
signatureToArgsRet sig = (αs, args, ret)
  where
    (αs, sigArgs, (v0, sResTp, sResReft)) = Calc.arrs sig
    names = map fst sigArgs
    v = freshVar v0 (fromList names)
    ret = Calc.RefType v sResTp $ Calc.subst (Calc.mkVar v) v0 sResReft
    args = map renameArg sigArgs
    renameArg (n, Calc.RefType x tp reft) = Calc.RefType m tp (Calc.subst (Calc.mkVar m) x reft)
      where
        m = if n /= "" then n else x
    renameArg (_, arr@Calc.ArrType {}) = arr
    renameArg (_, arr@Calc.FAType {}) = arr

-- > defaultBind({x:A | r})  = (x, {x:A | r})
-- > defaultBind(x:Tx -> Y) = (x, (x: Tx -> Y))
-- > defaultBind(forall α, tp) = (α, (forall α, tp))
defaultBind :: Calc.RefType -> (Id, Calc.RefType)
defaultBind r@(Calc.RefType nm _ _) = (nm, r)
defaultBind a@(Calc.ArrType nm _ _) = (nm, a)
defaultBind fa@(Calc.FAType nm _) = (nm, fa)
