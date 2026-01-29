-- Temporary file
module Lava.PaperUtils where

import Data.Bifunctor (first)
import Data.Char (isUpper)
import Data.List (uncons)
import qualified Data.Set as Set
import Debug.Trace
import qualified Lava.Coq as Coq
import Lava.InternalLH as ILH
import Lava.Util (Id, split, traceFuncRet)

-- * Differentiate data constructors from variables (probably temporary)

unqualidName :: Id -> Id
unqualidName n = case split '_' n of
  [_, [], s] -> s
  _ -> n

-- TODO: make this more robust (variables in refinement can use uppercase)
isDC :: String -> Bool
isDC x = case uncons (unqualidName x) of
  Just (c, _) -> isUpper c && x /= "VV"
  Nothing -> False

mkVarOrCr :: Id -> Coq.CoqTerm
mkVarOrCr c | isDC c = Coq.Cr c
mkVarOrCr x = Coq.Var x

-- * Errors

data TransError
  = WfErr String
  | CheckingErr String
  | SynErr String
  | SubstErr String
  | SubtypingErr String
  | TransErr String

instance Show TransError where
  show te = case te of
    WfErr err -> aux "Well-formedness" err
    CheckingErr err -> aux "Type checking" err
    SynErr err -> aux "Type synthesis " err
    TransErr err -> aux "Translation" err
    SubtypingErr err -> aux "Subtyping" err
    SubstErr err -> aux "Substitution" err
    where
      aux kind err = "—— " ++ kind ++ " failed with error: " ++ err ++ " ——"

-- * Free variables

freeVars :: LHSimpleTerm -> Set.Set Id
freeVars (Var x) | isDC x = Set.empty
freeVars (Var x) | x `elem` [ttTmName, ffTmName, unitTmName] = Set.empty
freeVars (Var x) = Set.singleton x
freeVars (App hd args) = Set.unions $ map freeVars (hd : args)
freeVars (Bop _ r1 r2) = Set.unions $ map freeVars [r1, r2]
freeVars (Neg r) = freeVars r
freeVars (StringLit _) = Set.empty
freeVars (IntLit _) = Set.empty
freeVars (FloatLit _) = Set.empty

-- * Substitution

-- Substitution {r'/x}r of a simple term into a simple term
substSmpTerm :: LHSimpleTerm -> Id -> LHSimpleTerm -> LHSimpleTerm
substSmpTerm r' x r = case r of
  Var y | y == x -> r'
  App h args -> App (substSmpTerm r' x h) $ map (substSmpTerm r' x) args
  Bop bop r1 r2 -> Bop bop (substSmpTerm r' x r1) (substSmpTerm r' x r2)
  Neg r0 -> Neg $ substSmpTerm r' x r0
  _ -> r -- Literals and y ≠ x

-- | Substitution {r'/x}e of a simple term into a term
substSmpTmTm :: LHSimpleTerm -> Id -> LHTerm -> Either TransError LHTerm
substSmpTmTm r x e = case e of
  BasicTerm r' -> return . BasicTerm $ substSmpTerm r x r'
  Case (Var y) _ _ | y == x -> Left . SubstErr $ "Cannot substitute variable " ++ x ++ " because it is used in a match"
  Case _ _ _ -> trace "TODO: complete PaperUtils.substSmmpTmTm" undefined
  Let y _ _ | y /= x -> trace "TODO: complete PaperUtils.substSmmpTmTm" undefined
  Let _ _ _ -> trace "TODO: complete PaperUtils.substSmmpTmTm" undefined
  Lambda _ _ -> trace "TODO: complete PaperUtils.substSmmpTmTm" undefined
  Undefined -> return Undefined
  SEqn r1 r2 e' -> SEqn r1' r2' <$> substSmpTmTm r x e'
    where
      [r1', r2'] = map (substSmpTerm r x) [r1, r2]
  QMark e1 e2 -> QMark <$> substSmpTmTm r x e1 <*> substSmpTmTm r x e2
  Annot e' tp -> (`Annot` tp) <$> substSmpTmTm r x e'

-- Substitution {y:A | {r'\x}r} -- TODO: we assume y ∈ fv(r')
substInRefType :: [(LHSimpleTerm, Id)] -> RefType -> RefType
substInRefType σ (RefType y a r) = RefType y a (foldr (uncurry substSmpTerm) r σ)

applyArrType :: ArrType -> [LHSimpleTerm] -> RefType
applyArrType (ArrType args ret) rs =
  let σ = zipWith (\a (b, _) -> (a, b)) rs args
   in substInRefType σ ret

-- | Partial applications of substitutions of the refinements in an application
-- (x_i:R_i)_{i < n} -> (r_i)_{i < n} -> Maybe (σn, R_iσ_i) where σ_i = {r_j\x_j}_{j < i}
substArgs :: [(Id, RefType)] -> [LHSimpleTerm] -> Either TransError ([(LHSimpleTerm, Id)], [RefType])
substArgs = {- traceFuncRet ["substArgs", show σ, show rs] $ -} aux []
  where
    -- The first argument is the current substitution built with previous arguments
    aux :: [(LHSimpleTerm, Id)] -> [(Id, RefType)] -> [LHSimpleTerm] -> Either TransError ([(LHSimpleTerm, Id)], [RefType])
    aux σ [] [] = return (σ, [])
    aux σ ((x, tp) : tps) (r : rs) = do
      (σ', rs') <- aux ((r, x) : σ) tps rs
      return (σ', substInRefType σ tp : rs')
    aux σ tps rs = traceFuncRet ["aux (substArgs)", show σ, show tps, show rs] $ Left . SubstErr $ "Error in substitution"

unapplyPi :: RefType -> ([(Id, RefType)], RefType)
unapplyPi rt@(RefType _ tp _) = case tp of
  Buildin {} -> ([], rt)
  TDat {} -> ([], rt)
  Pi (x1, xRTp1) ret1 -> first ((x1, xRTp1) :) $ unapplyPi ret1

getArity :: RefType -> Int
getArity rt = length . fst $ unapplyPi rt
