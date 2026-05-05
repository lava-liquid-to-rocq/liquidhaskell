{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

-- | System F type checking and elaboration for refinements
module Lava.SystemF where

import Data.Bifunctor (second)
import Data.Maybe (fromJust)
import Lava.Calculus
import Lava.Names
import Lava.TypingEnvironment
import Text.PrettyPrint.HughesPJClass
import Prelude hiding ((<>))

-- * Version of System F, used for typing type refinements

-- Grammar
--
-- T ::= α | B | TC T* | T -> T | ∀α, T
data SimpleType = SmpTyVar Id | SmpBuiltin Builtin | SmpTC Id [SimpleType] | SmpArrow SimpleType SimpleType | SmpFAType Id SimpleType
  deriving (Eq)

-- TODO: see if we can make type substitutions generic

substSmpTp :: SimpleType -> Id -> SimpleType -> SimpleType
substSmpTp tp' α tp = case tp of
  SmpTyVar β | α == β -> tp'
  SmpTC tc tps -> SmpTC tc (map (substSmpTp tp' α) tps)
  SmpArrow tp1 tp2 -> SmpArrow (substSmpTp tp' α tp1) (substSmpTp tp' α tp2)
  SmpFAType β tp'' | β /= α -> SmpFAType β (substSmpTp tp' α tp'')
  (SmpTyVar {}; SmpBuiltin {}; SmpFAType {}) -> tp

instance Pretty SimpleType where
  pPrint (SmpTyVar α) = text α
  pPrint (SmpBuiltin b) = pPrint b
  pPrint (SmpTC tc tps) = hsep $ text tc : map (parens . pPrint) tps
  pPrint (SmpArrow tp1 tp2) = pPrint tp1 <+> "->" <+> pPrint tp2
  pPrint (SmpFAType α tp) = "∀" <> text α <> "." <+> pPrint tp

-- | Extracts the elements out of an SmpArrow and raises an error for another type
fromSmpArrow :: SimpleType -> (SimpleType, SimpleType)
fromSmpArrow (SmpArrow tp1 tp2) = (tp1, tp2)
fromSmpArrow _ = error "SmpArrow expected"

-- | Projects a refinement type into a simple type
refTptoSmpTp :: RefType -> SimpleType
refTptoSmpTp (RefType _ (TC tc tps) _) = SmpTC tc (map refTptoSmpTp tps)
refTptoSmpTp (RefType _ (Builtin b) _) = SmpBuiltin b
refTptoSmpTp (RefType _ (TyVar α) _) = SmpTyVar α
refTptoSmpTp (ArrType _ tpx tp) = SmpArrow (refTptoSmpTp tpx) (refTptoSmpTp tp)
refTptoSmpTp (FAType α tp) = SmpFAType α (refTptoSmpTp tp)

-- | Type checking and elaboration in System F
smpTpCheck :: TypEnv -> Reft -> Either TypeError (SimpleType, Reft)
smpTpCheck γ (Var x _ locx) = do
  (locγ, tp) <- lookupVar x γ
  let res loc = return (refTptoSmpTp tp, Var x (arity tp) loc)
  case locx of
    Recursive {} -> res locx
    _ -> case locγ of
      Recursive {} -> Left . SynErr $ "Impossible to build induction for an occurence of the function" <+> text x
      _ -> res locγ
smpTpCheck _ r@(StringLit _) = return (SmpBuiltin String, r)
smpTpCheck _ r@(IntLit _) = return (SmpBuiltin Integer, r)
smpTpCheck _ r@(FloatLit _) = return (SmpBuiltin Double, r)
smpTpCheck γ r@(DC c) = do
  tpc <- lookupDC c γ
  return (refTptoSmpTp tpc, r)
smpTpCheck γ (App r1 r2) = do
  (tp1, r1') <- smpTpCheck γ r1
  (tp2, r2') <- smpTpCheck γ r2
  case tp1 of
    SmpArrow tpx tp | tpx == tp2 -> return (tp, App r1' r2')
    _ ->
      Left . SmpTpErr $
        "Too many arguments given in the application"
          <+> pPrint (App r1' r2')
          <+> colon
          $$ pPrint r1'
          <+> "has type"
          <+> pPrint r1'
smpTpCheck γ (TyApp r tp) = do
  (tpr, r') <- smpTpCheck γ r
  case tpr of
    -- TODO: do we check wf of tp? Do we elaborate to the unrefined type?
    SmpFAType α tpr' -> return (substSmpTp (refTptoSmpTp tp) α tpr', TyApp r' tp)
    _ ->
      Left . SmpTpErr $
        "Too many arguments given in the type application"
          <+> pPrint (TyApp r tp)
          <+> colon
          $$ pPrint r
          <+> "has type"
          <+> pPrint tpr
smpTpCheck γ (Neg r) = do
  (tp, r') <- smpTpCheck γ r
  if tp == SmpTC boolTpName []
    then return (tp, Neg r')
    else Left . SmpTpErr $ "Term" <+> pPrint r <+> "should be boolean"
smpTpCheck γ r@(Bop bop r1 r2) | bop == Eq || bop == Neq = do
  (tp1, r1') <- smpTpCheck γ r1
  (tp2, r2') <- smpTpCheck γ r2
  if tp1 == tp2
    then return (SmpTC boolTpName [], Bop bop r1' r2')
    else
      Left . SmpTpErr $
        "Different types on both sides of (in)equality" <+> pPrint r <> ": found" <+> pPrint tp1 <+> "and" <+> pPrint tp2
smpTpCheck γ r@(Bop bop r1 r2) = do
  let (tp1, (tp2, tp)) = second fromSmpArrow . fromSmpArrow $ refTptoSmpTp (fromJust $ lookup bop bopTypes)
  (tp1', r1') <- smpTpCheck γ r1
  (tp2', r2') <- smpTpCheck γ r2
  if tp1' == tp1 && tp2' == tp2
    then return (tp, Bop bop r1' r2')
    else Left . SmpTpErr $ "Wrong types for the arguments of the operator" <+> pPrint r
smpTpCheck γ (Proj r) = second Proj <$> smpTpCheck γ r
smpTpCheck _ r@(Sub {}; Inj {}; QMark {}; Pop {}) =
  error . render $ "Unexpected term" <+> pPrint r <+> "found in type refinement"
