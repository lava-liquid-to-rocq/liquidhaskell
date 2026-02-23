-- | This module contains the main functions of the translation.
-- Unrefined and refined translations are mutually dependent, so they are all in the same file
module Lava.Translation where

import Data.Bifunctor (second)
import Lava.Calculus as LH
import Lava.Coq as Coq
import Lava.CoqSyntaxUtil (packGetF)
import Lava.CoqUtil (funcHoodLemName, packInstanceName, relDefLemName, relDefName, relDefThmName, toPack, toUPack)
import Lava.Util (hashName)

-- * Generic translations

-- | Translation of builtins
trBuiltin :: LH.Builtin -> Coq.Builtin
trBuiltin Integer = Coq.CTInt
trBuiltin Double = error "Doubles not yet supported in Coq (function Translation.trBuiltin)"
trBuiltin String = error "Strings not yet supported in Coq (function Translation.trBuiltin)"

-- | Translation of datatypes
trDC :: Id -> Id
trDC c | c == LH.unitTmName = Coq.unitTmName
trDC c | c == LH.ttTmName = Coq.btrueTmName
trDC c | c == LH.ffTmName = Coq.bfalseTmName
trDC c = c

-- | Translation of base types
trBaseType :: LH.BaseType -> RocqType
trBaseType (LH.Builtin b) = Coq.Builtin $ trBuiltin b
trBaseType (LH.TC tc) = Coq.TC tc' []
  where
    tc' = case tc of
      _ | tc == boolTpName -> "bool"
      _ | tc == unitTpName -> "Unit"
      _ -> Coq.unrefinedTCName tc

-- | Translation of ILH binary operators to Coq binary operators
trBop :: LH.Bop -> Coq.Bop
trBop LH.Plus = Coq.Plus
trBop LH.Minus = Coq.Minus
trBop LH.Times = Coq.Times
trBop LH.Div = Coq.Div
trBop LH.Mod = Coq.Mod
trBop LH.Eq = Coq.EqualB
trBop LH.Neq = Coq.Neqb
trBop LH.Leq = Coq.Leqb
trBop LH.Geq = Coq.Geqb
trBop LH.Lt = Coq.Ltb
trBop LH.Gt = Coq.Gtb
trBop LH.And = Coq.Andb
trBop LH.Or = Coq.Orb
trBop LH.Impl = Coq.ImplB

-- | Translation of binary proof operators to operators for the refinements
trPop :: LH.ProofOp -> Coq.Bop
trPop = undefined

-- * Unrefined translations

-- | Translation of refinement types
--   Function TtoU (def 3.1) of the paper
utrRefType :: LH.RefType -> RocqType
utrRefType (RefType _ tp _) = trBaseType tp
utrRefType tp@(ArrType {}) =
  let (args, ret) = arrs tp
   in toUPack (map (utrRefType . snd) args) (utrRefType ret)

-- | Translation of refinement types at top level (with arrows and Prop at the end)
utrRefTypeTop :: LH.RefType -> RocqType
utrRefTypeTop tp@(RefType {}) = Arrow (utrRefType tp) (Coq.Sort Coq.PropSort)
utrRefTypeTop (ArrType _ tpx tp) = Coq.Arrow (utrRefType tpx) (utrRefTypeTop tp)

-- | Translation of refinements
--   Function RtoU (def 3.2) of the paper
utrReft :: LH.Reft -> Coq.CoqTerm
utrReft tm0 = case tm0 of
  LH.Var x ar loc -> undefined
  LH.StringLit s -> Coq.StringLiteral s
  LH.IntLit n -> Coq.IntLiteral n
  LH.FloatLit d -> Coq.FloatLiteral d
  LH.DC c -> undefined
  LH.App tm1 tm2 -> undefined
  LH.Neg tm -> undefined
  LH.Bop op tm r -> undefined
  LH.QMark tm hint prop -> undefined
  LH.Pop pop tm1 tm2 -> undefined
  LH.Sub tm tps tpt -> undefined
  LH.Inj tm tp -> undefined
  LH.Proj tm -> Project (trReft [] tm)

-- | Translation of refinements to propositions
--   Function RtoP (def 3.4) of the paper
utrReftProp :: LH.Reft -> Coq.CoqTerm
utrReftProp = undefined

-- * Refined translations

-- | Translation of refinement types
--   Function TtoR (def 3.6) of the paper
trRefType :: LH.RefType -> RocqType
trRefType (RefType x tp r) =
  Coq.Subset x (trBaseType tp) rT
  where
    rT = case tp of
      (LH.Builtin {}) -> utrReftProp r
      (LH.TC tc) -> Coq.And (getTCRef x tc) (utrReftProp r)
trRefType tp@(ArrType {}) =
  let (args, ret) = arrs tp
   in toPack (map (second trRefType) args) (trRefType ret)

-- | Translation of refinement types at top-level (with foralls)
trRefTypeTop :: LH.RefType -> RocqType
trRefTypeTop tp@(RefType {}) = trRefType tp
trRefTypeTop (ArrType x tpx tp) = Coq.FAType (x, trRefType tpx) (trRefTypeTop tp)

-- | Translation of refinements.
--   Takes a typing environment (for type constructors)
--   and the patterns of the arguments as supplementary arguments,
--   to translate applications.
--   Function RtoR (def 3.8) of the paper
trReft :: [Pattern] -> LH.Reft -> Coq.CoqTerm
trReft xs tm0 = case tm0 of
  LH.Var x ar Global | ar > 0 -> Coq.Def $ packInstanceName x
  LH.Var x _ _ -> Coq.Var x
  LH.StringLit s -> Coq.StringLiteral s
  LH.IntLit n -> Coq.IntLiteral n
  LH.FloatLit d -> Coq.FloatLiteral d
  LH.DC c -> Cr (trDC c)
  LH.Neg tm -> Coq.App (Coq.Def Coq.negB) [trReft xs tm]
  LH.Bop op tm1 tm2 -> Coq.Bop (trBop op) (trReft xs tm1) (trReft xs tm2)
  LH.QMark tm hint prop ->
    Coq.Let "_" (Just . Prop $ utrReftProp prop) (Proj2sig $ trReft xs hint) (trReft xs tm)
  LH.Pop pop tm1 tm2 -> undefined
  LH.Sub tm from to -> Coq.SubCast (trRefType to) (trRefType from) (trReft xs tm) (Coq.ProofHole Nothing)
  LH.Inj tm tp -> Coq.Exist (TypeArg $ trRefType tp) (trReft xs tm) (Coq.ProofHole Nothing)
  LH.Proj tm -> error $ "Projection " ++ show tm0 ++ " found outside of refinements in Translation.trReft"
  LH.App {} ->
    let (hd, args) = apps tm0
        argsT = map (trReft xs) args
     in case hd of
          LH.Var f n Recursive -> undefined
          LH.Var f n Local | n > 0 -> Coq.App (packGetF (Coq.Var f)) argsT
          _ -> Coq.App (trReft xs hd) argsT

-- | Translation of expressions as tactics
-- Some other cases might be necessary because of branches coming from Core.
-- Function EtoTac (def 3.7) of the paper
trExprTacs :: [Pattern] -> LH.Expr -> [CoqTactic]
trExprTacs xs e0 = case e0 of
  LH.Reft tm -> [Coq.Exact $ trReft xs tm]
  {- LH.Case cond [("False", [], elseE), ("True", [], thenE)] -> do
    let
      condT = utrSmpTerm (fetchFuncts γ) cond
      transBrExpr _ expr = checkTerm γ expr tp (f, mCtx)
    elseET <- transBrExpr Coq.btrue elseE
    thenET <- transBrExpr Coq.btrue thenE
    return [Coq.Destruct condT [("true", (Coq.ConjDestrPat [], thenET)), ("false", (Coq.ConjDestrPat [], elseET))]] -}
  LH.Case tm alts -> undefined
  -- An if
  {- LH.Let x _ (Reft cond) (LH.Case (LH.Var x' _ _) [("False", [], elseE), ("True", [], thenE)]) | x == x' -> do
    let
      condT = utrSmpTerm (fetchFuncts γ) cond
      transBrExpr _ expr = checkTerm γ expr tp (f, mCtx)
    elseET <- transBrExpr Coq.btrue elseE
    thenET <- transBrExpr Coq.btrue thenE
    return [Coq.Destruct condT [("true", (Coq.ConjDestrPat [], thenET)), ("false", (Coq.ConjDestrPat [], elseET))]] -}
  -- A destruct
  -- LH.Let x _ (Reft r) (LH.Case (LH.Var x' _ _) alts) | x == x' -> trExprTacs γ xs (Case r (mapThd (sub x r) alts))
  LH.Let _ Nothing _ _ -> error "Found let-binding with annotation while translating."
  LH.Let x (Just tpx@(RefType {})) e1 e2 ->
    [ AssertTacs x' (trRefType tpx) (trExprTacs xs e1),
      DestructConj x' x (subsetWitnessNm x)
    ]
      ++ trExprTacs xs e2
    where
      x' = x ++ "'"
  LH.Let x (Just tpx@(ArrType {})) e1 e2 ->
    [ AssertTacs x' (trRefTypeTop tpx) (intros : trExprTacs xs e1),
      assertF
    ]
      ++ trExprTacs xs e2
    where
      (args, ret) = arrs tpx
      intros = Intros $ map (\(xi, _) -> DestrPat $ ConjDestrPat [SingleIdPat xi, SingleIdPat $ subsetWitnessNm xi]) args
      tpxT = trRefTypeTop tpx
      x' = "f_" ++ hashName tpxT
      assertF = Coq.Custom $ "unshelve refine (let " ++ x ++ " : ltac:(buildPackG_spec " ++ x' ++ ") := (ltac:(fun_to_pack " ++ x' ++ ")) in _)"
