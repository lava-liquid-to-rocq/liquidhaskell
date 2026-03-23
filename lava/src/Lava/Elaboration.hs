{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

-- | Well-formedness and typing of initial λr terms plus elaboration
module Lava.Elaboration where

import Control.Monad (foldM, when)
import Data.Bifunctor (second)
import Data.List (unsnoc)
import Data.Maybe (fromJust, listToMaybe)
import Lava.Calculus
import Lava.TypingEnvironment
import Text.PrettyPrint
import Text.PrettyPrint.HughesPJClass hiding (first)

-- * Entry point for elaboration and typing

-- Typecheck and elaborate a list of declarations
elaborate :: [Decl] -> Either TypeError [Decl]
elaborate = wfDecls initial

-- * Types of primitives

-- | Singleton type of a literal
litType :: Builtin -> Reft -> RefType
litType tp l = RefType "VV" (Builtin tp) (Bop Eq (Var "VV" 0 Local) l)

-- | Type of negation, with singleton return type
negType :: RefType
negType = ArrType "x" (RefType "x" boolTp ttTm) (RefType "VV" boolTp (Bop Eq (Var "VV" 0 Local) (Neg . Proj $ Var "x" 0 Local)))

-- | Types of binary operators, with singleton return type
bopTypes :: [(Bop, RefType)]
bopTypes =
  [ (Plus, mkBopType Plus (Builtin Integer) (Builtin Integer) ttTm (Builtin Integer)),
    (Minus, mkBopType Minus (Builtin Integer) (Builtin Integer) ttTm (Builtin Integer)),
    (Times, mkBopType Times (Builtin Integer) (Builtin Integer) ttTm (Builtin Integer)),
    (Div, mkBopType Div (Builtin Integer) (Builtin Integer) (Bop Neq (Var "x_2" 0 Local) (IntLit 0)) (Builtin Integer)),
    (Mod, mkBopType Mod (Builtin Integer) (Builtin Integer) (Bop Neq (Var "x_2" 0 Local) (IntLit 0)) (Builtin Integer)),
    (Leq, mkBopType Leq (Builtin Integer) (Builtin Integer) ttTm boolTp),
    (Geq, mkBopType Geq (Builtin Integer) (Builtin Integer) ttTm boolTp),
    (Lt, mkBopType Lt (Builtin Integer) (Builtin Integer) ttTm boolTp),
    (Gt, mkBopType Gt (Builtin Integer) (Builtin Integer) ttTm boolTp),
    (And, mkBopType And boolTp boolTp ttTm boolTp),
    (Or, mkBopType Or boolTp boolTp ttTm boolTp),
    (Impl, mkBopType Impl boolTp boolTp ttTm boolTp)
  ]

-- | Type of the equality and inequality for any base type
eqneqTypes :: BaseType -> [(Bop, RefType)]
eqneqTypes b = [(Eq, mkBopType Eq b b ttTm boolTp), (Neq, mkBopType Neq b b ttTm boolTp)]

-- | Wrapper for the arrow type for a binary operator, with specialization of the output refinement
mkBopType :: Bop -> BaseType -> BaseType -> Reft -> BaseType -> RefType
mkBopType bop a1 a2 r2 a3 =
  ArrType "x_1" (RefType "x_1" a1 ttTm) $
    ArrType "x_2" (RefType "x_2" a2 r2) $
      RefType "VV" a3 (Bop Eq (Var "VV" 0 Local) (Bop bop (Proj $ Var "x_1" 0 Local) (Proj $ Var "x_2" 0 Local)))

-- * Simple types, used for typing type refinements

-- Simple types
--
-- T ::= B | TC | T -> T
data SimpleType = SmpBuiltin Builtin | SmpTC Id | SmpArrow SimpleType SimpleType
  deriving (Eq)

-- | Extracts the elements out of an SmpArrow and raises an error for another type
fromSmpArrow :: SimpleType -> (SimpleType, SimpleType)
fromSmpArrow (SmpArrow tp1 tp2) = (tp1, tp2)
fromSmpArrow _ = error "SmpArrow expected"

instance Pretty SimpleType where
  pPrint (SmpBuiltin b) = pPrint b
  pPrint (SmpTC tc) = text tc
  pPrint (SmpArrow tp1 tp2) = pPrint tp1 <+> text "->" <+> pPrint tp2

-- | Projects a refinement type into a simple type
refTptoSmpTp :: RefType -> SimpleType
refTptoSmpTp (RefType _ (TC tc) _) = SmpTC tc
refTptoSmpTp (RefType _ (Builtin b) _) = SmpBuiltin b
refTptoSmpTp (ArrType _ tpx tp) = SmpArrow (refTptoSmpTp tpx) (refTptoSmpTp tp)

-- | If the application in argument is a recursive call,
-- choose an induction variable and updates the localization with
-- the variable and the current branch pattern
-- We return a term App r1 r2 (without App constructor) to avoid a partial
-- pattern matching in the main functions
chooseIndVar :: TypEnv -> BranchPattern -> (Reft, [Reft]) -> Either TypeError (Reft, Reft)
chooseIndVar γ pats (hd, args) =
  case hd of
    Var x ar _ -> do
      (loc, _) <- lookupVar x γ
      case loc of
        Recursive {} ->
          let -- The inductive variables are those that appear after a single
              -- destruction of a parameter and that are used as an argument
              -- of the application we are translating in the same position
              -- as the parameter they originate from
              indVarCandidates =
                [ y
                | (Var y _ _, (DC _, ys)) <- zip args (map apps pats),
                  -- this enforces that y is obtained after a single
                  -- destruction, rather than using freeVars ys
                  y `elem` [y' | Var y' _ _ <- ys]
                ]
              -- We arbitrarily choose the first of the candidates to be the
              -- variable we do induction on
              indVar = case listToMaybe indVarCandidates of
                Nothing -> error $ "No possible induction variable in term " ++ prettyShow ogTerm
                Just y -> y
           in return (foldl App (Var x ar (Recursive indVar pats)) args', argsLast)
        _ -> return ogTerm
    _ -> return ogTerm
  where
    (args', argsLast) = fromJust (unsnoc args)
    ogTerm = (foldl App hd args', argsLast)

smpTpCheck :: TypEnv -> BranchPattern -> Reft -> Either TypeError (SimpleType, Reft)
smpTpCheck γ _ (Var x _ _) = do
  (loc, tp) <- lookupVar x γ
  return (refTptoSmpTp tp, Var x (arity tp) loc)
smpTpCheck _ _ r@(StringLit _) = return (SmpBuiltin String, r)
smpTpCheck _ _ r@(IntLit _) = return (SmpBuiltin Integer, r)
smpTpCheck _ _ r@(FloatLit _) = return (SmpBuiltin Double, r)
smpTpCheck γ _ r@(DC c) = do
  tpc <- lookupDC c γ
  return (refTptoSmpTp tpc, r)
smpTpCheck γ pats r@(App {}) = do
  (r1, r2) <- chooseIndVar γ pats (apps r)
  (tp1, r1') <- smpTpCheck γ pats r1
  (tp2, r2') <- smpTpCheck γ pats r1
  case tp1 of
    SmpArrow tpx tp | tpx == tp2 -> return (tp, App r1' r2')
    _ -> Left . SmpTpErr $ "Too many arguments given in the application " ++ prettyShow (App r1 r2)
smpTpCheck γ pats (Neg r) = do
  (tp, r') <- smpTpCheck γ pats r
  if tp == SmpTC boolTpName
    then return (tp, Neg r')
    else Left . SmpTpErr $ "Term " ++ prettyShow r ++ " should be boolean"
smpTpCheck γ pats r@(Bop bop r1 r2) | bop == Eq || bop == Neq = do
  (tp1, r1') <- smpTpCheck γ pats r1
  (tp2, r2') <- smpTpCheck γ pats r2
  if tp1 == tp2
    then return (SmpTC boolTpName, Bop bop r1' r2')
    else Left . SmpTpErr $ "Different types on both sides of (in)equality " ++ prettyShow r ++ ": found " ++ prettyShow tp1 ++ " and " ++ prettyShow tp2
smpTpCheck γ pats r@(Bop bop r1 r2) = do
  let (tp1, (tp2, tp)) = second fromSmpArrow . fromSmpArrow $ refTptoSmpTp (fromJust $ lookup bop bopTypes)
  (tp1', r1') <- smpTpCheck γ pats r1
  (tp2', r2') <- smpTpCheck γ pats r2
  if tp1' == tp1 && tp2' == tp2
    then return (tp, Bop bop r1' r2')
    else Left . SmpTpErr $ "Wrong types for the arguments of the operator " ++ prettyShow r
smpTpCheck γ pats r0@(QMark r rh rp) = do
  (tph, rh') <- smpTpCheck γ pats rh
  (tp, r') <- smpTpCheck γ pats r
  if tph == SmpTC boolTpName
    then return (tp, QMark r' rh' rp)
    else Left . SmpTpErr $ "Wrong type (not a refinement of unit) found for the hint in " ++ prettyShow r0
smpTpCheck γ pats r@(Pop pop r1 r2) = do
  (tp1, r1') <- smpTpCheck γ pats r1
  (tp2, r2') <- smpTpCheck γ pats r2
  if tp1 == tp2
    then return (tp1, Pop pop r1' r2')
    else Left . SmpTpErr $ "Different types on both sides of proof combinators " ++ prettyShow r ++ ": found " ++ prettyShow tp1 ++ " and " ++ prettyShow tp2
smpTpCheck _ _ (Sub {}) = error "Constructor Sub found in type refinement"
smpTpCheck _ _ (Inj {}) = error "Constructor Inj found in type refinement"
smpTpCheck _ _ (Proj {}) = error "Constructor Proj found in type refinement"

-- * Subtyping

-- | Subtyping here just checks that the base types correspond
isSubtype :: RefType -> RefType -> Bool
isSubtype (RefType _ a _) (RefType _ b _) = a == b
isSubtype (ArrType _ tp11 tp12) (ArrType _ tp21 tp22) =
  isSubtype tp21 tp11 && isSubtype tp12 tp22
isSubtype _ _ = False

-- * Well-formedness of types

wfRefType :: TypEnv -> BranchPattern -> RefType -> Either TypeError RefType
-- (E-TRef)
wfRefType γ pats (RefType x tp r) =
  case tp of
    TC tc | not (tc `member` γ) -> Left . WfErr $ "Unknown type " ++ tc
    _ -> do
      γ' <- insertLocalVar γ (x, RefType x tp ttTm)
      (tp_r, r') <- smpTpCheck γ' pats r
      if tp_r == SmpTC boolTpName
        then return $ RefType x tp r'
        else Left . WfErr $ "Refinement of type " ++ prettyShow (RefType x tp r) ++ " is not boolean"
-- (E-TFun)
wfRefType γ pats (ArrType x tpx tp) = do
  tpx' <- wfRefType γ pats tpx
  γ' <- insertLocalVar γ (x, tpx')
  tp' <- wfRefType γ' pats tp
  return $ ArrType x tpx' (subst (Proj (Var x (arity tpx') Local)) x tp')

-- * Well-formedness of declarations

wfDecls :: TypEnv -> [Decl] -> Either TypeError [Decl]
-- (WF-DTC)
wfDecls γ (Data tc constrs : decls) = do
  γ' <- foldM checkBranch γ constrs
  -- NOTE: Here we used to replace all refinements of the constructors by ttTm in the new context. Why??
  wfDecls γ' decls
  where
    checkBranch :: TypEnv -> (Id, RefType) -> Either TypeError TypEnv
    checkBranch γi (ci, tpi) = do
      checkFOandTC tpi
      tpi' <- wfRefType γi [] tpi
      insertDCinTC γi (ci, tpi') tc
    checkFOandTC :: RefType -> Either TypeError ()
    checkFOandTC tp =
      let (args, (_, tc', _)) = second fromRefType $ arrs tp
       in if any ((\case RefType {} -> False; _ -> True) . snd) args
            then Left . WfErr $ "The constructor type " ++ prettyShow tp ++ " is higher-order, which is forbidden"
            else when (tc' /= TC tc) . Left . WfErr $ "The constructor type " ++ prettyShow tp ++ " must return a refinement of " ++ prettyShow tc
-- (WF-DDef)
wfDecls γ (Definition f tpf e isRefl : decls) = do
  tpf' <- wfRefType γ [] tpf
  γf <- insertRecVar γ (f, tpf')
  let (args, ret) = arrs tpf'
  γfargs <- foldM insertLocalVar γf args
  let initBrPat = map (\(x, tpx) -> Var x (arity tpx) Local) args
  e' <- checkExpr γfargs initBrPat e ret
  decls' <- wfDecls γf decls
  return $ Definition f tpf e' isRefl : decls'
wfDecls _ [] = return []

-- * Type synthesis for refinements

synReft :: TypEnv -> BranchPattern -> Reft -> Either TypeError (RefType, Reft)
synReft γ _ (Var x _ _) = do
  (loc, tp) <- lookupVar x γ
  case (arity tp, loc) of
    -- (S-VarL)
    (0, Local) -> return (tp, Inj (Var x 0 Local) tp)
    -- (S-Var)
    (ar, _) -> return (tp, Var x ar loc)
-- (S-Lit)
synReft _ _ r@(StringLit _) = return (litType String r, r)
synReft _ _ r@(IntLit _) = return (litType Integer r, r)
synReft _ _ r@(FloatLit _) = return (litType Double r, r)
-- (S-Data)
synReft γ _ r@(DC c) = (,r) <$> lookupDC c γ
-- (S-App)
synReft γ pats r@(App {}) = do
  (r1, r2) <- chooseIndVar γ pats (apps r)
  (tp1, r1') <- synReft γ pats r1
  case tp1 of
    ArrType x tpx tp -> do
      r2' <- checkReft γ pats r2 tpx
      return (subst r2' x tp, App r1' r2')
    _ -> Left . SynErr $ "Too many arguments given in the application " ++ prettyShow (App r1 r2)
-- (S-Neg)
synReft γ pats (Neg r) = do
  let (x, tpx, tp) = fromArrType negType
  r' <- checkReft γ pats r tpx
  return (subst r' x tp, Neg r')
-- (S-Eq) + Neq
synReft γ pats r@(Bop bop r1 r2) | bop == Eq || bop == Neq = do
  (tp1, r1') <- synReft γ pats r1
  (tp2, r2') <- synReft γ pats r2
  case (tp1, tp2) of
    (RefType _ a _, RefType _ b _)
      | a == b ->
          let (x1, _, (x2, _, tp)) =
                second fromArrType . fromArrType . fromJust $ lookup bop (eqneqTypes a)
           in return (substs [(r2', x2), (r1', x1)] tp, Bop bop r1' r2')
    (RefType _ a _, RefType _ b _) ->
      Left . SynErr $ "Different types on both sides of (in)equality " ++ prettyShow r ++ ": found " ++ prettyShow a ++ " and " ++ prettyShow b
    (_, _) ->
      Left . SynErr $ "(In)Equality on higher-order values is not defined, in the type synthesis of " ++ prettyShow r
-- (S-Bin)
synReft γ pats (Bop bop r1 r2) = do
  let (x1, tp1, (x2, tp2, tp)) =
        second fromArrType . fromArrType . fromJust $ lookup bop bopTypes
  r1' <- checkReft γ pats r1 tp1
  r2' <- checkReft γ pats r2 tp2
  return (substs [(r2', x2), (r1', x1)] tp, Bop bop r1' r2')
-- (S-Hint)
synReft γ pats r0@(QMark r rh _) = do
  (tph, rh') <- synReft γ pats rh
  case tph of
    RefType x u rp | u == unitTp -> do
      γ' <- insertLocalVar γ (x, tph)
      (tp, r') <- synReft γ' pats r
      return (tp, QMark r' rh' rp)
    _ -> Left . SynErr $ "Wrong type (not a refinement of unit) found for the hint in " ++ prettyShow r0
-- Not in the paper
synReft γ pats r@(Pop pop r1 r2) = do
  (tp1, r1') <- synReft γ pats r1
  case tp1 of
    ArrType {} -> Left . SynErr $ "Proof combinators on higher-order values is not defined, in the type synthesis of " ++ prettyShow r
    RefType x a reft1 -> do
      let xvar = Var x 0 Local
          reft2 = Bop And reft1 (Bop (popToBop pop) xvar (Proj r1'))
      r2' <- checkReft γ pats r2 (RefType x a reft2)
      let reft3' = Bop And reft1 (Bop Eq xvar (Proj r2'))
          reft3 = case pop of PEq -> Bop And reft3' (Bop Eq xvar (Proj r1')); _ -> reft3'
      return (RefType x a reft3, Pop pop r1' r2')
synReft _ _ (Sub {}) = error "Constructor Sub found before elaboration"
synReft _ _ (Inj {}) = error "Constructor Inj found before elaboration"
synReft _ _ (Proj {}) = error "Constructor Proj found before elaboration"

-- * Type checking of expressions

-- | Type checking for refinements, always by subtyping
checkReft :: TypEnv -> BranchPattern -> Reft -> RefType -> Either TypeError Reft
checkReft γ pats r tp = do
  (tp_r, r') <- synReft γ pats r
  if isSubtype tp_r tp
    then return (Sub r' tp_r tp)
    else Left . SubtypingErr $ "Synthesized type " ++ prettyShow tp_r ++ " for " ++ prettyShow r ++ " is not a subtype of type " ++ prettyShow tp

checkExpr :: TypEnv -> BranchPattern -> Expr -> RefType -> Either TypeError Expr
-- (C-Syn)
checkExpr γ pats (Reft r) tp = Reft <$> checkReft γ pats r tp
-- (C-Let)
checkExpr γ pats (Let x (Just tpx) ex e) tp = do
  _ <- wfRefType γ pats tp -- check that tp does not depend on x
  tpx' <- wfRefType γ pats tpx
  let (args, ret) = arrs tpx'
  γx <- foldM insertLocalVar γ args
  ex' <- checkExpr γx pats ex ret
  γ' <- insertLocalVar γ (x, tpx')
  e' <- checkExpr γ' pats e tp
  return (Let x (Just tpx') ex' e')
-- Not in the paper, but in case we have no annotation
checkExpr γ pats (Let x Nothing (Reft r) e) tp = do
  _ <- wfRefType γ pats tp -- check that tp does not depend on x
  (tpr, r') <- synReft γ pats r
  γ' <- insertLocalVar γ (x, tpr)
  e' <- checkExpr γ' pats e tp
  return (Let x (Just tpr) (Reft r') e')
checkExpr _ _ e@(Let {}) _ = Left . CheckingErr $ "Type annotation expected for the let-binding " ++ prettyShow e
-- (C-Case)
checkExpr γ pats e0@(Case r branches _) tp = do
  (tpr, r') <- synReft γ pats r
  case tpr of
    RefType _ (TC _) _ -> do
      -- We translate to induct when we destruct one of the parameters
      let isInduct = case r of Var _ 0 Local -> r `elem` pats; _ -> False
      branches' <- mapM (`checkBranch` isInduct) branches
      -- In the first induct, we generalize the other parameters
      -- FIX: if the first destruction of a parameter is translated to destruct,
      -- we never generalize the variables
      let genVars =
            let onTopLevel = all (\case (Var {}) -> True; _ -> False) pats
             in reverse [z | zvar@(Var z 0 Local) <- pats, zvar /= r, onTopLevel, isInduct]
      return (Case r' branches' genVars)
    _ -> Left . CheckingErr $ "Matched term is not of an inductive type in expression " ++ prettyShow e0
  where
    -- The booleans on the introduced variables are just placeholder, we
    -- instantiate them here for real
    checkBranch :: ((Id, [(Id, Bool)]), Maybe Expr) -> Bool -> Either TypeError ((Id, [(Id, Bool)]), Maybe Expr)
    checkBranch (c, Nothing) _ = return (c, Nothing)
    checkBranch ((c, ys), Just e) isInduct = do
      tpc <- lookupDC c γ
      -- Replace the binders in tpc by the names of the match in ys
      let tpcRenamed = renames (zip (map fst ys) (tpArgs tpc)) tpc
      let (argsc, (_, tc, _)) = second fromRefType $ arrs tpcRenamed
      -- TODO: add additional type with z for occurence typing
      γ' <- foldM insertLocalVar γ argsc
      e' <- checkExpr γ' pats e tp
      -- True for inductive variables in ys if isInduct
      let inductives = map (\case (_, RefType _ tc' _) -> tc' == tc && isInduct; (_, ArrType {}) -> False) argsc
          ys' = zip (map fst ys) inductives
      return ((c, ys'), Just e')
