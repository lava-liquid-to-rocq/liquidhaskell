{-# LANGUAGE TupleSections #-}

-- | Well-formedness and typing of initial λr terms plus elaboration
module Lava.Elaboration where

import Control.Monad (foldM)
import Data.Either.Extra (maybeToEither)
import Data.Maybe (fromJust)
import Lava.Calculus
import Lava.TypingEnvironment

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
mkBopType bop a1 a2 r2 a3 =
  ArrType "x_1" (RefType "x_1" a1 ttTm) $
    ArrType "x_2" (RefType "x_2" a2 r2) $
      RefType "VV" a3 (Bop Eq (Var "VV" 0 Local) (Bop bop (Proj $ Var "x_1" 0 Local) (Proj $ Var "x_2" 0 Local)))

-- * Simple types

-- Simple types
--
-- T ::= B | TC | T -> T
data SimpleType = SmpBuiltin Builtin | SmpTC Id | SmpArrow SimpleType SimpleType

-- | Projects a refinement type into a simple type
refTptoSmpTp :: RefType -> SimpleType
refTptoSmpTp (RefType _ (TC tc) _) = SmpTC tc
refTptoSmpTp (RefType _ (Builtin b) _) = SmpBuiltin b
refTptoSmpTp (ArrType x tpx tp) = SmpArrow (refTptoSmpTp tpx) (refTptoSmpTp tp)

smpTpCheck :: TypEnv -> Reft -> Either TypeError (SimpleType, Reft)
smpTpCheck γ (Var x _ _) = do
  (loc, tp) <- lookupVar x γ
  return (refTptoSmpTp tp, Var x (arity tp) loc)
smpTpCheck γ r@(StringLit s) = return (SmpBuiltin String, r)
smpTpCheck γ r@(IntLit n) = return (SmpBuiltin Integer, r)
smpTpCheck γ r@(FloatLit f) = return (SmpBuiltin Double, r)
smpTpCheck γ r@(DC c) = do
  tpc <- lookupDC c γ
  return (refTptoSmpTp tpc, r)
smpTpCheck γ (App r1 r2) = do
  (tp1, r1') <- smpTpCheck γ r1
  (tp2, r2') <- smpTpCheck γ r1
  case tp1 of
    SmpArrow tpx tp | tpx == tp2 -> return (tp, App r1' r2')
    _ -> Left . SmpTpErr $ "Too many arguments given in the application " ++ show (App r1 r2)
smpTpCheck γ (Neg r) = do
  (tp, r') <- smpTpCheck γ r
  if tp == SmpTC boolTpName
    then return (tp, Neg r')
    else Left . SmpTpErr $ "Term " ++ show r ++ " should be boolean"
smpTpCheck γ r@(Bop bop r1 r2) | bop == Eq || bop == Neq = do
  (tp1, r1') <- smpTpCheck γ r1
  (tp2, r2') <- smpTpCheck γ r2
  if tp1 == tp2
    then return (SmpTC boolTpName, Bop bop r1' r2')
    else Left . SynErr $ "Different types on both sides of (in)equality " ++ show r ++ ": found " ++ show tp1 ++ " and " ++ show tp2
smpTpCheck γ r@(Bop bop r1 r2) = do
  let SmpArrow tp1 (SmpArrow tp2 tp) = refTptoSmpTp (fromJust $ lookup bop bopTypes)
  (tp1', r1') <- smpTpCheck γ r1
  (tp2', r2') <- smpTpCheck γ r2
  if tp1' == tp1 && tp2' == tp2
    then return (tp, Bop bop r1' r2')
    else Left . SmpTpErr $ "Wrong types for the arguments of the operator " ++ show r
smpTpCheck γ r0@(QMark r rh rp) = do
  (tph, rh') <- smpTpCheck γ rh
  (tp, r') <- smpTpCheck γ r
  if tph == SmpTC boolTpName
    then return (tp, QMark r' rh' rp)
    else Left . SynErr $ "Wrong type (not a refinement of unit) found for the hint in " ++ show r0
smpTpCheck γ (Pop pop r1 r2) = undefined
smpTpCheck γ (Sub r tps tpt) = error "Constructor Sub found in type refinement"
smpTpCheck γ (Inj r tp) = error "Constructor Inj found in type refinement"
smpTpCheck γ (Proj r) = error "Constructor Proj found in type refinement"

-- * Subtyping

-- | Subtyping here just checks that the base types correspond
isSubtype :: RefType -> RefType -> Bool
isSubtype (RefType _ a _) (RefType _ b _) = True
isSubtype (ArrType _ tp11 tp12) (ArrType _ tp21 tp22) =
  isSubtype tp21 tp11 && isSubtype tp12 tp22
isSubtype _ _ = False

-- * Well-formedness of types

wfRefType :: TypEnv -> RefType -> Either TypeError RefType
-- (E-TRef)
wfRefType γ (RefType x tp r) =
  case tp of
    TC tc | not (tc `member` γ) -> Left . WfErr $ "Unknown type " ++ tc
    _ -> do
      γ' <- insertLocalVar γ (x, RefType x tp ttTm)
      RefType x tp <$> smpTpCheck γ' r (SmpTC "Bool")
-- (E-TFun)
wfRefType γ (ArrType x tpx tp) = do
  tpx' <- wfRefType γ tpx
  γ' <- insertLocalVar γ (x, tpx')
  tp' <- wfRefType γ tp
  return $ ArrType x tpx' (subst (Proj (Var x (arity tpx') Local)) x tp')

-- * Well-formedness of declarations

wfDecls :: TypEnv -> [Decl] -> Either TypeError [Decl]
wfDecls = undefined

{- wfDecl γ decl =
  case decl of
    Import x decls ->
        -- TODO: see what we do with the second result value declsT, maybe write them into another file
        do
          (γ', _) <- wfModule γ (LHModule x decls)
          return (γ', [Coq.Load x])
    -- (WF-TC)
    Data tc alts -> do
      okBranches <- foldM (\acc (_, arr) -> (&&) acc <$> checkBranches arr) True alts
      if okBranches
        then (,transDataDecl γ' tc alts) <$> Ctx.insertTC (tc, alts) γ
        else Left . WfErr $ "Faulty constructor: " ++ show tc
      where
        γ' = (tc, Ctx.ΓTC (mapSnd trivializeRefs alts)) : γ
        trivializeRefs :: ArrType -> ArrType
        trivializeRefs (ArrType argTps resTp) = ArrType (mapSnd trivialize argTps) $ trivialize resTp
        trivialize :: RefType -> RefType
        trivialize (RefType x tp _) = RefType x tp ttTm

        checkBranches arr =
          wfArrType γ' arr >> return ((argTp . retTp) arr == TDat tc)
    -- (WF-Def) and (WF-Refl)
    Definition f tp@(ArrType args ret) e isRefl -> do
      γ_ <- Ctx.insertArrType (f, tp) γ
      γ' <- if isRefl then Ctx.insertRelType (f, tp) γ_ else return γ_
      γ'' <- foldM (flip Ctx.insertRefType) γ' args
      tacs <- checkTerm γ'' e ret (f, (map (Var . fst) args, []))
      if isRefl
        then (γ',) <$> transReflDefinition γ f tp e tacs
        else return {- traceFuncRet ["wfDecl", "...", show decl] -} (γ', transDefinition γ f tp tacs) -}

-- * Type synthesis for refinements

synReft :: TypEnv -> Reft -> Either TypeError (RefType, Reft)
synReft γ (Var x _ _) = do
  (loc, tp) <- lookupVar x γ
  case (arity tp, loc) of
    -- (S-VarL)
    (0, Local) -> return (tp, Inj (Var x 0 Local) tp)
    -- (S-Var)
    (ar, _) -> return (tp, Var x ar loc)
-- (S-Lit)
synReft γ r@(StringLit s) = return (litType String r, r)
synReft γ r@(IntLit n) = return (litType Integer r, r)
synReft γ r@(FloatLit f) = return (litType Double r, r)
-- (S-Data)
synReft γ r@(DC c) = (,r) <$> lookupDC c γ
-- (S-App)
synReft γ (App r1 r2) = do
  (tp1, r1') <- synReft γ r1
  case tp1 of
    ArrType x tpx tp -> do
      r2' <- checkReft γ r2 tpx
      return (subst r2' x tp, App r1' r2')
    _ -> Left . SynErr $ "Too many arguments given in the application " ++ show (App r1 r2)
-- (S-Neg)
synReft γ (Neg r) = do
  let (ArrType x tpx tp) = negType
  r' <- checkReft γ r tpx
  return (subst r' x tp, Neg r')
-- (S-Eq) + Neq
synReft γ r@(Bop bop r1 r2) | bop == Eq || bop == Neq = do
  (tp1, r1') <- synReft γ r1
  (tp2, r2') <- synReft γ r2
  case (tp1, tp2) of
    (RefType _ a _, RefType _ b _)
      | a == b ->
          let Just (ArrType x1 _ (ArrType x2 _ tp)) = lookup bop (eqneqTypes a)
           in return (substs [(r2', x2), (r1', x1)] tp, Bop bop r1' r2')
    (RefType _ a _, RefType _ b _) ->
      Left . SynErr $ "Different types on both sides of (in)equality " ++ show r ++ ": found " ++ show a ++ " and " ++ show b
    (_, _) ->
      Left . SynErr $ "(In)Equality on higher-order values is not defined, in the type synthesis of " ++ show r
-- (S-Bin)
synReft γ (Bop bop r1 r2) = do
  let Just (ArrType x1 tp1 (ArrType x2 tp2 tp)) = lookup bop bopTypes
  r1' <- checkReft γ r1 tp1
  r2' <- checkReft γ r2 tp2
  return (substs [(r2', x2), (r1', x1)] tp, Bop bop r1' r2')
-- (S-Hint)
synReft γ r0@(QMark r rh _) = do
  (tph, rh') <- synReft γ rh
  case tph of
    RefType x u rp | u == unitTp -> do
      γ' <- insertLocalVar γ (x, tph)
      (tp, r') <- synReft γ' r
      return (tp, QMark r' rh' rp)
    _ -> Left . SynErr $ "Wrong type (not a refinement of unit) found for the hint in " ++ show r0
-- Not in the paper
synReft γ (Pop pop r1 r2) = undefined
synReft γ (Sub r tps tpt) = error "Constructor Sub found before elaboration"
synReft γ (Inj r tp) = error "Constructor Inj found before elaboration"
synReft γ (Proj r) = error "Constructor Proj found before elaboration"

-- * Type checking of expressions

-- | Type checking for refinements, always by subtyping
checkReft :: TypEnv -> Reft -> RefType -> Either TypeError Reft
checkReft γ r tp = do
  (tp_r, r') <- synReft γ r
  if isSubtype tp_r tp
    then return (Sub r' tp_r tp)
    else Left . SubtypingErr $ "Synthesized type " ++ show tp_r ++ " for " ++ show r ++ " is not a subtype of type " ++ show tp

checkExpr :: TypEnv -> Expr -> RefType -> Either TypeError Expr
-- (C-Syn)
checkExpr γ (Reft r) tp = Reft <$> checkReft γ r tp
-- (C-Let)
checkExpr γ (Let x (Just tpx) ex e) tp = do
  _ <- wfRefType γ tp -- check that tp does not depend on x
  tpx' <- wfRefType γ tpx
  let (args, ret) = arrs tpx'
  γx <- foldM insertLocalVar γ args
  ex' <- checkExpr γx ex ret
  γ' <- insertLocalVar γ (x, tpx')
  e' <- checkExpr γ' e tp
  return (Let x (Just tpx') ex' e')
-- Not in the paper, but in case we have no annotation
checkExpr γ (Let x Nothing (Reft r) e) tp = do
  _ <- wfRefType γ tp -- check that tp does not depend on x
  (tpr, r') <- synReft γ r
  γ' <- insertLocalVar γ (x, tpr)
  e' <- checkExpr γ' e tp
  return (Let x (Just tpr) (Reft r') e')
checkExpr _ e@(Let {}) _ = Left . CheckingErr $ "Type annotation expected for the let-binding " ++ show e
-- (C-Case)
checkExpr γ e0@(Case r branches) tp = do
  (tpr, r') <- synReft γ r
  case tpr of
    RefType v (TC tc) rv -> do
      branches' <- mapM checkBranch branches
      return (Case r' branches')
    _ -> Left . CheckingErr $ "Matched term is not of an inductive type in expression " ++ show e0
  where
    checkBranch :: ((Id, [Id]), Maybe Expr) -> Either TypeError ((Id, [Id]), Maybe Expr)
    checkBranch (c, Nothing) = return (c, Nothing)
    checkBranch br@((c, ys), Just e) = do
      tpc <- lookupDC c γ
      -- Replace the binders in tpc by the names of the match in ys
      let tpcRenamed = renames (zip ys (tpArgs tpc)) tpc
      let (argsc, RefType v _ r) = arrs tpcRenamed
      -- TODO: add additional type with z for occurence typing
      γ' <- foldM insertLocalVar γ argsc
      e' <- checkExpr γ' e tp
      return ((c, ys), Just e')
