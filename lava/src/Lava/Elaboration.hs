{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

-- | Well-formedness and typing of initial λr terms plus elaboration
module Lava.Elaboration where

import Control.Monad (foldM, mapAndUnzipM, when)
import Data.Bifunctor (first, second)
import Data.List (delete, elemIndex, (!?), (\\))
import Data.Maybe (fromJust, isJust)
import Data.Set (Set)
import qualified Data.Set as Set
import Lava.Calculus
import Lava.Names (Id)
import Lava.TypingEnvironment hiding (delete)
import qualified Lava.TypingEnvironment as Env
import Text.PrettyPrint
import Text.PrettyPrint.HughesPJClass hiding (first)
import Prelude hiding ((<>))

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
  [ (Plus, mkBopType Plus intTp intTp ttTm intTp),
    (Minus, mkBopType Minus intTp intTp ttTm intTp),
    (Times, mkBopType Times intTp intTp ttTm intTp),
    (Div, mkBopType Div intTp intTp x2NotZero intTp),
    (Mod, mkBopType Mod intTp intTp x2NotZero intTp),
    (Leq, mkBopType Leq intTp intTp ttTm boolTp),
    (Geq, mkBopType Geq intTp intTp ttTm boolTp),
    (Lt, mkBopType Lt intTp intTp ttTm boolTp),
    (Gt, mkBopType Gt intTp intTp ttTm boolTp),
    (And, mkBopType And boolTp boolTp ttTm boolTp),
    (Or, mkBopType Or boolTp boolTp ttTm boolTp),
    (Impl, mkBopType Impl boolTp boolTp ttTm boolTp),
    (Iff, mkBopType Iff boolTp boolTp ttTm boolTp)
  ]
  where
    intTp = Builtin Integer
    x2NotZero = Bop Neq (Var "x_2" 0 Local) (IntLit 0)

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
  pPrint (SmpArrow tp1 tp2) = pPrint tp1 <+> "->" <+> pPrint tp2

-- | Projects a refinement type into a simple type
refTptoSmpTp :: RefType -> SimpleType
refTptoSmpTp (RefType _ (TC tc) _) = SmpTC tc
refTptoSmpTp (RefType _ (Builtin b) _) = SmpBuiltin b
refTptoSmpTp (ArrType _ tpx tp) = SmpArrow (refTptoSmpTp tpx) (refTptoSmpTp tp)

-- | Type checking in a simple type system, used to typecheck type refinements
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
        "Too many arguments given in the application" <+> pPrint (App r1' r2') <+> colon
          $$ pPrint r1' <+> "has type" <+> pPrint r1'
smpTpCheck γ (Neg r) = do
  (tp, r') <- smpTpCheck γ r
  if tp == SmpTC boolTpName
    then return (tp, Neg r')
    else Left . SmpTpErr $ "Term" <+> pPrint r <+> "should be boolean"
smpTpCheck γ r@(Bop bop r1 r2) | bop == Eq || bop == Neq = do
  (tp1, r1') <- smpTpCheck γ r1
  (tp2, r2') <- smpTpCheck γ r2
  if tp1 == tp2
    then return (SmpTC boolTpName, Bop bop r1' r2')
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

-- * Subtyping

-- | Subtyping here just checks that the base types correspond
isSubtype :: RefType -> RefType -> Bool
isSubtype (RefType _ a _) (RefType _ b _) = a == b
isSubtype (ArrType _ tp11 tp12) (ArrType _ tp21 tp22) =
  isSubtype tp21 tp11 && isSubtype tp12 tp22
isSubtype _ _ = False

-- | Check if the type is a unit proof type {{P}}, i.e. its base type is unitTp.
isUnitRefType :: RefType -> Bool
isUnitRefType (RefType _ a _) = a == unitTp
isUnitRefType _ = False

-- * Well-formedness of types

wfRefType :: TypEnv -> RefType -> Either TypeError RefType
-- (E-TRef)
wfRefType γ (RefType x tp r) =
  case tp of
    TC tc | tc `notMember` γ -> Left . WfErr $ "Unknown type" <+> text tc
    _ -> do
      let γ' = insertLocalVar (x, RefType x tp ttTm) γ
      (tp_r, r') <- smpTpCheck γ' r
      if tp_r == SmpTC boolTpName
        then return $ RefType x tp r'
        else Left . WfErr $ "Refinement of type" <+> pPrint (RefType x tp r') <+> "is not boolean"
-- (E-TFun)
wfRefType γ (ArrType x tpx tp) = do
  tpx' <- wfRefType γ tpx
  let γ' = insertLocalVar (x, tpx') γ
  tp' <- wfRefType γ' tp
  return $ ArrType x tpx' (subst (Proj (Var x (arity tpx') Local)) x tp')

-- * Well-formedness of declarations

wfDecls :: TypEnv -> [Decl] -> Either TypeError [Decl]
-- wfDecls _ (d : _) | traceFunc "wfDecls" [pPrint d] = undefined
-- (WF-DTC)
wfDecls γ (Data tc constrs : decls) = do
  -- We pre-populate the environment with all constructors using trivialized
  -- refinements, so that refinements of any constructor can refer to any other
  -- constructor of the same type (not just previously declared ones).
  let γtc = insertTC (tc, map (second trivializeRefs) constrs) γ
  (γ', constrs') <- foldM checkBranch (γtc, []) constrs
  decls' <- wfDecls γ' decls
  return $ Data tc (reverse constrs') : decls'
  where
    trivializeRefs :: RefType -> RefType
    trivializeRefs (RefType x tp _) = RefType x tp ttTm
    trivializeRefs (ArrType x tpx tp) = ArrType x (trivializeRefs tpx) (trivializeRefs tp)
    checkBranch :: (TypEnv, [(Id, RefType)]) -> (Id, RefType) -> Either TypeError (TypEnv, [(Id, RefType)])
    checkBranch (γi, dcs) (ci, tpi) = first (annotateErr ci) $ do
      checkFOandTC tpi
      tpi' <- wfRefType γi tpi
      -- Replace the trivialized entry for ci with the elaborated one
      γtc <- lookupTC tc γi
      let γtc' = map (\(c, tp) -> if c == ci then (ci, tpi') else (c, tp)) γtc
      return (insertTC (tc, γtc') γi, (ci, tpi') : dcs)
    checkFOandTC :: RefType -> Either TypeError ()
    checkFOandTC tp =
      let (args, (_, tc', _)) = arrs tp
       in if any ((\case RefType {} -> False; _ -> True) . snd) args
            then Left . WfErr $ "The constructor type" <+> pPrint tp <+> "is higher-order, which is forbidden"
            else when (tc' /= TC tc) . Left . WfErr $ "The constructor type" <+> pPrint tp <+> "must return a refinement of" <+> text tc
-- (WF-DDef)
wfDecls γ (Definition f tpf e isRefl : decls) = do
  tpf' <- inDecl $ wfRefType γ tpf
  let γf = insertRecVar (f, tpf') γ
  let (args, ret) = second mkRefType $ arrs tpf'
  -- We remove the projections around the parameters,
  -- because the parameters are destructed and thus considered unrefined in the
  -- elaboration of the body.
  -- We do not do it for the type tpf' because it is the complete dependent
  -- arrow that binds the parameters as refined
  let γfargs = insertLocalVars (map (second removeFOArgProjs) args) γf
  let initBrPat = map (\(x, tpx) -> Param x (arity tpx)) args
  -- We remove the projections of parameters from ret, since parameters are
  -- considered unrefined
  e' <- inDecl $ checkExpr γfargs initBrPat (removeRedundantMatches e) (removeFOArgProjs ret)
  γf' <- inDecl $ changeRecToGlobal f γf
  decls' <- wfDecls γf' decls
  return $ Definition f tpf' e' isRefl : decls'
  where
    inDecl = first (annotateErr f)
-- doesn't exist in the paper, could be called WF-DImp
wfDecls γ (Import modName decls : rest) = do
  -- Trust imported declarations and insert their types into the environment.
  -- We do not re-elaborate imported decls (they are elaborated in their own module).
  let γ' = populateFromImport γ decls
  decls' <- wfDecls γ' rest
  return $ Import modName decls : decls'
  where
    populateFromImport env [] = env
    populateFromImport env (Data tc constrs : ds) =
      populateFromImport (insertTC (tc, constrs) env) ds
    populateFromImport env (Definition f tp _ _ : ds) =
      populateFromImport (insertGlobalVar (f, tp) env) ds
    populateFromImport env (Import _ innerDecls : ds) =
      populateFromImport (populateFromImport env innerDecls) ds
wfDecls _ [] = return []

-- Remove matches on a constructor and inline let x := tm in if tm then … else …
-- We do this first because having redundant matches of the first kind interacts badly with induction
removeRedundantMatches :: Expr -> Expr
removeRedundantMatches e@(Case r branches genVars) =
  case apps r of
    (DC c, argsc) ->
      let br = filter ((==) c . fst . fst) branches
       in case br of
            -- TODO: We should use Maybe in the translation from Core rather than "undefined"
            (_, Just (Reft (Var "undefined" _ _))) : _ -> e
            ((_, ys), Just ebr) : _ -> removeRedundantMatches $ substs (zip argsc (map fst ys)) ebr
            _ -> recurse
    _ -> recurse
  where
    recurse = Case r (map (second $ fmap removeRedundantMatches) branches) genVars
removeRedundantMatches (Reft r) = Reft r
removeRedundantMatches (Let x _ (Reft tm) (Case (Var x' _ _) branches genVars))
  | x == x' && all xNotInBranch branches =
      removeRedundantMatches (Case tm branches genVars)
  where
    xNotInBranch (_, Nothing) = True
    xNotInBranch ((_, ys), Just e) =
      x `elem` map fst ys || not (x `Set.member` freeVars e)
removeRedundantMatches (Let x tpx ex e) =
  Let x tpx (removeRedundantMatches ex) (removeRedundantMatches e)

-- * Type synthesis for refinements

synReft :: TypEnv -> Reft -> Either TypeError (RefType, Reft)
synReft γ (Var x _ locx) = do
  (locγ, tp) <- lookupVar x γ
  case (arity tp, locγ) of
    -- (S-VarL)
    (0, Local) -> return (tp, Inj (Var x 0 Local) tp)
    -- For recursive variables, the localization must be instantiated when
    -- elaborating matches.
    -- If not, we have not been able to find an inductive variable for this occurence of the application
    (ar, Recursive {}) ->
      case locx of
        Recursive {} -> return (tp, Var x ar locx)
        _ -> Left . SynErr $ "Impossible to build induction for an occurence of the function" <+> text x <> ". Found locx =" <+> pPrint locx
    -- (S-Var)
    (ar, _) -> return (tp, Var x ar locγ)
-- (S-Lit)
synReft _ r@(StringLit _) = let tp = litType String r in return (tp, Inj r tp)
synReft _ r@(IntLit _) = let tp = litType Integer r in return (tp, Inj r tp)
synReft _ r@(FloatLit _) = let tp = litType Double r in return (tp, Inj r tp)
-- Builtin data constructors (supposed unrefined, in contrary to the others)
synReft γ r@(DC c) | r `elem` builtinDCs = do
  tp <- lookupDC c γ
  return (tp, Inj r tp)
-- (S-Data)
synReft γ r@(DC c) = (,r) <$> lookupDC c γ
-- (S-App)
synReft γ r@(App r1 r2) = do
  (tp1, r1') <- synReft γ r1
  case tp1 of
    ArrType x tpx tp -> do
      r2' <- checkReft γ r2 tpx
      return (subst r2' x tp, App r1' r2')
    _ -> Left . SynErr $ "Too many arguments given in the application" <+> pPrint r
-- (S-Neg)
synReft γ (Neg r) = do
  let (x, tpx, tp) = fromArrType negType
  r' <- checkReft γ r tpx
  return (subst r' x tp, Neg r')
-- (S-Eq) + Neq
synReft γ r@(Bop bop r1 r2) | bop == Eq || bop == Neq = do
  (tp1, r1') <- synReft γ r1
  (tp2, r2') <- synReft γ r2
  case (tp1, tp2) of
    (RefType _ a _, RefType _ b _)
      | a == b ->
          let (x1, _, (x2, _, tp)) =
                second fromArrType . fromArrType . fromJust $ lookup bop (eqneqTypes a)
           in return (substs [(r2', x2), (r1', x1)] tp, Bop bop r1' r2')
    (RefType _ a _, RefType _ b _) ->
      Left . SynErr $ "Different types on both sides of (in)equality" <+> pPrint r <> ": found" <+> pPrint a <+> "and" <+> pPrint b
    (_, _) ->
      Left . SynErr $ "(In)Equality on higher-order values is not defined, in the type synthesis of" <+> pPrint r
-- (S-Bin)
synReft γ (Bop bop r1 r2) = do
  let (x1, tp1, (x2, tp2, tp)) =
        second fromArrType . fromArrType . fromJust $ lookup bop bopTypes
  r1' <- checkReft γ r1 tp1
  r2' <- checkReft γ r2 tp2
  return (substs [(r2', x2), (r1', x1)] tp, Bop bop r1' r2')
-- (S-Hint)
synReft γ r0@(QMark r rh _) = do
  (tph, rh') <- synReft γ rh
  case tph of
    RefType x _ rp -> do
      let γ' = insertLocalVar (x, tph) γ
      (tp, r') <- synReft γ' r
      return (tp, QMark r' rh' rp)
    _ -> Left . SynErr $ "Higher-order value found as a hint in" <+> pPrint r0
-- Not in the paper
synReft γ r@(Pop pop r1 r2) = do
  (tp1, r1') <- synReft γ r1
  case tp1 of
    ArrType {} -> Left . SynErr $ "Proof combinators on higher-order values is not defined, in the type synthesis of" <+> pPrint r
    RefType x a reft1
      | isUnitRefType tp1 -> do
          (tp2, r2') <- synReft γ r2
          return (tp2, Pop pop r1' r2')
      | otherwise -> do
          let xvar = Var x 0 Local
              reft2 = Bop And reft1 (Bop (popToBop pop) xvar (mkProj r1'))
          r2' <- checkReft γ r2 (RefType x a reft2)
          let reft3' = Bop And reft1 (Bop Eq xvar (mkProj r2'))
              reft3 = case pop of PEq -> Bop And reft3' (Bop Eq xvar (mkProj r1')); _ -> reft3'
          return (RefType x a reft3, Pop pop r1' r2')
synReft _ (Sub {}) = error "Constructor Sub found before elaboration"
synReft _ (Inj {}) = error "Constructor Inj found before elaboration"
synReft _ (Proj {}) = error "Constructor Proj found before elaboration"

-- * Type checking of expressions

-- | Type checking for refinements, always by subtyping
checkReft :: TypEnv -> Reft -> RefType -> Either TypeError Reft
checkReft γ r tp = do
  (tp_r, r') <- synReft γ r
  if isSubtype tp_r tp
    then return (mkSub r' tp_r tp)
    else Left . SubtypingErr $ "Synthesized type" <+> pPrint tp_r <+> "for" <+> pPrint r <+> "is not a subtype of type" <+> pPrint tp

checkExpr :: TypEnv -> [DesState] -> Expr -> RefType -> Either TypeError Expr
-- checkExpr _ _ e tp | traceFunc "checkExpr" [pPrint e, pPrint tp] = undefined
-- (C-Syn)
checkExpr γ _ (Reft r) tp = Reft <$> checkReft γ r tp
-- (C-Let)
checkExpr γ state (Let x (Just tpx) ex e) tp = do
  _ <- wfRefType γ tp -- check that tp does not depend on x
  tpx' <- wfRefType γ tpx
  let (args, ret) = second mkRefType $ arrs tpx'
  let γx = insertLocalVars args γ
  ex' <- checkExpr γx state ex ret
  let γ' = insertLocalVar (x, tpx') γ
  e' <- checkExpr γ' state e tp
  return (Let x (Just tpx') ex' e')
-- Not in the paper, but in case we have no annotation
checkExpr γ state (Let x Nothing (Reft r) e) tp = do
  _ <- wfRefType γ tp -- check that tp does not depend on x
  (tpr, r') <- synReft γ r
  let γ' = insertLocalVar (x, tpr) γ
  e' <- checkExpr γ' state e tp
  return (Let x (Just tpr) (Reft r') e')
checkExpr _ _ e@(Let {}) _ = Left . CheckingErr $ "Type annotation expected for the let-binding" <+> pPrint e
-- (C-Case)
checkExpr γ state e0@(Case r branches _) tp = do
  (tpr, r') <- synReft γ r
  case tpr of
    RefType _ (TC _) _ -> do
      (branches', indVars) <- second Set.unions <$> mapAndUnzipM (checkBranch r') branches
      let -- In an induct, we generalize the other parameters that have not been destructed already
          -- the set indVars being non empty tells us that we use induction rather than destruct
          genVars = if Set.null indVars then Nothing else Just $ reverse [z | (Param z _) <- state']
      -- We still need to instantiate the booleans indicating what are the
      -- variables introducing induction hypotheses.
      -- We do this here instead of in checkBranch because it depends on
      -- whether we translate to induction or destruct, which we only know now
      branches'' <- if Set.null indVars then return branches' else mapM instantiateAllIndVars branches'
      return (Case r' branches'' genVars)
    _ -> Left . CheckingErr $ "Matched term is not of an inductive type in expression" <+> pPrint e0
  where
    -- if we match on a parameter x, matchedParamAndPos contains the name x and
    -- the position of the parameter
    matchedParamAndPos =
      case r of
        Var x _ _ -> (x,) <$> elemIndex (Param x 0) state
        _ -> Nothing
    -- state where x is replaced by Destructed
    state' =
      let updateState (_, pos) = take pos state ++ Destructed : drop (pos + 1) state
       in maybe state updateState matchedParamAndPos

    -- Returns the elaborated branch and a boolean to indicate if a subterm uses
    -- an induction hypothesis one of the introduced variables
    checkBranch :: Reft -> ((Id, [(Id, Bool)]), Maybe Expr) -> Either TypeError (((Id, [(Id, Bool)]), Maybe Expr), Set Id)
    -- TODO: we should not use a variable name to translate from Core, we should not have this case
    checkBranch _ (c, Just (Reft (Var "undefined" _ _))) = return ((c, Nothing), Set.empty)
    checkBranch _ (c, Nothing) = return ((c, Nothing), Set.empty)
    checkBranch matched ((c, ys), Just e) = do
      tpc <- lookupDC c γ
      -- Replace the binders in tpc by the names of the match in ys
      let tpcRenamed = renameParams (map fst ys) tpc
          (argsc, (_, tc, _)) = arrs tpcRenamed
          -- Variables of ys that are of type tc and can thus be used for induction
          potentialInductives = concatMap (\case (xi, RefType _ tc' _) | tc' == tc && isJust matchedParamAndPos -> [xi]; _ -> []) argsc
          -- We look for applications where one of the potentialInductives can be
          -- used as inductive variable and instantiate the head of those applications
          (e', indVars) = instRec potentialInductives e
          -- We remove projections from the types of the variables
          -- introduced by the patterns, as these are considered unrefined
          γ' = insertLocalVars (map (second removeFOArgProjs) argsc) $ case matched of
            -- if we match on a variable xMatch, we replace the variable in the context
            -- by the variables introduced by the pattern
            -- and we substitute all occurences of xMatch by the pattern
            Inj (Var xMatch 0 Local) _ ->
              let pat = foldl App (DC c) (map (mkVar . fst) ys)
               in substInEnv pat xMatch $ Env.delete xMatch γ
            -- If we match on an application or a constant, we keep the same context:
            -- in particular, we do not add an equality between the matched term and the pattern:
            -- this equality is useful for occurence typing when checking the VC, but will never appear in elaboration
            _ -> γ
      e'' <- checkExpr γ' state' e' tp
      return (((c, ys), Just e''), indVars)
      where
        -- Given a list of potential inductive variables `inds` introduced by the
        -- pattern matching, instantiate relevant recursive calls using those variable as basis for induction.
        -- Returns the instantiated term and the set of variables that are used for an induction

        instRec :: [Id] -> Expr -> (Expr, Set Id)
        instRec [] tm = (tm, Set.empty)
        instRec inds (Reft tm) = first Reft $ instRecReft inds tm
        instRec inds (Let x tpx ex e') =
          let (tpx', indVars1) = case tpx of
                Just tpx0 -> first Just $ instRecRefType inds tpx0
                Nothing -> (Nothing, Set.empty)
              (ex', indVars2) = instRec inds ex
              (e'', indVars3) = instRec (delete x inds) e'
           in (Let x tpx' ex' e'', Set.unions [indVars1, indVars2, indVars3])
        instRec inds (Case tm alts genVars) =
          let (tm', indVars0) = instRecReft inds tm
              (alts', indVars) = unzip $ map instRecBranch alts
           in (Case tm' alts' genVars, Set.unions (indVars0 : indVars))
          where
            instRecBranch :: ((Id, [(Id, Bool)]), Maybe Expr) -> (((Id, [(Id, Bool)]), Maybe Expr), Set Id)
            instRecBranch br@(_, Nothing) = (br, Set.empty)
            instRecBranch ((c', ys'), Just ebr) =
              let (ebr', indVars) = instRec (inds \\ map fst ys') ebr
               in (((c', ys'), Just ebr'), indVars)

        instRecRefType :: [Id] -> RefType -> (RefType, Set Id)
        instRecRefType [] tp' = (tp', Set.empty)
        instRecRefType inds (RefType x a reft) =
          first (RefType x a) $ instRecReft inds reft
        instRecRefType inds (ArrType x tpx tp') =
          let (tpx', indVars1) = instRecRefType inds tpx
              (tp'', indVars2) = instRecRefType (delete x inds) tp'
           in (ArrType x tpx' tp'', indVars1 `Set.union` indVars2)

        -- NOTE: we should be able to check that the recursive call is supported: for
        -- this, the arguments at the Destructed positions must be equal to what is in the IH
        instRecReft :: [Id] -> Reft -> (Reft, Set Id)
        instRecReft inds tm = case tm of
          (Var {}; StringLit _; IntLit _; FloatLit _; DC _) -> (tm, Set.empty)
          App {} ->
            let (hd, args) = apps tm
                res hd' indVars =
                  let (args', indVarsArgs) = unzip $ map (instRecReft inds) args
                   in (foldl App hd' args', Set.unions (indVars : indVarsArgs))
             in case hd of
                  Var x ar loc -> case (loc, lookupVar x γ) of
                    -- the variable is already instantiated as recursive with inductive variable and state
                    (Recursive {}, _) -> res hd Set.empty
                    -- the variable must be instantiated as recursive
                    (_, Right (Recursive {}, _)) ->
                      case findInductiveVar inds args of
                        Just indVar -> res (Var x ar (Recursive indVar state')) (Set.singleton indVar)
                        -- we only elaborate a variable to Recursive once we found an inductive variable
                        Nothing -> res hd Set.empty
                    _ -> res hd Set.empty
                  _ -> res hd Set.empty
          Bop bop r1 r2 ->
            let (r1', indVars1) = instRecReft inds r1
                (r2', indVars2) = instRecReft inds r2
             in (Bop bop r1' r2', indVars1 `Set.union` indVars2)
          Neg r' -> first Neg $ instRecReft inds r'
          QMark r' rh rp ->
            let (r'', indVars1) = instRecReft inds r'
                (rh', indVars2) = instRecReft inds rh
                (rp', indVars3) = instRecReft inds rp
             in (QMark r'' rh' rp', Set.unions [indVars1, indVars2, indVars3])
          Pop pop r1 r2 ->
            let (r1', indVars1) = instRecReft inds r1
                (r2', indVars2) = instRecReft inds r2
             in (Pop pop r1' r2', indVars1 `Set.union` indVars2)
          Sub r' from to ->
            let (r'', indVars1) = instRecReft inds r'
                (from', indVars2) = instRecRefType inds from
                (to', indVars3) = instRecRefType inds to
             in (Sub r'' from' to', Set.unions [indVars1, indVars2, indVars3])
          Inj r' tp' ->
            let (r'', indVars1) = instRecReft inds r'
                (tp'', indVars2) = instRecRefType inds tp'
             in (Inj r'' tp'', indVars1 `Set.union` indVars2)
          Proj r' -> first Proj $ instRecReft inds r'

        -- Given the potential inductive variables `inds` and a list of arguments,
        -- return Just y if y is both in `inds` and the ith argument, where i is the
        -- position of the parameter being matched on
        findInductiveVar :: [Id] -> [Reft] -> Maybe Id
        findInductiveVar inds args =
          -- Position of the parameter being matched on
          let pos = snd $ fromJust matchedParamAndPos
           in case stripCasts <$> (args !? pos) of
                Just (Var y _ _) | y `elem` inds -> Just y
                _ -> Nothing
          where
            stripCasts (Sub tm _ _) = stripCasts tm
            stripCasts (Inj tm _) = stripCasts tm
            stripCasts tm = tm

    -- TODO: think about whether it might be better to just put a type annotation for C
    -- and deal with that directly in the translation

    -- Instantiate the booleans on the introduced variable with True if the
    -- variable is possibly inductive (but not necessarily used)
    instantiateAllIndVars :: ((Id, [(Id, Bool)]), Maybe Expr) -> Either TypeError ((Id, [(Id, Bool)]), Maybe Expr)
    instantiateAllIndVars ((c, ys), e) = do
      tpc <- lookupDC c γ
      let (argsc, (_, tc, _)) = arrs tpc
          inductives = map (\case (_, RefType _ tc' _) -> tc' == tc; (_, ArrType {}) -> False) argsc
          ys' = zip (map fst ys) inductives
      return ((c, ys'), e)
