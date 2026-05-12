{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE TupleSections #-}

{- HLINT ignore "Use section" -}

-- | This module contains the main functions of the translation.
-- Unrefined and refined translations are mutually dependent, so they are all in the same file
module Lava.Translation where

import Data.Bifunctor (bimap, second)
-- import Debug.Trace (trace)

import Data.Maybe (fromMaybe)
import Lava.Calculus as LH
import Lava.Coq as Coq
import Lava.CoqSyntaxUtil
import Lava.Names
import Text.PrettyPrint.HughesPJClass as PP

-- * Generic translations

-- | Translation of builtins
trBuiltin :: LH.Builtin -> Coq.Builtin
trBuiltin Integer = Coq.CTInt
trBuiltin Double = error "Doubles not yet supported in Coq (function Translation.trBuiltin)"
trBuiltin String = error "Strings not yet supported in Coq (function Translation.trBuiltin)"

-- | Translation of base types
trBaseType :: LH.BaseType -> RocqType
trBaseType (LH.Builtin b) = Coq.Builtin $ trBuiltin b
trBaseType (LH.TC tc) = Coq.TC tc' []
  where
    tc' = case tc of
      _ | tc == boolTpName -> "bool"
      _ | tc == unitTpName -> "Unit"
      _ -> unrefinedTCName tc

-- | Translation of ILH binary operators to Coq binary operators
trBop :: LH.Bop -> Coq.BaseBop
trBop LH.Plus = Coq.Plus
trBop LH.Minus = Coq.Minus
trBop LH.Times = Coq.Times
trBop LH.Div = Coq.Div
trBop LH.Mod = Coq.Mod
trBop LH.Eq = Coq.Eq
trBop LH.Neq = Coq.Neq
trBop LH.Leq = Coq.Leq
trBop LH.Geq = Coq.Geq
trBop LH.Lt = Coq.Lt
trBop LH.Gt = Coq.Gt
trBop LH.And = Coq.And
trBop LH.Or = Coq.Or
trBop LH.Impl = Coq.Impl
trBop LH.Iff = Coq.Equiv

-- * Unrefined translations

-- ** Main functions

-- | Translation of datatypes
utrDC :: Id -> Id
utrDC c | c == LH.unitTmName = Coq.unitTmName
utrDC c | c == LH.ttTmName = Coq.btrueTmName
utrDC c | c == LH.ffTmName = Coq.bfalseTmName
utrDC c = unrefinedConstrName c

-- | Translation of refinement types
--   Function TtoU (def 3.1) of the paper
utrRefType :: LH.RefType -> RocqType
utrRefType (RefType _ tp _) = trBaseType tp
utrRefType tp@(ArrType {}) =
  let (argsUT, retUT) = bimap (map (utrRefType . snd)) (utrRefType . mkRefType) $ arrs tp
   in UPack (UArgListT argsUT) retUT

-- | Translation of refinement types at top-level (with arrows)
utrRefTypeTop :: LH.RefType -> RocqType
utrRefTypeTop tp@(RefType {}) = utrRefType tp
utrRefTypeTop (ArrType _ tpx tp) = Coq.Arrow (utrRefType tpx) (utrRefTypeTop tp)

-- | Translation of refinement types at top level (with arrows and Prop at the end)
utrRefTypeTopProp :: LH.RefType -> RocqType
utrRefTypeTopProp tp@(RefType {}) = Arrow (utrRefType tp) (Coq.Sort Coq.PropSort)
utrRefTypeTopProp (ArrType _ tpx tp) = Coq.Arrow (utrRefType tpx) (utrRefTypeTopProp tp)

-- | Translation of refinements
--   Function RtoU (def 3.2) of the paper
utrReft :: Bool -> LH.Reft -> Coq.CoqTerm
-- utrReft r | traceFunc "utrReft" [pPrint r] = undefined
utrReft eq r0 = case r0 of
  -- global function -> f_pack
  LH.Var x (Just _) Global -> Coq.Var $ upackInstanceName x
  -- global constant -> proj1_sig f
  LH.Var x Nothing Global -> Coq.Proj Sig1 (Coq.Def x)
  -- local or recursive variable -> x
  LH.Var x _ _ -> Coq.Var x
  LH.StringLit s -> Coq.StringLiteral s
  LH.IntLit n -> Coq.IntLiteral n
  LH.FloatLit d -> Coq.FloatLiteral d
  LH.DC c -> Coq.Cr $ utrDC c
  LH.App r1 r2 -> Coq.App (utrReft eq r1) [utrReft eq r2]
  LH.Neg r -> Coq.Neg UnrefOp $ utrReft eq r
  LH.Bop op r1 r2 ->
    if op `elem` [LH.And, LH.Or, LH.Impl, LH.Iff] && not (isValue r1) && not (isValue r2)
      then error $ "Refinement " ++ prettyShow r0 ++ "cannot be translated to a boolean type because of the presence of applications."
      else Coq.Bop (Binop (trBop op) UnrefOp) (utrReft eq r1) (utrReft eq r2)
  LH.QMark r _ _ -> utrReft eq r
  LH.Pop _ _ r -> utrReft eq r
  LH.Sub r _ _ -> utrReft eq r
  LH.Inj r _ -> utrReft eq r
  LH.Proj r -> Coq.mkProj GenProj $ trReft eq r

-- | Translation of refinements to propositions
--   Function RtoP (def 3.4) of the paper
utrReftProp :: Bool -> LH.Reft -> Coq.CoqTerm
-- utrReftProp r | traceFunc "utrReftProp" [pPrint r] = undefined
-- TODO: add inlining optimization (maybe in mkIsTrue)
{- utrReftProp eq (LH.Bop LH.Eq r1 r2) = -}
-- Applying the extraction on both sides of logical connectives
-- is necessary for the correct scoping of existentials
utrReftProp eq (LH.Bop bop r1 r2)
  | bop `elem` [LH.And, LH.Or, LH.Impl, LH.Iff] =
      Coq.Bop (Binop (trBop bop) PropOp) (utrReftProp eq r1) (utrReftProp eq r2)
utrReftProp eq r =
  let (rv, r') = extractApps r
   in hypsRV eq rv False (mkIsTrue (utrReft eq r'))

-- ** Utility functions for unrefined translations

-- | List of operators for which we use a graph relation in Rocq,
-- with the associated name.
-- In the paper, this is everything except = and ≠
operatorsWithGraph :: [(LH.Bop, Reft)]
operatorsWithGraph =
  [ (LH.Plus, LH.Var "addZ" (Just (LH.Builtin Integer)) Global),
    (LH.Minus, LH.Var "subZ" (Just (LH.Builtin Integer)) Global),
    (LH.Times, LH.Var "multZ" (Just (LH.Builtin Integer)) Global),
    (LH.Div, LH.Var "divZ" (Just (LH.Builtin Integer)) Global),
    (LH.Mod, LH.Var "modZ" (Just (LH.Builtin Integer)) Global)
  ]

-- | Returns an association of each application in the input to a fresh variable and the term where replacements of the applications by the associated variable have been done.
-- In the list associating terms to variables, the replacements have also been done.
-- For operators, we only extract the ones in the list operatorsWithGraph
-- Ex: extractApps ((f 0 1) + (f 0 1) + x) = ([(f 0 1, f_res)], f_res + f_res + x)
extractApps :: Reft -> ([(Reft, Id)], Reft)
-- extractApps r | traceFunc "extractApps" [pPrint r] = undefined
extractApps r0 = go [] r0
  where
    go :: [(Reft, Id)] -> Reft -> ([(Reft, Id)], Reft)
    go env r = case r of
      (LH.Var {}; StringLit {}; FloatLit {}; IntLit {}; DC {}) -> (env, r)
      -- Inside Proj, we have a refined term, translated as refined and for
      -- which we must therefore not extract projections
      LH.Proj {} -> (env, r)
      LH.Neg r' -> second LH.Neg $ go env r'
      LH.Bop bop r1 r2 ->
        let (env1, r1') = go env r1
            (env2, r2') = go env1 r2
         in case lookup bop operatorsWithGraph of
              Nothing -> (env2, LH.Bop bop r1' r2')
              Just bopVar -> updateEnv env2 (LH.App (LH.App bopVar r1') r2')
      LH.App {} -> case hd of
        -- TODO: in the applications of recursive calls appearing in the refined
        -- definition inside type refinments, we can't use the relation,
        -- but must use either the IH or the function itself
        -- (DC _; LH.Var _ _ (Recursive {})) -> extractInAppArgs
        DC _ -> extractInAppArgs
        (LH.Var {}; LH.Proj (LH.Var {})) -> extractApp
        _ -> error . render $ text "LH application" <+> pPrint r <+> text "not starting with an identifier."
        where
          (hd, args) = apps r
          extractInAppArgs =
            let (env', args') = foldr seqNames (env, []) args
             in (env', foldl LH.App hd args')
          extractApp = uncurry updateEnv extractInAppArgs
          -- apply the function on a list of arguments
          seqNames arg (curEnv, curArgs) = second (: curArgs) $ go curEnv arg
      -- We do not care about extracting applications of the subterms we will erase in QMark and Pop
      QMark r' rh rp -> second (\r'' -> QMark r'' rh rp) $ go env r'
      Pop pop r1 r2 -> second (Pop pop r1) $ go env r2
      Inj r' tp -> second (`Inj` tp) $ go env r'
      Sub r' from to -> second (\r'' -> Sub r'' from to) $ go env r'
      where
        -- If r is in env, returns its associated variable,
        -- otherwise creates a fresh variable, update env and returns the variable
        updateEnv env' r' = case lookup r' env' of
          Just z -> (env', LH.Var z Nothing Local)
          Nothing ->
            let z = freshName (fromMaybe "z" (headVar r')) env'
             in (env' ++ [(r', z)], LH.Var z Nothing Local)
        -- f_res, f_res_2, f_res_3 etc
        freshName f env' =
          let isF r' = case headVar r' of Just f' -> f == f'; Nothing -> False
              nbOfCalls = length $ filter (isF . fst) env'
           in f ++ "_res" ++ (if nbOfCalls == 0 then "" else "_" ++ show (nbOfCalls + 1))

-- | Takes as first argument the map RV from applications to fresh variables and
-- translates the hypothesis, placing them on top of the second argument
-- The flag indicates if we want to use foralls and implications or exists with conjunctions.
-- The first case is for building the graph relation, the second the backward reasoning lemmas and the translation of type refinements
hypsRV :: Bool -> [(Reft, Id)] -> Bool -> CoqTerm -> CoqTerm
hypsRV eq rv graphRel = \p -> foldr hyp p rv
  where
    -- hyp(f r1 … rn, z) p = forall z, (f_rel/get(U)PackRelName f) RtoU(r1) … RtoU(rn) z -> p
    --                    or exists z, (f_rel/get(U)PackRelName f) RtoU(r1) … RtoU(rn) z /\ p
    hyp :: (Reft, Id) -> CoqTerm -> CoqTerm
    hyp (app, z) p =
      quantifier [(z, trBaseType tpz)] $
        link (Coq.App hdT (map (utrReft eq) args ++ [Coq.Var z])) p
      where
        (quantifier, link) =
          if graphRel then (Forall, Coq.Bop (Binop Coq.Impl PropOp)) else (Exists, Coq.Bop (Binop Coq.And PropOp))
        (hd, args) = apps app
        (hdT, tpz) = case hd of
          -- f -> f_rel for global functions (includes operators in `operatorsWithGraph`)
          LH.Var f (Just tp) Global -> (Coq.Def $ relDefName f, tp)
          -- f -> getUPackRelName f for local HO variables
          LH.Var f (Just tp) Local -> (upackGetRel $ Coq.Def f, tp)
          -- TODO: this is not correct, but is a placeholder that does not
          -- prevent translation since this only appears in places that are not
          -- printed in Rocq (inside casts) or inside specifications, but no
          -- specifications uses the name of the function being defined
          LH.Var f (Just tp) (Recursive {}) -> (Coq.Def $ relDefName f, tp)
          -- proj f -> getPackRelName f for local HO variables
          LH.Proj (LH.Var f (Just tp) _) -> (packGetRel (Coq.Def f), tp)
          _ -> error . render $ text "Unexpected extract term" <+> pPrint app <+> text "in Translation.hypsRV."

-- * Refined translations

-- | Translation of datatypes
trDC :: Id -> Id
trDC c | c == LH.unitTmName = Coq.unitTmName
trDC c | c == LH.ttTmName = Coq.btrueTmName
trDC c | c == LH.ffTmName = Coq.bfalseTmName
trDC c = c

-- | Translation of refinement types
--   Function TtoR (def 3.6) of the paper
trRefType :: Bool -> LH.RefType -> RocqType
-- trRefType tp@(RefType {}) | traceFunc "trRefType" [pPrint tp] = undefined
trRefType eq (RefType x tp r) =
  Coq.Subset x (trBaseType tp) rT
  where
    rT = case tp of
      (LH.Builtin {}) -> utrReftProp eq r
      _ | tp `elem` builtinTCs -> utrReftProp eq r
      (LH.TC tc) -> Coq.Bop (Binop Coq.And PropOp) (Coq.App (Def $ wfTCName tc) [Coq.Var x]) (utrReftProp eq r)
-- TODO: I think if we have an arrtype of a unit type, we do not translate it to a pack
trRefType eq tp@(ArrType {}) =
  Pack argTps uargTps (argListCorPrf argTps uargTps) tpx p_
  where
    {- substs = map (\(w, _) -> (removeSuffix "_r" w, projectTm $ Var w)) args_
       cleanupSubst substs_ = subst substs_
       args = map (\(x, xTp) -> (x, cleanupSubst (filter (\(y, _) -> x /= y) substs) xTp)) args_
       tpx = cleanupSubst substs tpx_
       rx = subst substs rx_ -}
    (args, ret) = arrs tp
    (x, tpx, rx) = fromSubset . trRefType eq $ mkRefType ret
    argsT = map (second (trRefType eq)) args
    argTps = ArgListT argsT
    uargTps = UArgListT $ map (utrRefType . snd) args
    p = mkLam argsT (Lambda x tpx rx)
    argsNm = "x_" ++ hashName argTps
    v = "v_" ++ argsNm
    p_ = Lambda argsNm (ArgumentList argTps) (Lambda v tpx pBody)
    pBody = PrfTerm Hole (ByTac . Custom $ unwords ["flattenP", render $ parens (pPrint p), argsNm, v])

-- | Translation of refinement types at top-level (with foralls)
trRefTypeTop :: Bool -> LH.RefType -> RocqType
trRefTypeTop eq tp@(RefType {}) = trRefType eq tp
trRefTypeTop eq (ArrType x tpx tp) = Coq.FAType (x, trRefType eq tpx) (trRefTypeTop eq tp)

-- | Translation of a refinement type to an arrow where first-order arguments
-- are splitted over the value and predicate
--
-- > trRefTypeSplitFOArgs (x: {x:Int | x > 0}) -> (f: Int -> Int) -> {v: Int | v = proj(f) proj(x))
-- >   = ([(x: Z) (x_p: geq_rel x 0 true) (f: Pack(Int -> Int))], {v: Z | (getPackRel f) x v})
trRefTypeSplit :: Bool -> LH.RefType -> ([(Id, RocqType)], RocqType)
trRefTypeSplit eq tp =
  let (args, ret) = arrs . removeFOArgProjs $ harmonizeBinderNames tp
   in (concatMap (splitIfFO . second (trRefType eq)) args, trRefType eq $ mkRefType ret)
  where
    splitIfFO (x, Subset _ tpx p) = [(x, tpx), (subsetWitnessNm x, Prop p)]
    splitIfFO argT = [argT]

-- | Translation of refinements
--   Function RtoR (def 3.8) of the paper
trReft :: Bool -> LH.Reft -> Coq.CoqTerm
trReft _ (LH.Var x (Just _) Global) = Coq.Def $ packInstanceName x
trReft _ (LH.Var x _ _) = Coq.Var x
trReft _ (LH.StringLit s) = Coq.StringLiteral s
trReft _ (LH.IntLit n) = Coq.IntLiteral n
trReft _ (LH.FloatLit d) = Coq.FloatLiteral d
trReft _ (LH.DC c) = Cr (trDC c)
trReft eq (LH.Neg tm) = Coq.Neg RefOp $ trReft eq tm
trReft eq (LH.Bop op tm1 tm2) = Coq.Bop (Binop (trBop op) RefOp) (trReft eq tm1) (trReft eq tm2)
trReft _ qmark@(LH.QMark {}) | traceFunc "trReft" [text $ show qmark] = undefined
trReft eq (LH.QMark tm hint prop) =
  Coq.Let "_" (Just . Prop $ utrReftProp eq prop) (Coq.mkProj Sig2 $ trReft eq hint) (trReft eq tm)
trReft _ pop@(LH.Pop {}) | traceFunc "trReft" [text $ show pop] = undefined
trReft eq (LH.Pop pop tm1 tm2) =
  let popProp = Just . Prop $ Coq.Bop (Binop (trBop $ popToBop pop) PropOp) (Coq.mkProj GenProj $ trReft eq tm1) (Coq.mkProj GenProj $ trReft eq tm2)
   in Coq.Let "_" popProp (PrfTerm Hole $ if eq then ProofHole else ByTac Oracle) (trReft eq tm2)
trReft eq (LH.Sub tm from to) = Coq.SubCast (trRefType eq to) (trRefType eq from) (trReft eq tm) (if eq then ProofHole else ByTac Oracle)
trReft eq (LH.Inj tm tp) = mkExist eq (trRefType eq tp) (trReft eq tm)
trReft _ tm@(LH.Proj _) = error $ "Projection " ++ prettyShow tm ++ " found outside of type refinements in Translation.trReft"
-- TODO: we do not use packs for theorems, maybe we need to change that
trReft eq tm@(LH.App {}) = case apps tm of
  -- recursive call
  (LH.Var f _ (Recursive indVar state), args) ->
    trRecCall (if eq then Right f else Left indVar) state args
  -- apply local function
  (LH.Var f _ Local, args) -> Coq.App (packGetF (Coq.Var f)) (map (trReft eq) args)
  -- apply global function
  (LH.Var f _ Global, args) -> Coq.App (Coq.Def f) (map (trReft eq) args)
  -- other cases
  (hd, args) -> Coq.App (trReft eq hd) (map (trReft eq) args)

-- | Translation of expressions as tactics
-- Some other cases might be necessary because of branches coming from Core.
-- Function EtoTac (def 3.7) of the paper
trExprTacs :: Bool -> LH.Expr -> [Tactic]
-- trExprTacs e | traceFunc "trExprTacs" [pPrint e] = undefined
trExprTacs eq (LH.Reft tm) =
  let refine = Refine $ trReft eq tm
   in if eq then [mkConcat [refine, Try Oracle]] else [refine]
trExprTacs _ (LH.Let _ Nothing _ _) = error "Found let-binding with no annotation while translating."
-- TODO: maybe we need to do something special for let-bindings of a value of unit (return) type
trExprTacs eq (LH.Let x (Just tpx@(RefType {})) e1 e2) =
  [ AssertTacs x' (trRefType eq tpx) (trExprTacs eq e1),
    DestructConj x' x (subsetWitnessNm x)
  ]
    ++ trExprTacs eq e2
  where
    x' = x ++ "'"
trExprTacs eq (LH.Let x (Just tpx@(ArrType {})) e1 e2) =
  [ AssertTacs x' (trRefTypeTop eq tpx) (intros : trExprTacs eq e1),
    assertF
  ]
    ++ trExprTacs eq e2
  where
    (args, _) = arrs tpx
    intros = Intros $ map (\(xi, _) -> DestrPat $ ConjDestrPat [SingleIdPat xi, SingleIdPat $ subsetWitnessNm xi]) args
    tpxT = trRefTypeTop eq tpx
    x' = "f_" ++ hashName tpxT
    assertF =
      Custom . render $
        text "unshelve refine"
          <+> (parens . pPrint)
            ( Coq.Let
                x
                (Just . Prop . PrfTerm Hole . ByTac . Custom $ "buildPackG_spec " ++ x')
                (PrfTerm Hole . ByTac . Custom $ funToPackName ++ " " ++ x')
                TermHole
            )
trExprTacs eq (Case tm alts genVars) =
  let -- translation of an unreachable branch as intros; exfalso; oracle.
      trAltBody Nothing = [mkConcat $ [Intros [], Exfalso] ++ [Oracle | not eq]]
      trAltBody (Just e) = trExprTacs eq e
   in [mkMatching eq trAltBody tm alts genVars]

-- | Translation of expressions as a proof term (for Equations)
trExpr :: Bool -> LH.Expr -> CoqTerm
trExpr eq (Reft r) = trReft eq r
trExpr eq (LH.Let x tp ex e) =
  case tp of
    Just (ArrType {}) -> Coq.Let x (trRefType eq <$> tp) (trExpr eq ex) (trExpr eq e)
    Just (RefType {}) -> Coq.LetDes (x, subsetWitnessNm x) (trExpr eq ex) (trExpr eq e)
    Nothing -> error "trExpr: found let-binding without type annotation."
trExpr eq (Case tm alts _) =
  Match [Coq.mkProj Sig1 $ trReft eq tm] Nothing (map trAlt alts)
  where
    trAlt ((c, ys), e) = ([(c, map fst ys)],) $
      case e of
        Just e' -> trExpr eq e'
        Nothing -> PrfTerm Hole $ ByTac Exfalso

-- ** Utility functions for the refined translation

-- | Given an inductive variable y, the branch pattern and arguments,
-- build an application of IHy to the arguments
-- The identifier contains the inductive variable if translating with tactics,
-- and the function name if translating with Equations
trRecCall :: Either Id Id -> [DesState] -> [Reft] -> CoqTerm
-- trRecCall indVar pats args | traceFunc "trRecCall" [text indVar, pPrint pats, pPrint args] = undefined
trRecCall (Left indVar) state args =
  Coq.App (Coq.Var $ ihName indVar) (oracleTac : concatMap trArg (zip args state))
  where
    -- ltac:(try clear ihHyp; solver)
    oracleTac = PrfTerm Hole . ByTac $ Concat [Try (Clear $ ihName indVar), Oracle]
    -- Translation of the arguments:
    -- A higher-order argument is translated directly with RtoR
    trArg (ri, Param _ n) | n > 0 = [trReft False ri]
    -- a first-order argument must be decomposed either
    -- into its first projection and the witness (for which we use ltac:(oracle))
    trArg (ri, Param _ _) = [Coq.mkProj Sig1 $ trReft False ri, oracleTac]
    -- or into nothing if it is at the position of a destructed parameter
    trArg (_, Destructed) = []
trRecCall (Right f) state args =
  Coq.App (Coq.Var $ eqFunctionName f) (concatMap trArg (zip args state))
  where
    -- Translation of the arguments:
    -- higher-order arguments are kept as is
    trArg (ri, Param _ n) | n > 0 = [trReft True ri]
    -- while first-order ones must be decomposed into their first projection and
    -- a hole for the refinement
    trArg (ri, _) = [Coq.mkProj Sig1 $ trReft True ri, TermHole]

-- | Translation of a case expression as destruct or as induct
-- An induct such that none of the introduced IHs are used is transformed to destruct
-- This function is factorized by the function to apply to the branches,
-- in particular in the translation of a function we use trExprTacs
mkMatching :: Bool -> (Maybe Expr -> [Tactic]) -> Reft -> [((Id, [(Id, Bool)]), Maybe Expr)] -> Maybe [Id] -> Tactic
-- mkMatching _ tm alts genVars | traceFunc "mkMatching" [pPrint tm, pPrint alts, pPrint genVars] = undefined
mkMatching eq trans tm alts genVars =
  Coq.Destruct (Coq.mkProj Sig1 $ trReft eq tm) (map trAlt alts) genVars
  where
    -- Translation of the branches using the parametrized function
    trAlt ((c, ys), e) = (c, (ysDesPat ys e, trans e))
    -- Build the patterns for the introduced variables.
    -- The second argument contains the free variables of the translated branch,
    -- to check what induction hypotheses are used
    ysDesPat :: [(Id, Bool)] -> Maybe Expr -> CoqDestrPat
    ysDesPat ys e = ConjDestrPat $ concatMap varPattern ys
      where
        -- For inductive variables, in the pattern we add either the name of the IH if it is used later, or a hole _
        varPattern (y, isInd) =
          let ihy = if isIndVar y then SingleIdPat $ ihName y else UnnamedIdPat
           in SingleIdPat y : [ihy | isInd]
        -- Whether y is used as an inductive variable, by checking the
        -- information contained in the localization of the recursive variables
        isIndVar y = any (\case (_, Recursive y' _) -> y == y'; _ -> False) (freeVarsAnnot e)
