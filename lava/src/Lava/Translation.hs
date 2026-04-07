{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OrPatterns #-}

{- HLINT ignore "Use section" -}

-- | This module contains the main functions of the translation.
-- Unrefined and refined translations are mutually dependent, so they are all in the same file
module Lava.Translation where

import Data.Bifunctor (bimap, second)
import Debug.Trace (trace)
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
  let (argsUT, retUT) = bimap (map (utrRefType . snd)) utrRefType $ arrs tp
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
utrReft :: LH.Reft -> Coq.CoqTerm
-- utrReft r | traceFunc "utrReft" [pPrint r] = undefined
utrReft r0 = case r0 of
  LH.Var x n Global | n > 0 -> Coq.Var $ upackInstanceName x
  LH.Var x _ _ -> Coq.Var x
  LH.StringLit s -> Coq.StringLiteral s
  LH.IntLit n -> Coq.IntLiteral n
  LH.FloatLit d -> Coq.FloatLiteral d
  LH.DC c -> Coq.Cr $ utrDC c
  LH.App r1 r2 -> Coq.App (utrReft r1) [utrReft r2]
  LH.Neg r -> Coq.App (Coq.Def Coq.negb) [utrReft r]
  LH.Bop op r1 r2 -> Coq.Bop (trBop op) (utrReft r1) (utrReft r2)
  LH.QMark r _ _ -> utrReft r
  LH.Pop _ _ r -> utrReft r
  LH.Sub r _ _ -> utrReft r
  LH.Inj r _ -> utrReft r
  LH.Proj r -> Project $ trReft r

-- | Translation of refinements to propositions
--   Function RtoP (def 3.4) of the paper
utrReftProp :: LH.Reft -> Coq.CoqTerm
-- utrReftProp r | traceFunc "utrReftProp" [pPrint r] = undefined
utrReftProp r =
  let (rv, r') = extractApps r
   in hypsRV rv True (mkIsTrue (utrReft r'))

-- ** Utility functions for unrefined translations

-- | List of operators for which we use a graph relation in Rocq,
-- with the associated name.
-- In the paper, this is everything except = and ≠
operatorsWithGraph :: [(LH.Bop, Reft)]
operatorsWithGraph =
  [ (LH.Plus, LH.Var "addZ" 2 Global),
    (LH.Minus, LH.Var "subZ" 2 Global),
    (LH.Times, LH.Var "multZ" 2 Global),
    (LH.Div, LH.Var "divZ" 2 Global),
    (LH.Mod, LH.Var "modZ" 2 Global)
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
      -- top-level constant
      LH.Var _ 0 Global -> updateEnv env r
      (LH.Var {}; StringLit {}; FloatLit {}; IntLit {}; DC {}) -> (env, r)
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
        (LH.Var {}; Proj (LH.Var {})) -> extractApp
        _ -> error . render $ text "LH application" <+> pPrint r <+> text "not starting with an identifier."
        where
          (hd, args) = apps r
          extractInAppArgs =
            let (env', args') = foldr seqNames (env, []) args
             in (env', foldl LH.App hd args')
          extractApp = uncurry updateEnv extractInAppArgs
          -- apply the function on a list of arguments
          seqNames arg (curEnv, curArgs) = second (: curArgs) $ go curEnv arg
      -- We do not extract applications of the subterms we will erase in QMark and Pop
      QMark r' rh rp -> second (\r'' -> QMark r'' rh rp) $ go env r'
      Pop pop r1 r2 -> second (Pop pop r1) $ go env r2
      Inj r' tp -> second (`Inj` tp) $ go env r'
      Sub r' from to -> second (\r'' -> Sub r'' from to) $ go env r'
      Proj r' -> second Proj $ go env r'
      where
        -- If r is in env, returns its associated variable,
        -- otherwise creates a fresh variable, update env and returns the variable
        updateEnv env' r' = case lookup r' env' of
          Just z -> (env', LH.Var z 0 Local)
          Nothing -> let z = freshName "z" env' in (env' ++ [(r', z)], LH.Var z 0 Local)
        freshName f zs =
          -- Number of calls to f
          let nbOfCalls = foldr ((+) . isF) 0 zs
           in if nbOfCalls == 0
                then f ++ "res"
                else f ++ "_res_" ++ show (nbOfCalls + 1)
          where
            isF :: (Reft, Id) -> Int
            isF (LH.App (LH.Var f' _ _) _, _) | f' == f = 1
            isF _ = 0

-- | Takes as first argument the map RV from applications to fresh variables and
-- translates the hypothesis, placing them on top of the second argument
-- The flag indicates if we want to use foralls and implications or exists with conjunctions.
-- The first case is for building the graph relation, the second the backward reasoning lemmas
hypsRV :: [(Reft, Id)] -> Bool -> CoqTerm -> CoqTerm
hypsRV rv graphRel = \p -> foldr hyp p rv
  where
    -- hyp(f r1 … rn, z) p = forall z, (f_rel/get(U)PackRelName f) RtoU(r1) … RtoU(rn) z -> p
    hyp :: (Reft, Id) -> CoqTerm -> CoqTerm
    hyp (app, z) p =
      quantifier [(z, Hole)] $
        link (Coq.App hdT (map utrReft args ++ [Coq.Var z])) p
      where
        (quantifier, link) =
          if graphRel then (Forall, Coq.Impl) else (Exists, Coq.And)
        (hd, args) = apps app
        hdT = case hd of
          -- f -> f_rel for global FO/HO variables (includes operators in `operatorsWithGraph`)
          LH.Var f _ Global -> Coq.Def $ relDefName f
          -- f -> getUPackRelName f for local HO variables
          LH.Var f n Local | n > 0 -> upackGetRel (Coq.Def f)
          -- TODO: this is not correct, but is a placeholder that does not
          -- prevent translation since this only appears in places that are not
          -- printed in Rocq (inside casts) or inside specifications, but no
          -- specifications uses the name of the function being defined
          LH.Var f _ (Recursive {}) -> Coq.Def $ relDefName f
          -- proj f -> getPackRelName f for local HO variables
          Proj (LH.Var f n _) | n > 0 -> packGetRel (Coq.Def f)
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
trRefType :: LH.RefType -> RocqType
-- trRefType tp@(RefType {}) | traceFunc "trRefType" [pPrint tp] = undefined
trRefType (RefType x tp r) =
  Coq.Subset x (trBaseType tp) rT
  where
    rT = case tp of
      (LH.Builtin {}) -> utrReftProp r
      _ | tp `elem` builtinTCs -> utrReftProp r
      (LH.TC tc) -> Coq.And (Coq.App (Def $ wfTCName tc) [Coq.Var x]) (utrReftProp r)
trRefType tp@(ArrType {}) =
  Pack argTps uargTps (argListCorPrf argTps uargTps) tpx p_
  where
    {- substs = map (\(w, _) -> (removeSuffix "_r" w, projectTm $ Var w)) args_
       cleanupSubst substs_ = subst substs_
       args = map (\(x, xTp) -> (x, cleanupSubst (filter (\(y, _) -> x /= y) substs) xTp)) args_
       tpx = cleanupSubst substs tpx_
       rx = subst substs rx_ -}
    (args, ret) = arrs tp
    (x, tpx, rx) = fromSubset $ trRefType ret
    argsT = map (second utrRefType) args
    argTps = ArgListT argsT
    uargTps = UArgListT $ map (utrRefType . snd) args
    p = mkLam argsT (Lambda x tpx rx)
    argsNm = "x_" ++ hashName argTps
    v = "v_" ++ argsNm
    p_ = Lambda argsNm (ArgumentList argTps) (Lambda v tpx (PrfTerm Hole (ByTac . Custom $ unwords ["flattenP", prettyShow p, argsNm, v])))

-- | Translation of refinement types at top-level (with foralls)
trRefTypeTop :: LH.RefType -> RocqType
trRefTypeTop tp@(RefType {}) = trRefType tp
trRefTypeTop (ArrType x tpx tp) = Coq.FAType (x, trRefType tpx) (trRefTypeTop tp)

-- | Translation of a refinement type to an arrow where first-order arguments
-- are splitted over the value and predicate
--
-- > trRefTypeSplitFOArgs (x: {x:Int | x > 0}) -> (f: Int -> Int) -> {v: Int | v = proj(f) proj(x))
-- >   = ([(x: Z) (x_p: geq_rel x 0 true) (f: Pack(Int -> Int))], {v: Z | (getPackRel f) x v})
trRefTypeSplit :: LH.RefType -> ([(Id, RocqType)], RocqType)
trRefTypeSplit tp =
  let (args, ret) = arrs . removeFOArgProjs $ harmonizeBinderNames tp
   in (concatMap (splitIfFO . second trRefType) args, trRefType ret)
  where
    splitIfFO (x, Subset _ tpx p) = [(x, tpx), (subsetWitnessNm x, Prop p)]
    splitIfFO argT = [argT]

-- | Translation of refinements
--   Function RtoR (def 3.8) of the paper
trReft :: LH.Reft -> Coq.CoqTerm
trReft (LH.Var x ar Global) | ar > 0 = Coq.Def $ packInstanceName x
trReft (LH.Var x _ _) = Coq.Var x
trReft (LH.StringLit s) = Coq.StringLiteral s
trReft (LH.IntLit n) = Coq.IntLiteral n
trReft (LH.FloatLit d) = Coq.FloatLiteral d
trReft (LH.DC c) = Cr (trDC c)
trReft (LH.Neg tm) = Coq.App (Coq.Def Coq.negB) [trReft tm]
trReft (LH.Bop op tm1 tm2) = Coq.Bop (trBop op) (trReft tm1) (trReft tm2)
trReft (LH.QMark tm hint prop) =
  Coq.Let "_" (Just . Prop $ utrReftProp prop) (Proj2sig $ trReft hint) (trReft tm)
trReft (LH.Pop pop tm1 tm2) =
  let popProp = Just . Prop $ Coq.Bop (trBop $ popToBop pop) (Project $ trReft tm1) (Project $ trReft tm2)
   in Coq.Let "_" popProp (PrfTerm Hole $ ProofHole Nothing) (trReft tm2)
trReft (LH.Sub tm from to) = Coq.SubCast (trRefType to) (trRefType from) (trReft tm) (Coq.ProofHole Nothing)
trReft (LH.Inj tm tp) = mkExist (trRefType tp) (trReft tm)
trReft tm@(LH.Proj _) = error $ "Projection " ++ prettyShow tm ++ " found outside of type refinements in Translation.trReft"
trReft tm@(LH.App {}) = case apps tm of
  (LH.Var _ _ (Recursive indVar pats), args) ->
    trRecCall indVar pats args
  (LH.Var f n Local, args)
    | n > 0 ->
        Coq.App (packGetF (Coq.Var f)) (map trReft args)
  (hd, args) -> Coq.App (trReft hd) (map trReft args)

-- | Translation of expressions as tactics
-- Some other cases might be necessary because of branches coming from Core.
-- Function EtoTac (def 3.7) of the paper
trExprTacs :: LH.Expr -> [Tactic]
-- trExprTacs e | traceFunc "trExprTacs" [pPrint e] = undefined
trExprTacs (LH.Reft tm) = [Coq.Exact $ trReft tm]
trExprTacs (LH.Let _ Nothing _ _) = error "Found let-binding with annotation while translating."
trExprTacs (LH.Let x (Just tpx@(RefType {})) e1 e2) =
  [ AssertTacs x' (trRefType tpx) (trExprTacs e1),
    DestructConj x' x (subsetWitnessNm x)
  ]
    ++ trExprTacs e2
  where
    x' = x ++ "'"
trExprTacs (LH.Let x (Just tpx@(ArrType {})) e1 e2) =
  [ AssertTacs x' (trRefTypeTop tpx) (intros : trExprTacs e1),
    assertF
  ]
    ++ trExprTacs e2
  where
    (args, _) = arrs tpx
    intros = Intros $ map (\(xi, _) -> DestrPat $ ConjDestrPat [SingleIdPat xi, SingleIdPat $ subsetWitnessNm xi]) args
    tpxT = trRefTypeTop tpx
    x' = "f_" ++ hashName tpxT
    assertF = Custom $ "unshelve refine (let " ++ x ++ " : ltac:(buildPackG_spec " ++ x' ++ ") := (ltac:(fun_to_pack " ++ x' ++ ")) in _)"
trExprTacs (Case tm alts genVars) =
  let -- translation of an unreachable branch as intros; exfalso; oracle.
      trAltBody Nothing = [mkConcat [Intros [], Exfalso, Oracle]]
      trAltBody (Just e) = trExprTacs e
   in [mkMatching trAltBody tm alts genVars]

-- | Translation of a case expression as destruct or as induct
-- An induct such that none of the introduced IHs are used is transformed to destruct
-- This function is factorized by the function to apply to the branches,
-- in particular in the translation of a function we use trExprTacs
mkMatching :: (Maybe Expr -> [Tactic]) -> Reft -> [((Id, [(Id, Bool)]), Maybe Expr)] -> [Id] -> Tactic
-- mkMatching _ tm alts genVars | traceFunc "mkMatching" [pPrint tm, pPrint alts, pPrint genVars] = undefined
mkMatching trans tm alts genVars =
  if induct
    then Induction (Project $ trReft tm) (map trAlt alts) genVars
    else Coq.Destruct (Project $ trReft tm) (map trAlt alts)
  where
    -- Compute what variables will be actually used for later inductions
    indVars = map indVarsAlt alts
    indVarsAlt ((_, ys), e) = map fst $ filter (\(y, isInd) -> isInd && y `isIndVar` e) ys
    -- Whether y is used as an inductive variable, by checking the
    -- information contained in the localization of the recursive variables
    isIndVar y (Just e) = any (\case (_, (_, Recursive y' _)) -> y == y'; _ -> False) (freeVarsArLoc e)
    isIndVar _ Nothing = False
    -- If an induction hypothesis is used, we translate to induct
    induct = not (all null indVars)
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
          let ihy = if y `isIndVar` e then SingleIdPat $ ihName y else UnnamedIdPat
           in SingleIdPat y : [ihy | isInd, induct]

-- ** Utility functions for the refined translation

-- | Given an inductive variable y, the branch pattern and arguments,
-- build an application of IHy to the arguments
trRecCall :: Id -> BranchPattern -> [Reft] -> CoqTerm
trRecCall indVar pats args =
  let argsAndPats = zip args (map apps pats)
      -- ltac:(try clear ihHyp; solver)
      oracleTac = Coq.PrfTerm Coq.Hole $ Coq.ProofHole (Just $ ihName indVar)
      -- Translation of the arguments:
      -- We translate only arguments in positions of parameters that
      -- have not been destructed, the only ones that are not already instantiated.
      -- A higher-order argument is translated directly with RtoR;
      -- we recognize it with its pattern, necessarily intact and
      -- contains the arity.
      -- A first-order argument must be decomposed into its first
      -- projection and the witness, for which we use ltac:(oracle)
      trArg (ri, (LH.Var _ n _, _)) =
        if n > 0 then [trReft ri] else [Coq.Project $ trReft ri, oracleTac]
      trArg _ = []
      -- The number of parameters that have been destructed gives us
      -- the number of ltac:(oracle) we need for the induction
      -- hypothesis, this includes one for the induction variable itself
      nbOracles = length [ri | (ri, (LH.DC _, _)) <- argsAndPats]
      argsT = replicate nbOracles oracleTac ++ concatMap trArg argsAndPats
   in Coq.App (Coq.Var $ ihName indVar) argsT
