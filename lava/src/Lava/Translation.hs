{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OrPatterns #-}

{- HLINT ignore "Use section" -}

-- | This module contains the main functions of the translation.
-- Unrefined and refined translations are mutually dependent, so they are all in the same file
module Lava.Translation where

import Data.Bifunctor (first, second)
import qualified Data.Set as Set (empty, member)
import Lava.Calculus as LH
import Lava.Coq as Coq
import Lava.CoqSyntaxUtil (mkIsTrue, packGetF, packGetRel, upackGetRel)
import Lava.CoqUtil (funcHoodLemName, ihName, packInstanceName, relDefLemName, relDefName, relDefThmName, relPostfix, toPack, toUPack, upackInstanceName)
import Lava.Util (hashName, isSuffixOf, safeHead)

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

-- * Unrefined translations

-- ** Main functions

-- | Translation of refinement types
--   Function TtoU (def 3.1) of the paper
utrRefType :: LH.RefType -> RocqType
utrRefType (RefType _ tp _) = trBaseType tp
utrRefType tp@(ArrType {}) =
  let (args, ret) = arrs tp
   in toUPack (map (utrRefType . snd) args) (utrRefType ret)

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
utrReft r0 = case r0 of
  LH.Var x n Global | n > 0 -> Coq.Var $ upackInstanceName x
  LH.Var x _ _ -> Coq.Var x
  LH.StringLit s -> Coq.StringLiteral s
  LH.IntLit n -> Coq.IntLiteral n
  LH.FloatLit d -> Coq.FloatLiteral d
  LH.DC c -> Coq.Cr (unrefinedConstrName c)
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
extractApps r = go [] r
  where
    go :: [(Reft, Id)] -> Reft -> ([(Reft, Id)], Reft)
    go env r = case r of
      -- top-level constant
      LH.Var x 0 Global -> updateEnv env r
      (LH.Var {}; StringLit {}; FloatLit {}; IntLit {}; DC {}) -> (env, r)
      LH.Neg r' -> second LH.Neg $ go env r'
      LH.Bop bop r1 r2 ->
        let (env1, r1') = go env r1
            (env2, r2') = go env1 r2
         in case lookup bop operatorsWithGraph of
              Nothing -> (env2, LH.Bop bop r1' r2')
              Just bopVar -> updateEnv env2 (LH.App (LH.App bopVar r1') r2')
      LH.App {} -> case apps r of
        (DC c, args) ->
          let (env', args') = foldr seqNames (env, []) args
           in (env', foldr LH.App (LH.DC c) args')
        -- why is this case necessary?
        (LH.Var f_rel ar loc, args) | relPostfix `isSuffixOf` f_rel -> (env, r)
        (LH.Var f ar loc, args) ->
          let (env', args') = foldr seqNames (env, []) args
              r' = foldr LH.App (LH.Var f ar loc) args'
           in updateEnv env' r'
        (Proj (LH.Var f ar loc), args) ->
          let (env', args') = foldr seqNames (env, []) args
              r' = foldr LH.App (Proj (LH.Var f ar loc)) args'
           in updateEnv env' r'
        _ -> error $ "LH application " ++ show r ++ " not starting with an identifier."
      -- We do not extract applications of the subterms we will erase in QMark and Pop
      QMark r' rh rp -> second (\r'' -> QMark r'' rh rp) $ go env r'
      Pop pop r1 r2 -> second (Pop pop r1) $ go env r2
      Inj r' tp -> second (`Inj` tp) $ go env r'
      Proj r' -> second Proj $ go env r'
      where
        seqNames arg (curEnv, curArgs) = second (: curArgs) $ go curEnv arg
        -- If r is in env, returns its associated variable,
        -- otherwise creates a fresh variable, update env and returns the variable
        updateEnv env r = case lookup r env of
          Just z -> (env, LH.Var z 0 Local)
          Nothing -> let z = fresh z env in (env ++ [(r, z)], LH.Var z 0 Local)
        fresh f zs =
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
hypsRV rv graphRel p = foldr hyp p rv
  where
    -- hyp(f r1 … rn, z) p = forall z, (f_rel/get(U)PackRelName f) RtoU(r1) … RtoU(rn) z -> p
    hyp :: (Reft, Id) -> CoqTerm -> CoqTerm
    hyp (app, z) p =
      quantifier (z, Nothing) $
        link (Coq.App hdT (map utrReft args ++ [Coq.Var z])) p
      where
        (quantifier, link) =
          if graphRel then (FATerm, Coq.Impl) else (ExTerm, Coq.And)
        (hd, args) = apps app
        hdT = case hd of
          -- f -> f_rel for global FO/HO variables (includes operators in `operatorsWithGraph`)
          LH.Var f _ Global -> Coq.Def $ relDefName f
          -- f -> getUPackRelName f for local HO variables
          LH.Var f n Local | n > 0 -> upackGetRel (Coq.Def f)
          -- proj f -> getPackRelName f for local HO variables
          Proj (LH.Var f n _) | n > 0 -> packGetRel (Coq.Def f)
          _ -> error "Unexpected extract term in Translation.hypsRV."

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
trReft tm0 = case tm0 of
  LH.Var x ar Global | ar > 0 -> Coq.Def $ packInstanceName x
  LH.Var x _ _ -> Coq.Var x
  LH.StringLit s -> Coq.StringLiteral s
  LH.IntLit n -> Coq.IntLiteral n
  LH.FloatLit d -> Coq.FloatLiteral d
  LH.DC c -> Cr (trDC c)
  LH.Neg tm -> Coq.App (Coq.Def Coq.negB) [trReft tm]
  LH.Bop op tm1 tm2 -> Coq.Bop (trBop op) (trReft tm1) (trReft tm2)
  LH.QMark tm hint prop ->
    Coq.Let "_" (Just . Prop $ utrReftProp prop) (Proj2sig $ trReft hint) (trReft tm)
  LH.Pop pop tm1 tm2 ->
    let popProp = Just . Prop $ Coq.Bop (trBop $ popToBop pop) (Project $ trReft tm1) (Project $ trReft tm2)
     in Coq.Let "_" popProp (PrfTerm Hole $ ProofHole Nothing) (trReft tm2)
  LH.Sub tm from to -> Coq.SubCast (trRefType to) (trRefType from) (trReft tm) (Coq.ProofHole Nothing)
  LH.Inj tm tp -> Coq.Exist (TypeArg $ trRefType tp) (trReft tm) (Coq.ProofHole Nothing)
  LH.Proj tm -> error $ "Projection " ++ show tm0 ++ " found outside of refinements in Translation.trReft"
  LH.App {} -> case apps tm0 of
    (LH.Var f n (Recursive pats), args) ->
      let argsAndPats = zip args (map apps pats)
          -- The inductive variables are those that appear after a single
          -- destruction of a parameter and that are used as an argument
          -- of the application we are translating in the same position
          -- as the parameter they originate from
          indVarCandidates =
            [ y
            | (LH.Var y _ _, (DC _, ys)) <- argsAndPats,
              -- this enforces that y is obtained after a single
              -- destruction, rather than using freeVars ys
              y `elem` [y' | LH.Var y' _ _ <- ys]
            ]
          -- We arbitrarily choose the first of the candidates to be the
          -- variable we do induction on
          indVar = safeHead indVarCandidates
          ihHyp = case indVar of
            Just x -> Coq.Var $ ihName x
            Nothing -> error $ "No main induction variable in term " ++ show tm0
          -- ltac:(try clear ihHyp; solver)
          oracleTac = Coq.PrfTerm Coq.Hole $ Coq.ProofHole (ihName <$> indVar)
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
          -- hypothesis, one for each of those plus one for the induction variable
          nbOracles = length [ri | (ri, (LH.DC _, _)) <- argsAndPats] + 1
          argsT = replicate nbOracles oracleTac ++ concatMap trArg argsAndPats
       in Coq.App ihHyp argsT
    (LH.Var f n Local, args)
      | n > 0 ->
          Coq.App (packGetF (Coq.Var f)) (map trReft args)
    (hd, args) -> Coq.App (trReft hd) (map trReft args)

-- | Translation of expressions as tactics
-- Some other cases might be necessary because of branches coming from Core.
-- Function EtoTac (def 3.7) of the paper
trExprTacs :: LH.Expr -> [Tactic]
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
    (args, ret) = arrs tpx
    intros = Intros $ map (\(xi, _) -> DestrPat $ ConjDestrPat [SingleIdPat xi, SingleIdPat $ subsetWitnessNm xi]) args
    tpxT = trRefTypeTop tpx
    x' = "f_" ++ hashName tpxT
    assertF = Custom $ "unshelve refine (let " ++ x ++ " : ltac:(buildPackG_spec " ++ x' ++ ") := (ltac:(fun_to_pack " ++ x' ++ ")) in _)"
-- TODO: if we build an induct that does not introduce induction hypotheses,
-- turn it into a destruct
trExprTacs (Case tm alts induct) =
  case induct of
    LH.Destruct -> [Coq.Destruct (Project $ trReft tm) (map trAlt alts)]
    LH.Induct genVars ->
      let gendep = [GeneralizeDependent genVars | not (null genVars)]
          -- we add intros in each branch to degeneralize the variables from genVars
          trAltIntros = second (second (Intros [] :)) . trAlt
       in [Concat $ gendep ++ [Induction (trReft tm) (map trAltIntros alts)]]
  where
    -- translation of an unreachable branch as intros; exfalso; oracle.
    trAlt ((c, ys), Nothing) =
      (c, (ysDesPat ys Set.empty, [Concat [Intros [], Exfalso, Oracle]]))
    trAlt ((c, ys), Just e) =
      let eT = trExprTacs e
       in (c, (ysDesPat ys (Coq.freeVars eT), eT))
    -- Build the patterns for the introduced variables.
    -- The second argument contains the free variables of the translated branch,
    -- to check what induction hypotheses are used
    ysDesPat ys usedIHs = ConjDestrPat $ case induct of
      LH.Destruct -> map (SingleIdPat . fst) ys
      LH.Induct _ -> concatMap varPattern ys
        where
          -- For inductive variables, in the pattern we add either the name of the IH if it is
          -- used later, or a hole _
          varPattern (y, isInd) =
            let ihy = if ihName y `Set.member` usedIHs then SingleIdPat $ ihName y else UnnamedIdPat
             in SingleIdPat y : [ihy | isInd]

{- trExprTacs (LH.Case cond [("False", [], elseE), ("True", [], thenE)]) = do
  let
    condT = utrSmpTerm (fetchFuncts γ) cond
    transBrExpr _ expr = checkTerm γ expr tp (f, mCtx)
  elseET <- transBrExpr Coq.btrue elseE
  thenET <- transBrExpr Coq.btrue thenE
  return [Coq.Destruct condT [("true", (Coq.ConjDestrPat [], thenET)), ("false", (Coq.ConjDestrPat [], elseET))]] -}
-- An if
{- trExprTacs (LH.Let x _ (Reft cond) (LH.Case (LH.Var x' _ _) [("False", [], elseE), ("True", [], thenE)]) | x == x') =  do
  let
    condT = utrSmpTerm (fetchFuncts γ) cond
    transBrExpr _ expr = checkTerm γ expr tp (f, mCtx)
  elseET <- transBrExpr Coq.btrue elseE
  thenET <- transBrExpr Coq.btrue thenE
  return [Coq.Destruct condT [("true", (Coq.ConjDestrPat [], thenET)), ("false", (Coq.ConjDestrPat [], elseET))]] -}
-- A destruct
-- trExprTacs (LH.Let x _ (Reft r) (LH.Case (LH.Var x' _ _) alts)) | x == x' -> trExprTacs γ (Case r (mapThd (sub x r) alts))
