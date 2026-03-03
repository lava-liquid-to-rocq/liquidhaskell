{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

-- | This module contains the functions for the translation of declarations
module Lava.Declaration where

import Data.Bifunctor (bimap, first, second)
import Data.Either (isLeft)
import Data.List ((\\))
import qualified Data.Set as Set
import Lava.Calculus as LH
import Lava.Coq as Coq
import Lava.CoqSyntaxUtil (mkAnd, mkVarDestrPat, mkVarDestruct)
import Lava.CoqUtil
import Lava.Translation
import Lava.TypingEnvironment as TypEnv hiding (map)
import Lava.Util (freshVar)

-- | Main function for the translation of declarations
trDecl :: LH.Decl -> [Coq.Decl]
-- An inductive data type gives an unrefined data type, a well-formedness predicate, some utility definitions and pseudo-constructors
trDecl (LH.Data tc alts) =
  unrefTCDecl tc alts -- Unrefined datatype declaration TC_u
    : tcEqDecls tc alts -- Equality TC_eq for TC_u and associated declarations
    ++ tcRefDecls tc alts -- Well-formedness TC_wf and type alias for TC
    ++ concatMap (mkPseudoConstr tc) alts -- Refined data constructors
    ++ concatMap (mkConstrWf tc) alts -- Lemmas for decomposing well-formedness on data constructors
    ++ tcHints tc alts -- Final hints for datatypes and constructor
    --  For an unreflected definition, we only generate the refined definition,
    -- if the graph relation is needed, we generate it on the fly
trDecl (LH.Definition f tpf e False) = [trDefRefDef f tpf e]
trDecl (LH.Definition f tpf e True) =
  [ trDefRefDef f tpf e, -- f
    trDefGraphRel f tpf e, -- f_rel
    AddHint ConstructorsHint (relDefName f) CoreDB, -- hints for f_rel
    Instance (f ++ "_lookup_rel") ["dictionary", "rel", f] [("lookup'", Coq.Def $ f ++ "_rel")],
    Instance (f ++ "_getF") ["getFunc", relDefName f] [("getF'", Coq.Def f)],
    functionhoodLemma f (argsT, (f_res, retT)), -- f_funct
    AddHint ResolveHint (funcHoodLemName f) GraphRelDB -- hints for f_funct
  ]
    ++ relConstrLems
    ++ [ exLem f, -- f_ex
         AddHint ResolveHint (exLemName f) RelAxDB, -- hints for f_ex
         CoqMarkVisibility (ChangeVisibility f Opaque), -- Opaque.
         refRelRwLem,
         AddHint RewriteHint (relDefRwLemName f) GraphRelDB,
         AddHint ResolveHint (relDefRwLemName f) RelAxDB,
         Coq.Instance (f ++ "_lookup_rw") ["dictionary", "rwLem", f] [("lookup'", Coq.Def (relDefRwLemName f))],
         refUnrefLemma' f (args, (f_res, ret)),
         Coq.AddHint Coq.RewriteHint (relDefThmName f) Coq.GraphRelDB, -- hints for f__f_rel
         refUnrefLemma f,
         Coq.AddHint Coq.ResolveHint (relDefLemName f) Coq.GraphRelDB, -- hints for f__f_rel'
         refRelMkLem,
         AddHint ResolveHint (relDefMkLemName f) GraphRelDB
       ]
    ++ [ TacInstance -- create a pack instance, only for first-order functions
           (packInstanceName f)
           (show $ toPack argsT_r retT)
           (Custom $ unwords ["\n\tbuildPackG", f, relDefName f, relDefThmName f, funcHoodLemName f] ++ ". ")
       | all (\case (_, RefType {}) -> True; _ -> False) args
       ]
  where
    -- Bindings of arguments
    (args, ret) = arrs tpf
    (argsT, retT) = (map (second trRefType) args, trRefType ret)
    (argsUT, retUT) = (map (second utrRefType) args, utrRefType ret)
    argsT_r = map (first (++ "_r")) argsT
    xis = argsUT
    -- Name for the result of f (chosen different from the names of the arguments)
    f_res = case retT of Coq.Subset v _ _ -> v; _ -> freshVar (map fst argsT)

-- | Translation of a definition `f` to the refined definition `f` (defined with tactics)
trDefRefDef :: Id -> RefType -> Expr -> Coq.Decl
trDefRefDef f tpf e = Coq.Definition f argsT (trRefType ret) (ProofBody tacs) Transparent
  where
    (args, ret) = arrs tpf
    argsT = map (\(id, arg) -> ((id, trRefType arg), False)) args
    tacs =
      let destructArgs = map (mkVarDestruct . fst) $ onlyFOArgs args
       in -- TODO: maybe use cleanInductions (usedIHs eT) eT
          destructArgs ++ trExprTacs (tpArgsArLoc tpf) e

-- | Translation of a definition `f` to the unrefined graph relation `f_rel`
trDefGraphRel :: Id -> RefType -> Expr -> Coq.Decl
trDefGraphRel f tp e =
  CoqInductive (relDefName f) [] (utrRefTypeTopProp tp) (map pathConstr paths)
  where
    paths = functionPaths e (tpArgsArLoc tp)
    pathConstr path = Coq.Constr (namePath f path False) (trPathToConstr f path)

-- * Functions for the construction of the graph relation

-- | Represents one path for a function.
-- The first element contains a map from arguments to their patterns,
-- the second from additional applications to the patterns for their results (“with”),
-- the third is the term of the branch, that is always a refinement
type FunctionPath = ([(Id, Reft)], [(Reft, Reft)], Reft)

-- | Creates the function paths of an expression by calling separateBranches:
-- function paths(e; x1...xn) of the paper (definition B.2)
functionPaths :: Expr -> [Reft] -> [FunctionPath]
functionPaths e xs = separateBranches (map (\case x@(LH.Var id _ _) -> (id, x)) xs) [] e

-- | Actually create the function paths of an expression: function P from the paper (definition B.3)
separateBranches :: [(Id, Reft)] -> [(Reft, Reft)] -> Expr -> [FunctionPath]
separateBranches σxs σp (Reft r) = [(σxs, σp, r)]
-- TODO: remove this case for if-then-else, but deal with it in the translation
{- separateBranches σxs σp (LH.Let x _ (Reft cond) (Case (LH.Var x') [("False", [], elseE), ("True", [], thenE)] _)) args | x == x' =
  let thenBrs = map (\(σxs_t, σp_t, r_t) -> (σxs_t, cond : σp_t, r_t)) $ separateBranches thenE args
      elseBrs = map (\(σxs_f, σp_f, r_f) -> (σxs_f, LH.Neg cond : σp_f, r_f)) $ separateBranches elseE args
   in thenBrs ++ elseBrs -}
-- Lets are subsituted away
separateBranches σxs σp (LH.Let x _ ex e) =
  let x_br = separateBranches σxs σp ex
   in concatMap (\(σxs_x, σp_x, r_x) -> separateBranches σxs_x σp_x (subst r_x x ex)) x_br
separateBranches σxs σp (Case r branches) =
  case alreadyMatched of
    -- if r is matched already
    Just (DC c, rs) -> maybe [] (separateBranches σxs σp) $ matchBranch (c, rs) cleanBranches
    Nothing -> case apps r of
      -- if r is an applied constructor
      (DC c, rs) -> maybe [] (separateBranches σxs σp) $ matchBranch (c, rs) cleanBranches
      -- if r is a parameter
      (LH.Var x _ _, []) -> concatMap (varRecCall x) cleanBranches
      -- if r is an application or top-level constant
      _ ->
        concatMap
          ( \((c, ys), e) ->
              separateBranches
                σxs
                (σp ++ [(r, foldl LH.App (LH.DC c) (map (\y -> LH.Var y 0 Local) ys))])
                e
          )
          cleanBranches
  where
    -- Reachable branches only
    cleanBranches = concatMap (\case (_, Nothing) -> []; (pat, Just x) -> [(pat, x)]) branches
    -- Returns the pattern to which r is matched if it is already
    alreadyMatched =
      apps <$> case r of
        LH.Var x _ _ -> case lookup x σxs of Just (LH.Var y _ _) -> Nothing; pat -> pat
        _ -> lookup r σp
    -- Recursive calls for the variable case, substituting the variable everywhere
    varRecCall :: Id -> ((Id, [Id]), Expr) -> [FunctionPath]
    varRecCall x (pat, ebr) =
      let pat' = matchToApp pat
       in separateBranches
            (map (second (subst pat' x)) σxs)
            (map (bimap (subst pat' x) (subst pat' x)) σp)
            (subst pat' x ebr)
    -- Given a pattern and a branch, returns the corresponding branch instantiated
    -- with respect to the arguments of the constructor.
    -- There should be at most one corresponding branch, so we return only one
    -- expression even if several branches are found.
    matchBranch :: (Id, [Reft]) -> [((Id, [Id]), Expr)] -> Maybe Expr
    matchBranch (c, rs) branches =
      case filter (\((c', _), _) -> c == c') branches of
        ((_, ys), e) : _ -> Just $ substs (zip rs ys) e
        [] -> Nothing

-- | Translates a function path into a constructor for f_rel.
-- Function pathInd (def 3.5) of the paper
trPathToConstr :: Id -> FunctionPath -> RocqType
trPathToConstr f (σxs, σp, rf) =
  Coq.Prop $ mkForallYs argsVars (go σp [])
  where
    -- Build forall (y)_{y in ys}, cqtm
    mkForallYs ys cqtm = foldr (\y -> FATerm (y, Nothing)) cqtm ys
    -- Variable introduced by destructing the arguments
    argsVars = Set.toList $ freeVars (map snd σxs) Set.\\ freeVars (map fst σxs)
    -- Auxiliary function matching on σp. The parameter hs contains hypotheses
    -- that have already been included
    go :: [(Reft, Reft)] -> [(Reft, Id)] -> CoqTerm
    go [] hs =
      let (hyps_r, r') = extractApps rf
          currentHyps = hyps_r \\ hs
          result = Coq.App (Coq.Def $ relDefName f) (map utrReft (map snd σxs ++ [r']))
       in hypsRV currentHyps result
    go ((r, rp) : σp') hs =
      let (hyps_r, r') = extractApps r
          currentHyps = hyps_r \\ hs
          foralls = mkForallYs . Set.toList $ freeVars rp
          equality = Coq.Bop EqProp (utrReft r') (utrReft rp)
          recCall = go σp' (hs ++ currentHyps)
       in hypsRV currentHyps . foralls $ Coq.Impl equality recCall

-- | Create a name for a constructor based on the patterns of the parameters (`pats`)
-- The flag takeVars indicates if we want the variables alone between the constructors
-- Used with true to create names of IH, and with false to create names for the relation
namePath :: Id -> FunctionPath -> Bool -> Id
namePath f (pats, _, _) takeVars = foldl (++) base $ map getConstructor pats'
  where
    pats' = map snd pats
    getConstructor (LH.Var x _ _) = if takeVars then "_" ++ x else ""
    getConstructor (LH.App (DC c) _) = "_" ++ c
    base = if all (null . getConstructor) pats' then relDefBranchName f else f

-- * Generated lemmas

-- | Functionhood lemma f_funct
functionhoodLemma :: Id -> ([(Id, RocqType)], (Id, RocqType)) -> Coq.Decl
functionhoodLemma f (argsT, (f_res, retT)) =
  Coq.Definition
    (funcHoodLemName f)
    (map (,True) argsT)
    ( mkForallT
        [(f_res, unrefRocqType retT), (f_res', unrefRocqType retT), h, k]
        (Coq.Prop $ Coq.Bop Coq.Eq (Coq.Var f_res) (Coq.Var f_res'))
    )
    (Coq.ProofBody functionhoodTacs)
    Coq.Opaque
  where
    f_res' = f_res ++ "'"
    indBrs = indBranches [] tacs
    inductTac = mkInductiveSkeleton argsT indBrs False
    functionhoodTacs = [Coq.Concat [inductTac, Coq.Custom "rel_functionhood_body"]]
    h = ("H", Coq.Prop $ Coq.App (Coq.Def $ relDefName f) (map (Coq.Var . fst) argsT ++ [Coq.Var f_res]))
    k = ("K", Coq.Prop $ Coq.App (Coq.Def $ relDefName f) (map (Coq.Var . fst) argsT ++ [Coq.Var f_res']))

refUnrefLemmas :: Id -> ([(Id, RefType)], (Id, RefType)) -> Coq.Decl
refUnrefLemmas f tp@(args, (f_res, ret)) =
  [refUnrefLemma' f tp, refUnrefLemma f tp]
  where
    xir's = mapSnd substs xirs
    equivalence fuArgs =
      Coq.Equiv
        (Coq.Bop Coq.Eq (projectTm $ Coq.App (Coq.Def f) xirVars) (Coq.Var x))
        (Coq.App (Coq.Def fu) $ fuArgs ++ [Coq.Var x])

-- | Lemma relating the refined definition and graph relation f__f_rel
refUnrefLemma' :: Id -> ([(Id, RefType)], (Id, RefType)) -> Coq.Decl
refUnrefLemma' f (args, (f_res, ret)) =
  mkCoqTheorem
    (relDefThmName f)
    (map (,False) $ xir's ++ [(f_res, utrRefType ret)])
    (equivalence xirProjArgs)
    [Coq.Custom "f__f_rel"]

-- | Lemma relating the refined definition and graph relation f__f_rel'
refUnrefLemma :: Id -> Coq.Decl
refUnrefLemma f =
  Coq.Definition
    (relDefLemName f)
    unrLemArgs
    unrLemTp
    ( Coq.ProofBody
        [ Coq.Intros $ replicate (length $ argsTps arrTp) (Coq.RewritePat Coq.RwLR),
          Coq.Exact (Coq.App (Coq.Def f_fu) (xirVars ++ [Coq.Var x]))
        ]
    )
    Coq.Opaque
  where
    unrLemArgs = map (,False) $ xis ++ xir's ++ [(x, utrRefType $ retTp arrTp)]
    unrLemTp = Coq.Prop $ foldr Coq.Impl (equivalence xiVars) xiEqxir

-- | Existence lemma f_ex
exLem :: Id -> Coq.Decl
exLem f =
  mkCoqTheorem
    (exLemName f)
    (map (,False) (args ++ catMaybes xiPs))
    (Coq.App (Def $ relDefName f) (vars ++ [Project $ mkApp (Def f) injArgs]))
    [ Concat
        [ Custom $ "existence_lemma_pre " ++ f,
          mkInductiveSkeleton uArgs indBrs True,
          Custom $ "existence_lemma_quicksolve " ++ f,
          Custom "f__f_rel_ex_body",
          Custom "f_rel_finish"
        ]
    ]

refRelRwLem = mkCoqTheorem (relDefRwLemName f) (map (,False) (args ++ catMaybes xiPs ++ [retArgU])) (Equiv (Coq.Bop Coq.Eq (Project $ mkApp (Def f) injArgs) (Coq.Var v)) relApp) [Custom "f__f_rel_rw"]

refRelMkLem = mkCoqLemma (relDefMkLemName f) (map (,True) args ++ mapMaybe ((,False) <$>) xiPs) relMkRet [Concat [Intros [], Refine (SubCast relMkRet (Subset v Hole TermHole) (mkApp (Def f) injArgs) (TermWitness TermHole)), Rewrite (Just RwRL) (Def $ relDefLemName f) Nothing, Easy]]

relConstrLems = concatMap (\lem -> [lem, AddHint RewriteHint (bindName lem) GraphRelBackDB]) relConstrLemmas

relConstrLemmas :: [Coq.Decl]
relConstrLemmas = mkRelBranchLemmas args retArgU univArgs univAxs conds' branches
  where
    matchAxs :: CoqTerm -> ([(Id, RocqType, RocqType)], CoqTerm)
    matchAxs (Forall [(z, zTp)] (Coq.Impl zDefTp p)) = first ((z, zTp, Prop zDefTp) :) $ matchAxs p
    matchAxs r = ([], r)
    mkX (x, xTp, xDefTp) = (x, xTp)
    mkXDef (x, xTp, xDefTp) = (x ++ "_def", xDefTp)
    (univArgs, univAxs, conds') = case conds of
      [] -> ([], [], conds)
      cond : condTl -> (map mkX commonAxs, map mkXDef commonAxs, zipWith mkCond' remConds (cond' : cond's))
        where
          (condAxs, cond') = matchAxs cond
          (condAxss, cond's) = unzip $ map matchAxs condTl
          commonAxs = filter (\ax -> all (ax `elem`) condAxss) condAxs
          remConds = map (\\ commonAxs) (condAxs : condAxss)
          mkCond' caxs = mkForall (map mkX caxs ++ map mkXDef caxs)

-- * Utility functions for declarations

-- | Filter arguments with a non-arrow refinement type (those that usually need to be destructed)
onlyFOArgs :: [(Id, RefType)] -> [(Id, RefType)]
onlyFOArgs = filter (\case (_, RefType {}) -> True; (_, ArrType {}) -> False)

-- | tpArgsArLoc((x_i:R_i|r_i)_{i ≤ n} -> R) = [Var x_i ar(R_i) Local]_{i ≤ n}
-- Used to give the initial patterns on the parameters of a function
tpArgsArLoc :: RefType -> [Reft]
tpArgsArLoc = map (\(x, tp) -> LH.Var x (arity tp) Local) . fst . arrs

-- * Declarations generated for the translation of a datatype

-- | Translates a constructor to an unrefined constructor
trConstr :: (Id, RefType) -> Coq.CoqConstr
trConstr (c, tp) = Constr (unrefinedConstrName c) (utrRefTypeTop tp)

-- | unrefTC(tc) = tc_u
unrefTC :: Id -> RocqType
unrefTC tc = Coq.TC (unrefinedTCName tc) []

-- | Unrefined datatype declaration TC_u
unrefTCDecl :: Id -> [(Id, RefType)] -> Coq.Decl
unrefTCDecl tc alts =
  CoqInductive (unrefinedTCName tc) [] (Sort SetSort) $ map trConstr alts

-- ** Equality

-- | Declarations related to the equality on unrefined constructors
tcEqDecls :: Id -> [(Id, RefType)] -> [Coq.Decl]
tcEqDecls tc alts = eqDecl tc alts : eqReflLem tc ++ eqbEqLem tc ++ [eqbInstanceDecl tc]

-- | Fixpoint definition of equality of two inductives
--
-- > Fixpoint TC_eq (x: TC_u) (y: TC_u): bool := ...
eqDecl :: Id -> [(Id, RefType)] -> Coq.Decl
eqDecl tc alts =
  Fix (tcEqName tc) [(("x", unrefTC tc), False), (("y", unrefTC tc), False)] Coq.boolTp $
    Match [Coq.Var "x", Coq.Var "y"] Nothing (map mkConstrEqBranch alts ++ [defaultBranch | length alts > 1])
  where
    mkConstrEqBranch :: (Id, RefType) -> ([(Id, [Id])], CoqTerm)
    mkConstrEqBranch alt@(c, tp) =
      let c_u = unrefinedConstrName c
       in ( [(c_u, tpArgs tp), (c_u, map (++ "'") $ tpArgs tp)],
            foldl (\b (x, tpx) -> Coq.Bop Andb b (mkEq tpx (Coq.Var x) (Coq.Var $ x ++ "'"))) btrue (fst $ arrs tp)
          )
    defaultBranch = ([("_", []), ("_", [])], bfalse)
    -- TODO: we could have an inductive tc' that is not the same one, but for which
    -- we need to use tc'_eq instead of boolean equality (the best would be to
    -- overload boolean equality)
    -- Is it really not possible to expand the boolean equality automatically?
    mkEq :: RefType -> CoqTerm -> CoqTerm -> CoqTerm
    mkEq (RefType _ (LH.TC tc') _) x x' | tc' == tc = Coq.App (Def $ tcEqName tc) [x, x']
    mkEq _ x x' = Coq.Bop EqualB x x'

-- | Lemma TC_eq_refl: reflexivity of TC_eq, with associated hint:
--
-- > Definition TC_eq_refl (x: TC_u): is_true (TC_eq x x).
-- > Proof. eq_refl. Qed.
-- > #[global] Hint Resolve TC_eq_refl : eq_hint_db.
eqReflLem :: Id -> [Coq.Decl]
eqReflLem tc =
  [ Coq.Definition
      (eqReflLemName tc)
      [(("x", unrefTC tc), False)]
      (Prop . IsTrue $ Coq.App (Def $ tcEqName tc) (map Coq.Var ["x", "x"]))
      (ProofBody [Custom "eq_refl"])
      Opaque,
    AddHint ResolveHint (eqReflLemName tc) EqHintDb
  ]

-- | Lemma TC_eqb_eq and hint:
--
-- > Definition TC_eqb_eq (s t: TC_u), is_true (TC_eq s t) -> s = t.
-- > Proof. ... Qed.
-- > #[global] Hint Resolve TC_eqb_eq : eq_hint_db.
eqbEqLem :: Id -> [Coq.Decl]
eqbEqLem tc =
  [ Coq.Definition
      (eqEqbEqLemName tc)
      [(("s", unrefTC tc), False), (("t", unrefTC tc), False)]
      ( Prop $
          Coq.Impl
            (IsTrue $ Coq.App (Def $ tcEqName tc) (map Coq.Var ["s", "t"]))
            (Coq.Bop Coq.Eq (Coq.Var "s") (Coq.Var "t"))
      )
      (ProofBody [Custom "eqb_eq_lem"])
      Opaque,
    AddHint ResolveHint (eqEqbEqLemName tc) EqHintDb
  ]

-- | Instantiation of the equality typeclass for TC_u
--
-- > #[global] Instance leibnitz_eq_TC : LeibnitzEqB := { ... }.
eqbInstanceDecl :: Id -> Coq.Decl
eqbInstanceDecl tc =
  Instance
    (leibnitzInstanceName tc)
    ["LeibnitzEqB"]
    [("equalB'", Def $ tcEqName tc), ("refl'", Def $ eqReflLemName tc), ("eqb_eq'", Def $ eqEqbEqLemName tc)]

-- ** Definition of the refined datatype (well-formedness predicate and type alias)

tcRefDecls :: Id -> [(Id, RefType)] -> [Coq.Decl]
tcRefDecls tc alts = [wfDecl tc alts, wfLem tc, refTCDecl tc]

-- | Well-formedness predicate TC_wf, defined as a fixpoint
--
-- > Fixpoint TC_wf (x: TC_u): Prop := match x with ...
-- TODO: remove projections of the arguments
wfDecl :: Id -> [(Id, RefType)] -> Coq.Decl
wfDecl tc alts = undefined

{- Fix (wfTCName tc) [(unrefTCArg, False)] (Sort PropSort) $
  Match
    [Coq.Var "x"]
    Nothing
    -- TODO: make something cleaner
    [ ( [(unrefinedConstrName c, map fst cargs)],
        mkAnd (getCase cargs ++ [sub vv (Coq.App (Cr $ unrefinedConstrName c) (map (Coq.Var . fst) cargs)) crf])
      )
    | (Constr c cTp) <- constrs,
      let (cargs, Subset vv _ (Coq.And _ crf)) = matchFunctionType [] cTp
    ]
where
  getCase :: [(Id, RocqType)] -> [CoqTerm]
  getCase cargs = concatMap argReqs (xIHs cargs')
    where
      cargs' = map subArgs cargs
      subArgs (v, Subset v' vBtp vr) = (v, Subset v vBtp (sub v' (Coq.Var v) vr))
      subArgs (v, Pack argTps uargTps z t p) = (v, Pack argTps uargTps z t p)
      argReqs ((_, Subset x _ r), _) = [r]
      argReqs ((f, Pack {}), _) = [Coq.App (Def uPackWfName) [Coq.Var f]] -- TODO: add required conditions
  unrefTCArg = ("x", unrefTC tc) -}

{-   xIHs :: [(Id, RocqType)] -> [((Id, RocqType), Bool)]
  xIHs = map isIHArg
    where
      isIHArg arg@(_, rt) = {-trace ("comparing "++tc++" and "++a)-} case rt of
        Subset _ (Coq.TC st _) _ -> (arg, st == tc)
        Subset {} -> (arg, False)
        Pack argTps uargTps z t p -> (arg, False)
        _ -> error "Found non normalized constructor type in CoqUtils.wfDecl." -}

-- | Lemma TC_wf_ref:
--
-- > Theorem TC_wf_ref [p: TC_u -> Prop] (tm: {v: TC_u | TC_wf v /\ p v}): TC_wf (proj1_sig tm).
wfLem :: Id -> Coq.Decl
wfLem tc =
  Coq.Definition
    (wfLemName tc)
    [(("p", Arrow (unrefTC tc) (Sort PropSort)), True), (tm, False)]
    (Prop $ Coq.App (Def $ wfTCName tc) [Project $ Coq.Var "tm"])
    (ProofBody [destructSubsetArg "tm", Oracle])
    Opaque
  where
    tm = ("tm", Subset "v" (unrefTC tc) $ Coq.And wfV (Coq.App (Coq.Var "p") [Coq.Var "v"]))
    wfV = Coq.App (Def $ wfTCName tc) [Coq.Var "v"]

-- | Definition of the refined TC as a notation:
--
-- > Global Notation TC := {x: TC_u | TC_wf x /\ True}.
refTCDecl :: Id -> Coq.Decl
refTCDecl tc = CoqNewType tc (Subset "x" (Coq.TC tc []) (Coq.And (Coq.App (Def $ wfTCName tc) [Coq.Var "x"]) TT))

-- ** Definition of the refined constructors

-- | Definition of the refined constructors C and the needed lemma:
--
-- > Definition C_lem [args]: TC_wf (C_u [args]) /\ True.
-- > Definition C [args]: TC := exist _ (C_u [args]) (C_lem [args]).
mkPseudoConstr :: Id -> (Id, RefType) -> [Coq.Decl]
mkPseudoConstr tc (c, tp) =
  [ Coq.Definition (psConstrLemName c) argsT retLem bodyLem Transparent,
    Coq.Definition c argsT retT bodyConstr Transparent
  ]
  where
    (args, ret@(RefType x _ retRef)) = arrs tp
    argsT = map ((,False) . second trRefType) args
    retT = trRefType ret
    -- C proj(x1) … proj(xn) (in LH), that translates to C_u proj1_sig(x1) … proj1_sig(x_n)
    unrefCrApp = foldr LH.App (DC c) (map Proj $ tpArgsArLoc tp)
    bodyLem = ProofBody [Custom "repeat first [split; solver]"]
    -- The translated refinement of the return type of C, where x is replaced by Cu proj1_sig(args)
    -- NOTE: instead of inlining the translation of the refinement of an
    -- inductive type, we could use a substitution in Rocq, but I want to avoid
    -- implementing it
    retLem = Prop $ Coq.And (Coq.App (Def $ wfTCName tc) [utrReft unrefCrApp]) (trReft [] $ subst unrefCrApp x retRef)
    -- The constructor is defined as an `exist`
    bodyConstr =
      let lemCrApp = Coq.App (Def $ psConstrLemName c) (map (Coq.Var . fst) args)
       in TermBody $ Exist TermHole (trReft [] unrefCrApp) (TermWitness lemCrApp)

-- | Lemmas giving well-formedness of inductive subterms, for each of the
-- inductive subterms
--
-- > Definition wf_C_argInd1 [args] (p: TC_wf (C [args])): IList_wf [inductive arg 1].
-- > ...
-- > Definition wf_C_argIndn [args] (p: TC_wf (C [args])): IList_wf [inductive arg n].
mkConstrWf :: Id -> (Id, RefType) -> [Coq.Decl]
mkConstrWf tc (c, tp) =
  map mkConstrWfArg (filter (isUserTC . snd) args)
  where
    args = fst $ arrs tp
    -- Whether a type is the refinement of a user-defined datatype.
    -- If so, this is an inductive argument for which we create a lemma
    isUserTC (RefType _ tp'@(LH.TC tcInd) _) = isLeft $ lookupTC tcInd initial
    isUserTC _ = False
    -- Build the lemma wf_tcInd_x
    mkConstrWfArg (x, RefType _ (LH.TC tcInd) _) =
      Coq.Definition
        (constrWfName c x)
        (argsUT ++ [(("p", ass), False)])
        (Prop goal)
        (ProofBody [Easy])
        Transparent
      where
        argsUT = map ((,True) . second utrRefType) args
        unrefCrApp = Coq.App (Def $ unrefinedConstrName c) $ map (Coq.Var . fst) args
        ass = Prop $ Coq.App (Def $ wfTCName tc) [unrefCrApp]
        goal = Coq.App (Def $ wfTCName tcInd) [Coq.Var x]

-- ** Final hints from a datatype translation

tcHints :: Id -> [(Id, RefType)] -> [Coq.Decl]
tcHints tc alts = map (\(a, b, c) -> AddHint a b c) hints
  where
    hints =
      [ (ResolveHint, wfLemName tc, WfDB),
        (UnfoldHint, wfTCName tc, WfDB),
        (ResolveHint, tcEqName tc, RefConstrDB)
      ]
        ++ refConstrHints
    refConstrHints =
      map ((ResolveHint,,RefConstrDB) . bindName) constrWfDecls
        -- Names of the lemmas create by mkConstrWf
        ++ map ((UnfoldHint,,RefConstrDB) . fst) alts
