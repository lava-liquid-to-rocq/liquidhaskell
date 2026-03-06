{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE TupleSections #-}

-- | This module contains the functions for the translation of declarations
module Lava.Declaration where

import Data.Bifunctor (bimap, first, second)
import Data.Either (isLeft)
import Data.List ((\\))
import Data.Maybe (catMaybes)
import qualified Data.Set as Set
import Lava.Calculus as LH
import Lava.Coq as Coq
import Lava.CoqSyntaxUtil (mkAnd, mkVarDestrPat, mkVarDestruct)
import Lava.CoqUtil
import Lava.Temporary (relConstrLemmas)
import Lava.Translation
import Lava.TypingEnvironment as TypEnv hiding (map)
import Lava.Util (freshVar)

-- TOOD: maybe put all translations, vars, injArgs etc in a record that is
-- passed to all functions

-- | Main function for the translation of declarations
trDecl :: LH.Decl -> [Coq.Decl]
-- An inductive data type gives an unrefined data type, a well-formedness predicate, some utility definitions and pseudo-constructors
trDecl (LH.Data tc alts) =
  unrefTCDecl tc alts --                     TC_u: unrefined datatype declaration
    : tcEqDecls tc alts --                   TC_eq: equality for TC_u and associated declarations
    ++ tcRefDecls tc alts --                 TC_wf and TC: Well-formedness and type alias
    ++ concatMap (mkPseudoConstr tc) alts -- C_i: Refined data constructors
    ++ concatMap (mkConstrWf tc) alts --     Lemmas for decomposing well-formedness on data constructors
    ++ tcHints tc alts --                    Final hints for datatypes and constructor
    -- For an unreflected definition, we only generate the refined definition,
    -- if the graph relation is needed, we generate it on the fly
trDecl (LH.Definition f tpf e False) = [trDefRefDef f tpf e]
-- For a reflected definition, we generate the graph relation, packs and other lemmas
trDecl (LH.Definition f tpf e True) =
  trDefRefDef f tpf e --                                  f
    : defGraphRelAndHints f tpf e --                      f_rel
    ++ relFunctionhoodLemma f tpf --                      f_rel_funct
    ++ relConstrLems f tpf --                             inversion lemmas for f_rel
    ++ defExLemma f tpf --                                f_ex
    ++ [CoqMarkVisibility $ ChangeVisibility f Opaque] -- Opaque f.
    ++ refRelRwLemma f tpf --                             f_rel_rw
    ++ refUnrefLemmas f tpf --                            f__f_rel and f__f_rel'
    ++ relMkLemma f tpf --                                f_rel_mk
    ++ packInstance f tpf --                              f_pack
  where
    -- Bindings of arguments
    (args, ret) = arrs tpf
    (argsT, retT) = (map (second trRefType) args, trRefType ret)
    (argsUT, retUT) = (map (second utrRefType) args, utrRefType ret)
    -- Name for the result of f (chosen different from the names of the arguments)
    -- Actually always v since not an arrow
    f_res = case ret of RefType v _ _ -> v; _ -> freshVar (map fst argsT)

-- * Translation of function definitions

-- ** Refined definition

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
    -- Filter arguments with a non-arrow refinement type (those that need to be destructed)
    onlyFOArgs :: [(Id, RefType)] -> [(Id, RefType)]
    onlyFOArgs = filter (\case (_, RefType {}) -> True; (_, ArrType {}) -> False)

-- ** Graph relation

-- | Unrefined graph relation `f_rel` and associated hint and instances:
--
-- > Inductive f_rel : … := …
-- > #[global] Hint Constructors f_rel : core_hint_db.
-- > #[global] Instance f_lookup_rel : dictionary rel f := { lookup' := f_rel }.
-- > #[global] Instance f_getF : getFunc f_rel := { getF' := f }.
defGraphRelAndHints :: Id -> RefType -> Expr -> [Coq.Decl]
defGraphRelAndHints f tpf e =
  [ trDefGraphRel f tpf e, -- f_rel
    AddHint ConstructorsHint (relDefName f) CoreDB,
    Instance (f ++ "_lookup_rel") ["dictionary", "rel", f] [("lookup'", Coq.Def $ f ++ "_rel")],
    Instance (f ++ "_getF") ["getFunc", relDefName f] [("getF'", Coq.Def f)]
  ]
  where
    trDefGraphRel :: Id -> RefType -> Expr -> Coq.Decl
    trDefGraphRel f tp e =
      CoqInductive (relDefName f) [] (utrRefTypeTopProp tp) (map pathConstr paths)
      where
        paths = functionPaths e (tpArgsArLoc tp)
        pathConstr path = Coq.Constr (namePath f path False) (trPathToConstr f path)

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
    argsVars = Set.toList $ freeVars (map snd σxs) Set.\\ Set.fromList (map fst σxs)
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

-- ** Generated lemmas

-- Functionhood lemma f_funct and hint:
--
-- > Definition f_rel_funct [args] (v v': Z) : f_rel [args] v -> f_rel [args] v' -> v = v'.
-- > #[global] Hint Resolve f_rel_funct : f_rel_funct_db.
relFunctionhoodLemma :: Id -> RefType -> [Coq.Decl]
relFunctionhoodLemma f tpf =
  [functionhoodLemma, AddHint ResolveHint (funcHoodLemName f) GraphRelDB]
  where
    (args, ret@(RefType f_res _ _)) = arrs tpf
    (argsT, retT) = (map (second trRefType) args, trRefType ret)
    functionhoodLemma =
      Coq.Definition
        (funcHoodLemName f)
        (map (,True) argsT)
        ( mkForallT
            [(f_res, unrefRocqType retT), (f_res', unrefRocqType retT)]
            ( Coq.Prop
                . Coq.Impl (relInst f_res)
                . Coq.Impl (relInst f_res')
                $ Coq.Bop Coq.Eq (Coq.Var f_res) (Coq.Var f_res')
            )
        )
        (Coq.ProofBody undefined {- functionhoodTacs -})
        Coq.Opaque
      where
        f_res' = f_res ++ "'"
        indBrs = undefined {- indBranches [] tacs -}
        inductTac = mkInductiveSkeleton argsT indBrs False
        functionhoodTacs = [Coq.Concat [inductTac, Coq.Custom "rel_functionhood_body"]]
        relInst x = Coq.App (Coq.Def $ relDefName f) (map (Coq.Var . fst) argsT ++ [Coq.Var x])

-- | Inversion lemmas for the graph relation, one for each branch
relConstrLems :: Id -> RefType -> [Coq.Decl]
relConstrLems = undefined {- concatMap (\lem -> [lem, AddHint RewriteHint (bindName lem) GraphRelBackDB]) relConstrLemmas -}

-- | Lemma f_ex
-- > Theorem f_rel_ex [args argsp]: f_rel [args] ⌊ f (exist args argsp) -⌋.
-- > #[global] Hint Resolve f_rel_ex : rel_ax_db.
defExLemma :: Id -> RefType -> [Coq.Decl]
defExLemma f tpf = [exLem, AddHint ResolveHint (exLemName f) RelAxDB]
  where
    exLem =
      Coq.Definition
        (exLemName f)
        (map (,False) $ fst (trRefTypeSplit tpf))
        (Prop $ Coq.App (Def $ relDefName f) (vars ++ [Project $ mkApp (Def f) injArgs]))
        ( ProofBody
            [ Concat
                [ Custom $ "existence_lemma_pre " ++ f,
                  mkInductiveSkeleton (map (second utrRefType) args) indBrs True,
                  Custom $ "existence_lemma_quicksolve " ++ f,
                  Custom "f__f_rel_ex_body",
                  Custom "f_rel_finish"
                ]
            ]
        )
        Opaque
    args = fst $ arrs tpf
    -- vars = (proj(x_i) if HO or x_i if FO)_{x_i: R_i in args}
    vars = map (\case (x, ArrType {}) -> Project (Coq.Var x); (x, _) -> Coq.Var x) args
    -- returns the injected version of each parameter: x_i if HO (already refined),
    -- or exist _ x_i x_i_p if FO (because splitted)
    injArgs = map injArg args
      where
        injArg (x, ArrType {}) = Coq.Var x
        injArg (x, RefType {}) = Exist TermHole (Coq.Var x) (TermWitness $ Coq.Var (subsetWitnessNm x))
    indBrs = undefined {- indBranches [] tac -}

-- | Lemma f__f_rel_rw
--
-- > Theorem f__f_rel_rw [args argsp] v: ⌊ f (exist _ args argsp) -⌋ = v <-> f_rel [args] v.
-- > #[global] Hint Rewrite f__f_rel_rw : f_rel_funct_db.
-- > #[global] Hint Resolve f__f_rel_rw : rel_ax_db.
-- > #[global] Instance f_lookup_rw : dictionary rwLem f := { lookup' := f__f_rel_rw }.
refRelRwLemma :: Id -> RefType -> [Coq.Decl]
refRelRwLemma f tpf =
  [ refRelRwLem,
    AddHint RewriteHint (relDefRwLemName f) GraphRelDB,
    AddHint ResolveHint (relDefRwLemName f) RelAxDB,
    Coq.Instance (f ++ "_lookup_rw") ["dictionary", "rwLem", f] [("lookup'", Coq.Def (relDefRwLemName f))]
  ]
  where
    refRelRwLem =
      Coq.Definition
        (relDefRwLemName f)
        (map (,False) $ fst (trRefTypeSplit tpf) ++ [(v, utrRefType ret)])
        (Prop $ Equiv defEq relApp)
        (ProofBody [Custom "f__f_rel_rw"])
        Opaque
    -- ⌊ f (exist _ args argsp) -⌋ = v
    defEq = Coq.Bop Coq.Eq (Project $ mkApp (Def f) injArgs) (Coq.Var v)
    -- f_rel [exist _ args argsp] v
    relApp = Coq.App (Def $ relDefName f) (vars ++ [Coq.Var v])
    -- TODO: make vars and injArgs outside autonomous (or put them in the main function)
    -- We can make it more obvious what they are by giving a function for the applications of f_rel
    -- and f directly
    (args, ret@(RefType v _ _)) = arrs tpf
    -- vars = (proj(x_i) if HO or x_i if FO)_{x_i: R_i in args}
    vars = map (\case (x, ArrType {}) -> Project (Coq.Var x); (x, _) -> Coq.Var x) args
    -- returns the injected version of each parameter: x_i if HO (already refined),
    -- or exist _ x_i x_i_p if FO (because splitted)
    injArgs = map injArg args
      where
        injArg (x, ArrType {}) = Coq.Var x
        injArg (x, RefType {}) = Exist TermHole (Coq.Var x) (TermWitness $ Coq.Var (subsetWitnessNm x))

-- | Lemmas f__f_rel and f__f_rel'
--
-- > Theorem f__f_rel [args refined] v : ⌊ f [args] -⌋ = v <-> (f_rel ⌊ [args] -⌋ v).
-- > #[global] Hint Rewrite f__f_rel : f_rel_funct_db.
-- > Theorem f__f_rel' [args_u unrefined] [args refined] v : [args_u = proj(args)] -> (⌊ f [args] -⌋ = v <-> f_rel [args_u] v).
-- > #[global] Hint Resolve f__f_rel' : f_rel_funct_db.
refUnrefLemmas :: Id -> RefType -> [Coq.Decl]
refUnrefLemmas f tpf =
  [ refUnrefLemma,
    Coq.AddHint Coq.RewriteHint (relDefThmName f) Coq.GraphRelDB,
    refUnrefLemma',
    Coq.AddHint Coq.ResolveHint (relDefLemName f) Coq.GraphRelDB
  ]
  where
    (args, ret@(RefType v _ _)) = arrs tpf
    argsT = map (second trRefType) args
    (argsUT, retUT) = (map (bimap (++ "_u") utrRefType) args, utrRefType ret)
    params = map (Coq.Var . fst) argsT
    params_u = map (Coq.Var . fst) argsUT
    equivalence fuArgs =
      Coq.Equiv
        (Coq.Bop Coq.Eq (Project $ Coq.App (Coq.Def f) params) (Coq.Var v))
        (Coq.App (Coq.Def (relDefName f)) $ fuArgs ++ [Coq.Var v])
    refUnrefLemma =
      mkCoqTheorem
        (relDefThmName f)
        (map (,False) $ argsT ++ [(v, utrRefType ret)])
        (equivalence $ map Project params)
        [Coq.Custom "f__f_rel"]
    refUnrefLemma' =
      Coq.Definition
        (relDefLemName f)
        unrLemArgs
        unrLemTp
        ( Coq.ProofBody
            [ Coq.Intros $ replicate (length args) (Coq.RewritePat Coq.RwLR),
              Coq.Exact (Coq.App (Coq.Def $ relDefThmName' f) (params ++ [Coq.Var v]))
            ]
        )
        Coq.Opaque
      where
        paramsEq =
          zipWith
            (\xiu xi -> Coq.Bop Coq.Eq (Coq.Var xiu) (Project (Coq.Var xi)))
            (map fst argsUT)
            (map fst argsT)
        unrLemArgs = map (,False) $ argsUT ++ argsT ++ [(v, retUT)]
        unrLemTp = Coq.Prop $ foldr Coq.Impl (equivalence params_u) paramsEq

-- Lemma f_rel_mk
--
-- > Definition f_rel_mk [args argsp] : {v: _ | f_rel [args] v}.
-- > #[global] Hint Resolve f_rel_mk : f_rel_funct_db.
relMkLemma :: Id -> RefType -> [Coq.Decl]
relMkLemma f tpf = [refRelMkLem, AddHint ResolveHint (relDefMkLemName f) GraphRelDB]
  where
    refRelMkLem =
      Coq.Definition
        (relDefMkLemName f)
        (mkOnlyWitnessesExplicit . fst $ trRefTypeSplit tpf)
        relMkRet
        ( ProofBody
            [ Concat
                [Intros [], Refine subCast, Rewrite (Just RwRL) (Def $ relDefLemName f) Nothing, Easy]
            ]
        )
        Opaque
    relMkRet = Subset v Hole relApp
    (args, ret@(RefType v _ _)) = arrs tpf
    relApp = Coq.App (Def $ relDefName f) (vars ++ [Coq.Var v])
    vars = map (\case (x, ArrType {}) -> Coq.App (Def projPackName) [Coq.Var x]; (x, _) -> Coq.Var x) args
    injArgs = map injArg args
      where
        injArg (x, ArrType {}) = Coq.Var x
        injArg (x, RefType {}) = Exist TermHole (Coq.Var x) (TermWitness $ Coq.Var (subsetWitnessNm x))
    subCast = SubCast relMkRet (Subset v Hole TermHole) (mkApp (Def f) injArgs) (TermWitness TermHole)
    -- All arguments to the function are implicit, except for witnesses x_p
    mkOnlyWitnessesExplicit ((x, utp) : (xp, p) : argsT)
      | xp == subsetWitnessNm x =
          ((x, utp), True) : ((xp, p), False) : mkOnlyWitnessesExplicit argsT
    mkOnlyWitnessesExplicit ((x, tp) : argsT) = ((x, tp), True) : mkOnlyWitnessesExplicit argsT
    mkOnlyWitnessesExplicit [] = []

-- ** Pack instance

-- Pack instance f_pack, only created for first-order functions
--
-- > #[global] Instance f_pack : ….
-- > Proof. buildPackG f f_rel f__f_rel f_rel_funct. Defined.
packInstance :: Id -> RefType -> [Coq.Decl]
packInstance f tpf =
  [TacInstance (packInstanceName f) (show $ toPack argsT_r retT) def | firstOrder]
  where
    (args, ret) = arrs tpf
    (argsT_r, retT) = (map (bimap (++ "_r") trRefType) args, trRefType ret)
    def = Custom $ unwords ["\n\tbuildPackG", f, relDefName f, relDefThmName f, funcHoodLemName f] ++ ". "
    firstOrder = all (\case (_, RefType {}) -> True; (_, ArrType {}) -> False) args

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
wfDecl :: Id -> [(Id, RefType)] -> Coq.Decl
wfDecl tc alts =
  Fix (wfTCName tc) [(("x", unrefTC tc), False)] (Sort PropSort) $
    Match [Coq.Var "x"] Nothing (map mkBranch alts)
  where
    mkBranch :: (Id, RefType) -> ([(Id, [Id])], CoqTerm)
    mkBranch (c, tp) = ([(unrefinedConstrName c, map fst args)], mkAnd (retRefT : map argProp args))
      where
        (args, RefType vv _ retRef) = arrs . removeFOArgProjs $ harmonizeBinderNames tp
        -- Proposition for the refinement of the return type, with C x1 … xn in the refinement
        retRefT = trReft [] (subst (foldl LH.App (DC c) (tpArgsArLoc tp)) vv retRef)
        -- Proposition for each argument
        argProp (x, argTp) =
          case trRefType argTp of
            Subset _ _ p -> p
            Pack {} -> Coq.App (Def uPackWfName) [Coq.Var x] -- TODO: add required conditions

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
    unrefCrApp = foldl LH.App (DC c) (map Proj $ tpArgsArLoc tp)
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
-- inductive subterms.
--
-- > Definition wf_C_argInd1 [args] (p: TC_wf (C [args])): IList_wf [inductive arg 1].
-- > #[global] Hint Resolve wf_C_argInd1 : ref_constr_db.
-- > ...
-- > Definition wf_C_argIndn [args] (p: TC_wf (C [args])): IList_wf [inductive arg n].
-- > #[global] Hint Resolve wf_C_argIndn : ref_constr_db.
mkConstrWf :: Id -> (Id, RefType) -> [Coq.Decl]
mkConstrWf tc (c, tp) =
  concatMap mkConstrWfArg (filter (isUserTC . snd) args)
  where
    args = fst $ arrs tp
    -- Whether a type is the refinement of a user-defined datatype.
    -- If so, this is an inductive argument for which we create a lemma
    isUserTC (RefType _ tp'@(LH.TC tcInd) _) = isLeft $ lookupTC tcInd initial
    isUserTC _ = False
    -- Build the lemma wf_tcInd_x and the associated hint
    mkConstrWfArg (x, RefType _ (LH.TC tcInd) _) =
      [ Coq.Definition
          (constrWfName c x)
          (argsUT ++ [(("p", ass), False)])
          (Prop goal)
          (ProofBody [Easy])
          Transparent,
        AddHint ResolveHint (constrWfName c x) RefConstrDB
      ]
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
        ++ map ((UnfoldHint,,RefConstrDB) . fst) alts
