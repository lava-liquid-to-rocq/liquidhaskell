{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

-- | This module contains the functions for the translation of declarations
module Lava.Declaration where

import Data.Bifunctor (bimap, first, second)
import Data.Either (isLeft)
import Data.List (groupBy, mapAccumL, nub, union, (\\))
import qualified Data.Map as Map
import Data.Maybe (isNothing)
import qualified Data.Set as Set
import Debug.Trace (trace)
import Lava.Calculus as LH
import Lava.Coq as Coq
import Lava.CoqSyntaxUtil
import Lava.Names
import Lava.Translation
import Lava.TypingEnvironment as TypEnv
import Text.PrettyPrint as PP
import Text.PrettyPrint.HughesPJClass hiding (first)

-- | Main function for the translation of declarations.
--   The boolean is True to use Equations
trDecl :: Bool -> LH.Decl -> [Coq.Decl]
-- An inductive data type gives an unrefined data type, a well-formedness predicate, some utility definitions and pseudo-constructors
-- trDecl decl | trace (render $ text "Translating" <+> pPrint decl) False = undefined
trDecl equations (LH.Data tc alts) =
  unrefTCDecl tc alts --                     TC_u: unrefined datatype declaration
    : tcEqDecls tc alts --                   TC_eq: equality for TC_u and associated declarations
    ++ tcRefDecls equations tc alts --                 TC_wf and TC: Well-formedness and type alias
    ++ concatMap (mkPseudoConstr equations tc) alts -- C_i: Refined data constructors
    ++ concatMap (mkConstrWf tc) alts --     Lemmas for decomposing well-formedness on data constructors
    ++ tcHints tc alts --                    Final hints for datatypes and constructor
    -- For an unreflected definition, we only generate the refined definition,
    -- if the graph relation is needed, we generate it on the fly.
    -- For a reflected definition, we generate the graph relation, packs and other lemmas
trDecl _ (LH.Import modName _) = [Coq.Load modName]
trDecl equations (LH.Definition f tpf e isRefl) =
  (if equations then trDefEquations fdata else trDefRefDef fdata) -- f  -- f
    ++ if isRefl
      then
        defGraphRelAndHints fdata --       f_rel
          ++ relFunctionhoodLemma fdata -- f_rel_funct
          ++ relConstrLems fdata --        inversion lemmas for f_rel
          ++ defExLemma fdata --           f_rel_ex
          ++ [mkOpaque f] --               Opaque f.
          ++ refRelRwLemma fdata --        f_rel_rw
          ++ refUnrefLemmas fdata --       f__f_rel and f__f_rel'
          ++ relMkLemma fdata --           f_rel_mk
          ++ packInstances fdata --        f_pack and f_upack
      else []
  where
    fdata = mkFuncData equations f tpf e

-- * Declarations generated for the translation of a datatype

-- | Translates a constructor to an unrefined constructor
trConstr :: (Id, RefType) -> Coq.CoqConstr
trConstr (c, tp) = Constr (unrefinedConstrName c) (utrRefTypeTop tp)

-- | unrefTC(tc) = tc_u
unrefTC :: Id -> RocqType
unrefTC tc = Coq.TC (unrefinedTCName tc) []

-- | Unrefined datatype declaration TC_u
unrefTCDecl :: Id -> [(Id, RefType)] -> Coq.Decl
-- unrefTCDecl tc _ | traceTC "unrefTCDecl" tc = undefined
unrefTCDecl tc alts =
  CoqInductive (unrefinedTCName tc) [] (Sort TypeSort) $ map trConstr alts

-- ** Equality

-- | Declarations related to the equality on unrefined constructors
tcEqDecls :: Id -> [(Id, RefType)] -> [Coq.Decl]
-- tcEqDecls tc _ | traceTC "tcEqDecls" tc = undefined
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
    mkConstrEqBranch (c, tp) =
      let c_u = unrefinedConstrName c
       in ( [(c_u, tpArgs tp), (c_u, map (++ "'") $ tpArgs tp)],
            foldl (\b (x, tpx) -> Coq.Bop (Binop Coq.And UnrefOp) b (mkEq tpx (Coq.Var x) (Coq.Var $ x ++ "'"))) btrue (fst $ arrs tp)
          )
    defaultBranch = ([("_", []), ("_", [])], bfalse)
    -- TODO: we could have an inductive tc' that is not the same one, but for which
    -- we need to use tc'_eq instead of boolean equality (the best would be to
    -- overload boolean equality)
    -- Is it really not possible to expand the boolean equality automatically?
    mkEq :: RefType -> CoqTerm -> CoqTerm -> CoqTerm
    mkEq (RefType _ (LH.TC tc') _) x x' | tc' == tc = Coq.App (Def $ tcEqName tc) [x, x']
    mkEq _ x x' = Coq.Bop (Binop Coq.Eq RefOp) x x'

-- | Lemma TC_eq_refl: reflexivity of TC_eq, with associated hint:
--
-- > Definition TC_eq_refl: forall (x: TC_u), is_true (TC_eq x x).
-- > Proof. eq_refl. Qed.
-- > #[global] Hint Resolve TC_eq_refl : eq_hint_db.
eqReflLem :: Id -> [Coq.Decl]
eqReflLem tc =
  [ Coq.Definition
      (eqReflLemName tc)
      []
      (FAType ("x", unrefTC tc) . Prop . mkIsTrue $ Coq.App (Def $ tcEqName tc) (map Coq.Var ["x", "x"]))
      (ProofBody [Custom "eq_refl"])
      Opaque,
    AddHint ResolveHint (eqReflLemName tc) EqHintDB
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
      []
      ( FAType ("s", unrefTC tc)
          . FAType ("t", unrefTC tc)
          . Prop
          $ Coq.Bop
            (Binop Coq.Impl PropOp)
            (mkIsTrue $ Coq.App (Def $ tcEqName tc) (map Coq.Var ["s", "t"]))
            (Coq.Bop (Binop Coq.RocqEq PropOp) (Coq.Var "s") (Coq.Var "t"))
      )
      (ProofBody [Custom "eqb_eq_lem"])
      Opaque,
    AddHint ResolveHint (eqEqbEqLemName tc) EqHintDB
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

tcRefDecls :: Bool -> Id -> [(Id, RefType)] -> [Coq.Decl]
-- tcRefDecls tc _ | traceTC "tcRefDecls" tc = undefined
tcRefDecls eq tc alts = [wfDecl eq tc alts, wfLem tc, refTCDecl tc]

-- | Well-formedness predicate TC_wf, defined as a fixpoint
--
-- > Fixpoint TC_wf (x: TC_u): Prop := match x with ...
wfDecl :: Bool -> Id -> [(Id, RefType)] -> Coq.Decl
wfDecl eq tc alts =
  Fix (wfTCName tc) [(("x", unrefTC tc), False)] (Sort PropSort) $
    Match [Coq.Var "x"] Nothing (map mkBranch alts)
  where
    mkBranch :: (Id, RefType) -> ([(Id, [Id])], CoqTerm)
    mkBranch (c, tp) = ([(unrefinedConstrName c, map fst args)], mkAnd (retRefT : map argProp args))
      where
        (args, (vv, _, retRef)) = arrs . removeFOArgProjs $ harmonizeBinderNames tp
        -- Proposition for the refinement of the return type, with C x1 … xn in the refinement
        retRefT = utrReftProp eq (subst (foldl LH.App (DC c) (tpArgsArLoc tp)) vv retRef)
        -- Proposition for each argument
        argProp (x, tpArg) =
          case trRefType eq tpArg of
            Subset _ _ p -> p
            Pack {} -> Coq.App (Def uPackWfName) [Coq.Var x] -- TODO: add required conditions
            _ -> PropLit True

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
    tm = ("tm", Subset "v" (unrefTC tc) $ Coq.Bop (Binop Coq.And PropOp) wfV (Coq.App (Coq.Var "p") [Coq.Var "v"]))
    wfV = Coq.App (Def $ wfTCName tc) [Coq.Var "v"]
    destructSubsetArg x = DestructSubsetTerm (Coq.Var x) (ConjDestrPat [SingleIdPat x, SingleIdPat $ subsetWitnessNm x])

-- | Definition of the refined TC as a notation:
--
-- > Global Notation TC := {x: TC_u | TC_wf x /\ True}.
refTCDecl :: Id -> Coq.Decl
refTCDecl tc = CoqNewType tc (Subset "x" (Coq.TC (unrefinedConstrName tc) []) (Coq.Bop (Binop Coq.And PropOp) (Coq.App (Def $ wfTCName tc) [Coq.Var "x"]) (PropLit True)))

-- ** Definition of the refined constructors

-- | Definition of the refined constructors C and the needed lemma:
--
-- > Definition C_lem [args]: TC_wf (C_u [args]) /\ True.
-- > Definition C [args]: TC := exist _ (C_u [args]) (C_lem [args]).
mkPseudoConstr :: Bool -> Id -> (Id, RefType) -> [Coq.Decl]
-- mkPseudoConstr tc (c, _) | traceDC "mkPseudoConstr" tc c = undefined
mkPseudoConstr eq tc (c, tp) =
  [ Coq.Definition (psConstrLemName c) argsT retLem bodyLem Transparent,
    Coq.Definition c argsT retT bodyConstr Transparent
  ]
  where
    (args, ret@(x, _, retRef)) = arrs tp
    argsT = map ((,False) . second (trRefType eq)) args
    retT = trRefType eq (mkRefType ret)
    -- C proj(x1) … proj(xn) (in LH), that translates to C_u proj1_sig(x1) … proj1_sig(x_n)
    unrefCrApp = foldl LH.App (DC c) (map mkProj $ tpArgsArLoc tp)
    bodyLem = ProofBody [Custom "repeat first [split; solver]"]
    -- The translated refinement of the return type of C, where x is replaced by Cu proj1_sig(args)
    -- NOTE: instead of inlining the translation of the refinement of an
    -- inductive type, we could use a substitution in Rocq, but I want to avoid
    -- implementing it
    retLem = Prop $ Coq.Bop (Binop Coq.And PropOp) (Coq.App (Def $ wfTCName tc) [utrReft eq unrefCrApp]) (utrReftProp eq $ subst unrefCrApp x retRef)
    -- The constructor is defined as an `exist`
    bodyConstr =
      let lemCrApp = Coq.App (Def $ psConstrLemName c) (map (Coq.Var . fst) args)
       in TermBody $ Exist TermHole (utrReft eq unrefCrApp) (TermWitness lemCrApp)

-- | Lemmas giving well-formedness of inductive subterms, for each of the
-- inductive subterms.
--
-- > Definition wf_C_argInd1 [args] (p: TC_wf (C [args])): IList_wf [inductive arg 1].
-- > #[global] Hint Resolve wf_C_argInd1 : ref_constr_db.
-- > ...
-- > Definition wf_C_argIndn [args] (p: TC_wf (C [args])): IList_wf [inductive arg n].
-- > #[global] Hint Resolve wf_C_argIndn : ref_constr_db.
mkConstrWf :: Id -> (Id, RefType) -> [Coq.Decl]
-- mkConstrWf tc (c, _) | traceDC "mkConstrWf" tc c = undefined
mkConstrWf tc (c, tp) =
  concatMap mkConstrWfArg (concatMap userTCs args)
  where
    args = fst $ arrs tp
    -- List of inductive datatypes (not builtin) appearing in args.
    -- For those we create a lemma
    userTCs (x, RefType _ (LH.TC tcInd) _) | isLeft (lookupTC tcInd initial) = [(x, tcInd)]
    userTCs _ = []
    -- Build the lemma wf_tcInd_x and the associated hint
    mkConstrWfArg (x, tcInd) =
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
-- tcHints tc _ | traceTC "tcHints" tc = undefined
tcHints tc alts = map (\(a, b, c) -> AddHint a b c) hints
  where
    hints =
      [ (ResolveHint, wfLemName tc, WfDB),
        (UnfoldHint, wfTCName tc, WfDB),
        (ResolveHint, tcEqName tc, RefConstrDB)
      ]
        ++ map ((UnfoldHint,,RefConstrDB) . fst) alts

-- * Translation of function definitions

-- ** Record with data shared across the functions

data FuncData = FuncData
  { -- | function name
    name :: Id,
    -- | function type
    tpf :: RefType,
    -- | function body with the recursive variable marked as such
    body :: Expr,
    -- | function parameters (x_i: R_i)_{i ≤ n}
    -- ret :: (Id, BaseType, Reft), -- ^ function return type
    args :: [(Id, RefType)],
    -- | name of the return value of the function
    retName :: Id,
    -- | translation of the parameters
    argsT :: [(Id, RocqType)],
    -- | unrefined translation of the parameters
    argsUT :: [(Id, RocqType)],
    -- | refined translation of the return type
    retT :: RocqType,
    -- | unrefined translation of the return type
    retUT :: RocqType,
    -- | function paths
    paths :: [FunctionPath],
    -- | argument names, projected if first-order
    projArgs :: [CoqTerm],
    -- | argument names, injected if first-order
    injArgs :: [CoqTerm],
    -- | whether we use Equations
    equations :: Bool
  }

mkFuncData :: Bool -> Id -> RefType -> Expr -> FuncData
-- mkFuncData name _ _ | trace ("mkFuncData(" ++ name ++ ")") False = undefined
mkFuncData eq name tpf body =
  FuncData
    { name,
      tpf,
      body,
      args,
      retName,
      argsT = map (second (trRefType eq)) args,
      argsUT = map (second utrRefType) args,
      retT = trRefType eq ret,
      retUT = utrRefType ret,
      paths = functionPaths body (tpArgsArLoc tpf),
      projArgs = map projArg args,
      injArgs = map injArg args,
      equations = eq
    }
  where
    (args, ret0@(retName, _, _)) = arrs tpf
    ret = mkRefType ret0
    projArg (x, ArrType {}) = Project (Coq.Var x)
    projArg (x, _) = Coq.Var x
    injArg (x, ArrType {}) = Coq.Var x
    injArg (x, RefType {}) = Exist TermHole (Coq.Var x) (TermWitness $ Coq.Var (subsetWitnessNm x))

traceF :: String -> FuncData -> Bool
traceF s f = trace ("Defining " ++ s ++ "(" ++ name f ++ ")") False

traceTC :: String -> Id -> Bool
traceTC s tc = trace ("Defining " ++ s ++ "(" ++ tc ++ ")") False

traceDC :: String -> Id -> Id -> Bool
traceDC s tc dc = trace ("Defining " ++ s ++ "(" ++ tc ++ "." ++ dc ++ ")") False

-- ** Representation of the λr function graph

-- | Represents one path for a function.
-- The first element contains a map from arguments to their patterns,
-- the second from additional applications to the patterns for their results (“with”),
-- the third is the term of the branch, that is always a refinement
type FunctionPath = ([(Id, Reft)], [(Reft, Reft)], Reft)

-- | Creates the function paths of an expression by calling separateBranches:
-- function paths(e; x1...xn) of the paper (definition B.2)
functionPaths :: Expr -> [Reft] -> [FunctionPath]
functionPaths e xs =
  let varPat xvar@(LH.Var x _ _) = (x, xvar)
      varPat _ = error "Parameters should all be variables"
   in separateBranches (map varPat xs) [] e

-- | Actually create the function paths of an expression: function P from the paper (definition B.3)
separateBranches :: [(Id, Reft)] -> [(Reft, Reft)] -> Expr -> [FunctionPath]
separateBranches σxs σp (Reft r) = [(σxs, σp, r)]
-- Lets are subsituted away
separateBranches σxs σp (LH.Let x _ ex e) =
  let x_br = separateBranches σxs σp ex
   in concatMap (\(σxs_x, σp_x, r_x) -> separateBranches σxs_x σp_x (subst r_x x e)) x_br
separateBranches σxs σp (Case r branches _) =
  case alreadyMatched of
    -- if r is matched already:
    Just (DC c, rs) -> maybe [] (separateBranches σxs σp) $ matchBranch (c, rs) cleanBranches
    -- if not:
    Nothing -> case apps r of
      -- if r is an applied constructor
      (DC c, rs) -> maybe [] (separateBranches σxs σp) $ matchBranch (c, rs) cleanBranches
      -- if r is a first-order local variable (always injected)
      (Inj (LH.Var x 0 _) _, []) -> concatMap (varRecCall x) cleanBranches
      -- if r is a first-order global variable
      (LH.Var x 0 _, []) -> concatMap (varRecCall x) cleanBranches
      -- if r is an application or top-level constant
      _ -> concatMap (\(pat, e) -> separateBranches σxs (σp ++ [(r, matchToApp pat)]) e) cleanBranches
    Just _ -> error "Error in creation of function paths"
  where
    -- Reachable branches only
    cleanBranches = concatMap (\case (_, Nothing) -> []; (pat, Just x) -> [(pat, x)]) branches
    -- Returns the pattern to which r is matched if it is already
    alreadyMatched =
      apps <$> case r of
        Inj (LH.Var x 0 _) _ -> case lookup x σxs of Just (LH.Var {}) -> Nothing; pat -> pat
        LH.Var x 0 _ -> case lookup x σxs of Just (LH.Var {}) -> Nothing; pat -> pat
        _ -> lookup r σp
    -- Recursive calls for the variable case, substituting the variable everywhere
    varRecCall :: Id -> ((Id, [(Id, Bool)]), Expr) -> [FunctionPath]
    varRecCall x (pat, ebr) =
      let pat' = matchToApp pat
       in separateBranches
            (map (second (subst pat' x)) σxs)
            (map (bimap (subst pat' x) (subst pat' x)) σp)
            (if x `notElem` freeVars pat' then subst pat' x ebr else ebr)
    -- Returns the application corresponding to the pattern of a case
    -- Since we do not have higher-order constructors, all variables are of arity 0
    matchToApp :: (Id, [(Id, Bool)]) -> Reft
    matchToApp (c, ys) = foldl LH.App (DC c) (map (\(y, _) -> LH.Var y 0 Local) ys)
    -- Given a pattern and a branch, returns the corresponding branch instantiated
    -- with respect to the arguments of the constructor.
    -- There should be at most one corresponding branch, so we return only one
    -- expression even if several branches are found.
    matchBranch :: (Id, [Reft]) -> [((Id, [(Id, Bool)]), Expr)] -> Maybe Expr
    matchBranch (c, rs) brs =
      case filter (\((c', _), _) -> c == c') brs of
        ((_, ys), e) : _ -> Just $ substs (zip rs (map fst ys)) e
        [] -> Nothing

-- | Factorize function paths over the destruction of arguments and over guard conditions.
-- The result structure is the same as an EqBranch, but for λr:
-- it is a list of argument patterns, guard conditions and a list of guard patterns and terms for the branch
factorizePaths :: [FunctionPath] -> [([(Id, Reft)], [Reft], [([Maybe Reft], Reft)])]
factorizePaths = map groupGuards . groupArgPaths
  where
    -- Factorize guard conditions and harmonize across the branches
    groupGuards (σxs, withs) = (σxs, allGuards, map (first completePatterns) withs)
      where
        allGuards = foldr union [] (map (map fst . fst) withs)
        -- Nothing for a guard pattern that is not involved in this branch
        -- TODO: that does not seem correct
        completePatterns :: [(Reft, Reft)] -> [Maybe Reft]
        completePatterns withPats = map (`lookup` withPats) allGuards

-- | Groups together function paths that destruct arguments in the same way
groupArgPaths :: [FunctionPath] -> [([(Id, Reft)], [([(Reft, Reft)], Reft)])]
groupArgPaths branches =
  map groupMatches $ groupBy (\(σ1, _, _) (σ2, _, _) -> σ1 == σ2) branches
  where
    groupMatches [] = ([], [])
    groupMatches br@((xs, _, _) : _) = (xs, [(with, tm) | (_, with, tm) <- br])

-- ** Refined definition

-- | Translation of a definition `f` to the refined definition `f` (with tactics)
--
-- > Definition f_spec (xi:Ai)_i : Type := {v:A|p}.
-- > #[global] Hint Unfold f_spec : lia_unfold.
-- > Definition f (xi:Ai)_i : f_spec (x_i)_i.
-- > Proof. … Defined.
trDefRefDef :: FuncData -> [Coq.Decl]
-- trDefRefDef f | traceF "trDefRefDef" f = undefined
trDefRefDef f =
  [ Coq.Definition f_spec (map (,False) $ argsT f) (Sort TypeSort) (TypeBody $ retT f) Transparent,
    AddHint UnfoldHint f_spec LiaUnfoldDB,
    Coq.Definition (name f) (map (,False) (argsT f)) f_ret (ProofBody tacs) Transparent
  ]
  where
    f_spec = specName $ name f
    f_ret = Prop $ Coq.App (Def f_spec) (map (Coq.Var . fst) (argsT f))
    tacs =
      let destructArgs = map (mkVarDestruct . fst) $ onlyFOArgs (args f)
       in destructArgs ++ trExprTacs (equations f) (body f)
    -- Filter arguments with a non-arrow refinement type (those that need to be destructed)
    onlyFOArgs :: [(Id, RefType)] -> [(Id, RefType)]
    onlyFOArgs = filter (\case (_, RefType {}) -> True; (_, ArrType {}) -> False)

-- | Translation of a definition `f` to the refined definition `f` (with Equations)
trDefEquations :: FuncData -> [Coq.Decl]
-- trDefRefDef f | traceF "trDefRefDef" f = undefined
trDefEquations f =
  [ Equations f_rec argsTsplit retTsplit (mkEquationsBranches (equations f) (paths f)),
    Coq.Definition (name f) (map (,False) $ argsT f) (retT f) (TermBody defBody) Transparent
  ]
  where
    f_rec = eqFunctionName $ name f
    (argsTsplit, retTsplit) = trRefTypeSplit (equations f) (tpf f)
    -- f_rec ⌊x1⌋ ⌈x1⌉ … ⌊xn⌋ ⌈xn⌉
    -- where xi is only projected if it is of a simple refinement type
    defBody = Coq.App (Coq.Var f_rec) . concatMap splitParameter $ argsT f
      where
        -- Split a parameter x into ⌊x⌋ and ⌈x⌉ if x is of a simple refinement type
        splitParameter :: (Id, RocqType) -> [CoqTerm]
        splitParameter (x, Coq.Subset {}) = [Project (Coq.Var x), Proj2sig (Coq.Var x)]
        splitParameter (x, _) = [Coq.Var x]

-- | Translates a list of `FunctionPath` into a list of `EqBranch`
-- Translates the matches and the path expressions and gathers the guards
mkEquationsBranches :: Bool -> [FunctionPath] -> [EqBranch]
mkEquationsBranches eq paths = map trBranch $ factorizePaths paths
  where
    trBranch :: ([(Id, Reft)], [Reft], [([Maybe Reft], Reft)]) -> EqBranch
    trBranch (σxs, with, guards) =
      (concatMap (trArgPattern . snd) σxs, map (mkProject . trReft eq) with, map trGuard guards)
    -- Translate arguments patterns and change `pat` to `pat _` for FO parameters
    trArgPattern :: Reft -> [CoqTerm]
    trArgPattern pat@(LH.Var _ n _) | n > 0 = [utrReft eq pat]
    trArgPattern pat = [utrReft eq pat, TermHole]
    -- Translate guards patterns and the branch term
    -- We add holes as patterns for guards that are not involved in the branch
    trGuard (guardPats, tm) = (map (maybe TermHole (utrReft eq)) guardPats, trExpr eq $ Reft tm)

-- ** Graph relation

-- | Unrefined graph relation `f_rel` and associated hint and instances:
--
-- > Inductive f_rel : … := …
-- > #[global] Hint Constructors f_rel : core_hint_db.
-- > #[global] Instance f_lookup_rel : dictionary rel f := { lookup' := f_rel }.
-- > #[global] Instance f_getF : getFunc f_rel := { getF' := f }.
defGraphRelAndHints :: FuncData -> [Coq.Decl]
-- defGraphRelAndHints f | traceF "defGraphRelAndHints" f = undefined
defGraphRelAndHints f =
  [ trDefGraphRel, -- f_rel
    AddHint ConstructorsHint (relDefName $ name f) CoreDB,
    Instance (name f ++ "_lookup_rel") ["dictionary", "rel", name f] [("lookup'", Coq.Def $ name f ++ "_rel")],
    Instance (name f ++ "_getF") ["getFunc", relDefName $ name f] [("getF'", Coq.Def $ name f)]
  ]
  where
    trDefGraphRel :: Coq.Decl
    trDefGraphRel =
      let pathConstrs = snd . mapAccumL mkUniqueNames Map.empty $ map pathConstr (paths f)
       in CoqInductive (relDefName $ name f) [] (utrRefTypeTopProp $ tpf f) pathConstrs
    pathConstr path@(σxs, guards, _) =
      Coq.Constr (pathConstrName (name f) (map snd σxs ++ map snd guards) "Constr") (trPathToConstr (equations f) (name f) (map snd $ argsUT f) path)
    -- Make names of the constructors unique: there can be redundancy when there are additional guards
    -- This could be factorized inside pathConstrName if we need it in another function
    mkUniqueNames :: Map.Map Id Int -> CoqConstr -> (Map.Map Id Int, CoqConstr)
    mkUniqueNames usedNames (Coq.Constr f_p tp) =
      case Map.lookup f_p usedNames of
        Nothing -> (Map.insert f_p 1 usedNames, Coq.Constr f_p tp)
        Just nbOfUses -> (Map.adjust (+ 1) f_p usedNames, Coq.Constr (f_p ++ "_" ++ show nbOfUses) tp)

-- TODO: extend to Expr as the last term for Equations

-- | Translates a function path into a constructor for f_rel.
-- Function pathInd (def 3.5) of the paper
-- Requires the unrefined translation of argument types because Rocq cannot
-- infer it for higher-order parameters of the function
trPathToConstr :: Bool -> Id -> [RocqType] -> FunctionPath -> RocqType
trPathToConstr eq f argsUT p@(σxs, _, _) =
  Coq.Prop $ Forall argsVarsWithTypes (trPathGuard eq f p [] Nothing)
  where
    -- Variables introduced by destructing the arguments
    argsVarsWithTypes = concat $ zipWith patVars σxs argsUT
    patVars (x, LH.Var x' n Local) tp | x == x' && n > 0 = [(x, tp)]
    patVars (_, pat) _ = map (,Hole) . Set.toList $ LH.freeVars pat

-- | Auxiliary function for `trPathToConstr` and `inversionLemma`
-- Builds a Rocq term from the guards of a path and the path result.
-- The third argument hs contains hypotheses that have already been included
-- The fourth argument is Nothing is we build the graph relation, Just z where
-- z is a variable bound to the result of the application of f_rel in the
-- inversion lemma
trPathGuard :: Bool -> Id -> FunctionPath -> [(Reft, Id)] -> Maybe Id -> CoqTerm
trPathGuard eq f (σxs, [], rf) hs relRes =
  let (hyps_r, r') = extractApps rf
      currentHyps = hyps_r \\ hs
      result =
        case relRes of
          Nothing -> Coq.App (Coq.Def $ relDefName f) (map (utrReft eq) (map snd σxs ++ [r']))
          Just z -> Coq.Bop (Binop Coq.Eq PropOp) (Coq.Var z) (utrReft eq r')
   in hypsRV eq currentHyps (isNothing relRes) result
trPathGuard eq f (σxs, (r, rp) : σp', rf) hs relRes =
  let (hyps_r, r') = extractApps r
      currentHyps = hyps_r \\ hs
      foralls = mkForallXs . Set.toList $ LH.freeVars rp
      equality = Coq.Bop (Binop Coq.Eq PropOp) (utrReft eq r') (utrReft eq rp)
      recCall = trPathGuard eq f (σxs, σp', rf) (hs ++ currentHyps) relRes
   in hypsRV eq currentHyps (isNothing relRes) . foralls $ Coq.Bop (Binop Coq.Impl PropOp) equality recCall

-- | From a function name `f` and a list of patterns `pats`,
-- returns a name for the constructor for f wrt pats
-- The third argument is an additional string to add to the result if we end up
-- with just the name of the function
pathConstrName :: Id -> [Reft] -> String -> Id
pathConstrName f pats additional =
  let res = render . fst $ aux (DC f, pats)
   in if res == f then f ++ "_" ++ additional else res
  where
    -- We return an int indicating how many _ we must insert
    aux :: (Reft, [Reft]) -> (Doc, Int)
    aux (DC c, args) =
      if all (\case (LH.Var {}) -> True; _ -> False) args
        then (text c, 0)
        else
          let (argsPrint, n) = second (foldr max 0) . unzip $ map (aux . apps) args
           in (hcat $ punctuate (text $ replicate (n + 1) '_') (text c : argsPrint), n + 1)
    aux (LH.Var {}, _) = ("x", 0)
    aux _ = ("", 0)

-- ** Generated lemmas

-- Functionhood lemma f_funct and hint:
--
-- > Definition f_rel_funct [args] (v v': Z) : f_rel [args] v -> f_rel [args] v' -> v = v'.
-- > #[global] Hint Resolve f_rel_funct : f_rel_funct_db.
relFunctionhoodLemma :: FuncData -> [Coq.Decl]
-- relFunctionhoodLemma f | traceF "relFunctionhoodLemma" f = undefined
relFunctionhoodLemma f =
  [functionhoodLemma, AddHint ResolveHint (funcHoodLemName $ name f) GraphRelDB]
  where
    functionhoodLemma =
      Coq.Definition
        (funcHoodLemName $ name f)
        (map (,True) $ argsUT f)
        ( mkForallT
            [(retName f, retUT f), (retName', retUT f)]
            ( Coq.Prop
                . Coq.Bop (Binop Coq.Impl PropOp) (relInst $ retName f)
                . Coq.Bop (Binop Coq.Impl PropOp) (relInst retName')
                $ Coq.Bop (Binop Coq.RocqEq PropOp) (Coq.Var $ retName f) (Coq.Var retName')
            )
        )
        (Coq.ProofBody functionhoodTacs)
        Coq.Opaque
      where
        retName' = retName f ++ "'"
        inductTac = mkIndSkel (equations f) (body f) False
        functionhoodTacs = [mkConcat [inductTac, Coq.Custom "rel_functionhood_body"]]
        relInst x = Coq.App (Coq.Def . relDefName $ name f) (map (Coq.Var . fst) (args f) ++ [Coq.Var x])

-- | Inversion lemmas for the graph relation, one for each branch
relConstrLems :: FuncData -> [Coq.Decl]
-- relConstrLems f | traceF "relConstrLems" f = undefined
relConstrLems f = concatMap (inversionLemma (equations f) (name f)) $ groupArgPaths (paths f)

-- | Definition of the inversion lemma and rewrite hint.
-- The second argument contains all paths that match on the arguments in the same way
inversionLemma :: Bool -> Id -> ([(Id, Reft)], [([(Reft, Reft)], Reft)]) -> [Coq.Decl]
inversionLemma eq f (σxs, guards) =
  [ Coq.Definition
      f_lem
      (map ((,False) . (,Hole)) $ argsVars ++ [res])
      (Coq.Prop $ Coq.Bop (Binop Equiv PropOp) relApp guardDisjunction)
      (ProofBody [Custom . render $ "rel_back'" <+> tacArg])
      Opaque,
    AddHint RewriteHint f_lem GraphRelBackDB
  ]
  where
    f_lem = relBranchLemName $ pathConstrName f (map snd σxs) "inv"
    -- Variable introduced by destructing the arguments
    argsVars = Set.toList $ LH.freeVars (map snd σxs)
    -- Fresh variable for the result of relApp
    res = f_lem ++ "_res"
    relApp = Coq.App (Def $ relDefName f) (map (utrReft eq . snd) σxs ++ [Coq.Var res])
    -- TODO: do we need something else than []?
    guardDisjunction = mkOr $ map (\(σp, rf) -> trPathGuard eq f (σxs, σp, rf) [] (Just res)) guards
    -- argument of the tactic: the translation of the terms destructed in the guards
    tacArg =
      let withPatterns = nub . map fst $ concatMap fst guards
       in maybeParens
            (not $ null withPatterns)
            $ sep (map ((<+> "_::_") . parens . pPrint . utrReft eq) withPatterns)
              <+> "_nil"

-- | Lemma f_rel_ex
-- > Theorem f_rel_ex [args argsp]: f_rel [args] ⌊ f (exist args argsp) -⌋.
-- > #[global] Hint Resolve f_rel_ex : rel_ax_db.
defExLemma :: FuncData -> [Coq.Decl]
-- defExLemma f | traceF "defExLemma" f = undefined
defExLemma f = [exLem, AddHint ResolveHint (exLemName $ name f) RelAxDB]
  where
    exLem =
      Coq.Definition
        (exLemName $ name f)
        (map (,False) $ fst (trRefTypeSplit (equations f) (tpf f)))
        (Prop $ Coq.App (Def . relDefName $ name f) (projArgs f ++ [mkProject $ mkApp (Def $ name f) (injArgs f)]))
        ( ProofBody
            [ mkConcat
                [ Custom $ "existence_lemma_pre " ++ name f,
                  mkIndSkel (equations f) (body f) True,
                  Custom $ "existence_lemma_quicksolve " ++ name f,
                  Custom "f__f_rel_ex_body",
                  Custom "f_rel_finish"
                ]
            ]
        )
        Opaque

-- | Lemma f__f_rel_rw
--
-- > Theorem f__f_rel_rw [args argsp] v: ⌊ f (exist _ args argsp) -⌋ = v <-> f_rel [args] v.
-- > #[global] Hint Rewrite f__f_rel_rw : f_rel_funct_db.
-- > #[global] Hint Resolve f__f_rel_rw : rel_ax_db.
-- > #[global] Instance f_lookup_rw : dictionary rwLem f := { lookup' := f__f_rel_rw }.
refRelRwLemma :: FuncData -> [Coq.Decl]
-- refRelRwLemma f | traceF "refRelRwLemma" f = undefined
refRelRwLemma f =
  [ refRelRwLem,
    AddHint RewriteHint (relDefRwLemName $ name f) GraphRelDB,
    AddHint ResolveHint (relDefRwLemName $ name f) RelAxDB,
    Coq.Instance (name f ++ "_lookup_rw") ["dictionary", "rwLem", name f] [("lookup'", Coq.Def (relDefRwLemName $ name f))]
  ]
  where
    refRelRwLem =
      Coq.Definition
        (relDefRwLemName $ name f)
        (map (,False) $ fst (trRefTypeSplit (equations f) (tpf f)) ++ [(retName f, retUT f)])
        (Prop $ Coq.Bop (Binop Equiv PropOp) defEq relApp)
        (ProofBody [Custom "f__f_rel_rw"])
        Opaque
    -- ⌊ f (exist _ args argsp) -⌋ = f_res
    defEq = Coq.Bop (Binop Coq.RocqEq PropOp) (mkProject $ mkApp (Def $ name f) (injArgs f)) (Coq.Var $ retName f)
    -- f_rel [exist _ args argsp] f_res
    relApp = Coq.App (Def . relDefName $ name f) (projArgs f ++ [Coq.Var $ retName f])

-- | Lemmas f__f_rel and f__f_rel'
--
-- > Theorem f__f_rel [args refined] f_res : ⌊ f [args] -⌋ = f_res <-> (f_rel ⌊ [args] -⌋ f_res).
-- > #[global] Hint Rewrite f__f_rel : f_rel_funct_db.
-- > Theorem f__f_rel' [args_u unrefined] [args refined] f_res : [args_u = proj(args)] -> (⌊ f [args] -⌋ = f_res <-> f_rel [args_u] f_res).
-- > #[global] Hint Resolve f__f_rel' : f_rel_funct_db.
refUnrefLemmas :: FuncData -> [Coq.Decl]
-- refUnrefLemmas f | traceF "refUnrefLemmas" f = undefined
refUnrefLemmas f =
  [ refUnrefLemma,
    Coq.AddHint Coq.RewriteHint (relDefThmName $ name f) Coq.GraphRelDB,
    refUnrefLemma',
    Coq.AddHint Coq.ResolveHint (relDefLemName $ name f) Coq.GraphRelDB
  ]
  where
    argsUT_u = map (first (++ "_u")) (argsUT f)
    params = map (Coq.Var . fst) (argsT f)
    params_u = map (Coq.Var . fst) argsUT_u
    equivalence fuArgs =
      Coq.Bop
        (Binop Coq.Equiv PropOp)
        (Coq.Bop (Binop Coq.RocqEq PropOp) (mkProject $ Coq.App (Coq.Def $ name f) params) (Coq.Var $ retName f))
        (Coq.App (Coq.Def (relDefName $ name f)) $ fuArgs ++ [Coq.Var $ retName f])
    refUnrefLemma =
      mkCoqTheorem
        (relDefThmName $ name f)
        (map (,False) $ argsT f ++ [(retName f, retUT f)])
        (equivalence $ map mkProject params)
        [Coq.Custom "f__f_rel"]
    refUnrefLemma' =
      Coq.Definition
        (relDefLemName $ name f)
        unrLemArgs
        unrLemTp
        ( Coq.ProofBody
            [ Coq.Intros $ replicate (length $ args f) (Coq.RewritePat Coq.RwLR),
              Refine (Coq.App (Coq.Def . relDefThmName $ name f) (params ++ [Coq.Var $ retName f]))
            ]
        )
        Coq.Opaque
      where
        paramsEq =
          zipWith
            (\xiu xi -> Coq.Bop (Binop Coq.RocqEq PropOp) (Coq.Var xiu) (Project (Coq.Var xi)))
            (map fst argsUT_u)
            (map fst $ argsT f)
        unrLemArgs = map (,False) $ argsUT_u ++ argsT f ++ [(retName f, retUT f)]
        unrLemTp = Coq.Prop $ foldr (Coq.Bop $ Binop Coq.Impl PropOp) (equivalence params_u) paramsEq

-- Lemma f_rel_mk
--
-- > Definition f_rel_mk [args argsp] : {f_res: _ | f_rel [args] f_res}.
-- > #[global] Hint Resolve f_rel_mk : f_rel_funct_db.
relMkLemma :: FuncData -> [Coq.Decl]
-- relMkLemma f | traceF "relMkLemma" f = undefined
relMkLemma f = [refRelMkLem, AddHint ResolveHint (relDefMkLemName $ name f) GraphRelDB]
  where
    refRelMkLem =
      Coq.Definition
        (relDefMkLemName $ name f)
        ({- mkOnlyWitnessesExplicit . -} map (,False) . fst . trRefTypeSplit (equations f) $ tpf f)
        relMkRet
        ( ProofBody
            [ mkConcat
                [Intros [], Refine subCast, Rewrite (Just RwRL) (Def . relDefLemName $ name f) Nothing, Easy]
            ]
        )
        Opaque
    relMkRet = Subset (retName f) Hole relApp
    relApp = Coq.App (Def . relDefName $ name f) (vars ++ [Coq.Var $ retName f])
    vars = map (\case (x, ArrType {}) -> Coq.App (Def projPackName) [Coq.Var x]; (x, _) -> Coq.Var x) (args f)
    subCast = SubCast relMkRet (Subset (retName f) Hole TermHole) (mkApp (Def $ name f) (injArgs f)) (TermWitness TermHole)

-- NOTE: I removed this because we currently use trailing implicit for all
-- implicits [], but this does not work if the last argument is higher-order
-- We'll see if this breaks something
{- -- All first-order arguments to the function are implicit, except for witnesses x_p
mkOnlyWitnessesExplicit ((x, utp) : (xp, p) : argsT)
  | xp == subsetWitnessNm x =
      ((x, utp), True) : ((xp, p), False) : mkOnlyWitnessesExplicit argsT
mkOnlyWitnessesExplicit ((x, tp) : argsT) = ((x, tp), True) : mkOnlyWitnessesExplicit argsT
mkOnlyWitnessesExplicit [] = [] -}

-- ** Pack instances

-- Refined pack instances f_pack and f_upack, only created for first-order functions, and not for constants
--
-- > #[global] Instance f_pack : ….
-- > Proof. buildPackG f f_rel f__f_rel f_rel_funct. Defined.
-- > #[global] Instance f_upack : ….
-- > Proof. buildUPackG f_rel f_rel_funct. Defined.
packInstances :: FuncData -> [Coq.Decl]
-- packInstance f | traceF "packInstance" f = undefined
packInstances f =
  [TacInstance (packInstanceName $ name f) (trRefType (equations f) $ tpf f) def | firstOrder, arrowType]
    ++ [TacInstance (upackInstanceName $ name f) (utrRefType $ tpf f) udef | firstOrder, arrowType]
  where
    def = Custom $ unwords ["buildPackG", name f, relDefName $ name f, relDefThmName $ name f, funcHoodLemName $ name f]
    udef = Custom $ unwords ["buildUPackG", relDefName $ name f, funcHoodLemName $ name f]
    firstOrder = all (\case (_, RefType {}) -> True; (_, ArrType {}) -> False) (args f)
    arrowType = case tpf f of ArrType {} -> True; RefType {} -> False

-- ** Utility functions

-- | Generates the nested top-level inductive skeleton tactic used in the functionhood and existence lemma proofs.
--   The flag indicates whether we should specialize induction hypotheses
mkIndSkel :: Bool -> Expr -> Bool -> Tactic
mkIndSkel eq (Case r alts genVars) specIHs =
  let -- we do not print anything for unreacheable branches in the inductive skeleton
      trans Nothing = []
      trans (Just e) = [mkIndSkel eq e specIHs]
   in mkMatching eq trans r alts genVars
-- TODO: handle inductive skeleton of the bound term
mkIndSkel eq (LH.Let _ _ _ e) specIHs = mkIndSkel eq e specIHs
mkIndSkel _ (Reft r) specIhs =
  mkConcat $
    if specIhs
      then Custom "fix_notations" : [poseIHCall call | call <- ihCalls] ++ [Try $ Clear indhyp | indhyp <- allIHs]
      else []
  where
    -- translation of recursive calls
    ihCalls = map (\(indVar, state, args) -> trRecCall (Left indVar) state args) $ findRecCalls r
    -- all induction hypotheses used
    allIHs = map (\(indVar, _, _) -> ihName indVar) $ findRecCalls r
    poseIHCall ihCall = ProofPose ("IH_" ++ hashName ihCall) ihCall

    findRecCalls :: Reft -> [(Id, [DesState], [Reft])]
    findRecCalls (LH.Var _ _ (Recursive indVar state)) = [(indVar, state, [])]
    findRecCalls r'@(LH.App {}) =
      case apps r' of
        (LH.Var _ _ (Recursive indVar state), args) -> [(indVar, state, args)]
        _ -> []
    findRecCalls (LH.Var {}; StringLit {}; IntLit {}; FloatLit {}; DC {}) = []
    findRecCalls (LH.Neg r') = findRecCalls r'
    findRecCalls (LH.Bop _ r1 r2) = findRecCalls r1 `union` findRecCalls r2
    findRecCalls (QMark r' rh rp) = findRecCalls r' `union` (findRecCalls rh `union` findRecCalls rp)
    findRecCalls (Pop _ r1 r2) = findRecCalls r1 `union` findRecCalls r2
    findRecCalls (Sub r' _ _) = findRecCalls r'
    findRecCalls (Inj r' _) = findRecCalls r'
    findRecCalls (Proj r') = findRecCalls r'
