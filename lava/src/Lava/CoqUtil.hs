{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE TupleSections #-}

-- | Utility functions for both the translations ILH -> ECoq and ECoq -> Coq
module Lava.CoqUtil
  ( -- * Names of translation generated declarations and variables
    relDefName,
    relDefLemName,
    relDefThmName,
    funcHoodLemName,
    constrWfName,
    ihName,
    relPostfix,
    relDefBranchName,
    exLemName,
    relDefRwLemName,
    relDefMkLemName,
    relBranchLemName,

    -- * Translating a refined data type to Coq
    transRefTC,
    tcEqName,
    eqReflLemName,
    eqEqbEqLemName,
    leibnitzInstanceName,
    wfLemName,
    psConstrLemName,

    -- * Miscellanious functions
    mkApp,
    mkIsTrue,
    mkForall,
    mkForallT,
    mkFuncType,
    mkConcat,
    assertFresh,
    matchFunctionType,
    matchImplFunctionType,
    projectTm,
    mkCoqTheorem,
    destructSubsetArg,

    -- * Miscellanious functions for the 'TypedTranslations'
    injCast,
    ppForall,
    mkReflAuxDecls,
    mkInductiveSkeleton,
    IndTree (..),
    unrefRocqType,

    -- * Shared code related to Packs
    packName,
    packRelName,
    upackRelName,
    upackFunctName,
    refProjName,
    mkUPackName,
    packInstanceName,
    upackInstanceName,
    uPackWfName,
    packDefName,
    constructProj {- packFFrelName, packFunctName, -},
    toPack,
    toUPack,
    ltacTerm,
    packGetF,
    packGetRel,
    packGetCor,
    packGetFunct,
    upackGetRel,
  )
where

import Data.Bifunctor
import Data.List (intersect, nub, sortBy)
import Data.List.Extra ((\\))
import Data.Tuple.Extra (uncurry3)
import Lava.Coq
import Lava.CoqSyntaxUtil
import Lava.Util

-- * Names of ECoq generated declarations and variables

-- TODO: put them in Declaration

{- ORMOLU_DISABLE -}

constrWfName c x = "wf_" ++ c ++ "_" ++ x
wfLemName tp = tp ++ "_wf_ref"
eqReflLemName tp = tp ++ "_eq_refl"
eqEqbEqLemName tp = tp ++ "_eqb_eq"
leibnitzInstanceName tc = "leibnitz_eq_" ++ tc

relPostfix = "_rel"
relDefName name = name ++ relPostfix
relDefThmName name = name ++ "__" ++ relDefName name
relDefLemName name = relDefThmName name ++ "'"
relDefRwLemName name = name ++ "__" ++ relDefName name ++ "_rw"
exLemName name = name ++ relPostfix ++ "_ex"
relDefMkLemName name = relDefName name ++ "_mk"
funcHoodLemName name = relDefName name ++ "_funct"
relDefBranchName name = name ++ "_def"
relBranchLemName name = name ++ "_lem"

{- ORMOLU_ENABLE -}

ihPrefix = "IH"

ihSpecName :: Id -> Id -> Id
ihSpecName ihNm x =
  if any (`elem` x) "- "
    -- \| x contains an illegal character, so we take the hash instead
    then ihNm ++ "_" ++ hashName x
    else ihNm ++ "_" ++ x

ih :: [Id] -> Id
ih = foldl ihSpecName ihPrefix

ihName :: Id -> Id
ihName ihVar = ih [ihVar]

-- ** names used internally for translation of TCs to Coq

-- mkExistTCName name = name ++ "_mk_ref"
psConstrLemName c = c ++ "_lem"

tcEqName tc = tc ++ "_eq"

{- ORMOLU_DISABLE -}
packDefName = "f_def"
packRelName = "f_rel"
upackRelName = "rel_u"
packFFrelName = "f__f_rel"
packFunctName = "f_funct"
upackFunctName = "funct_u"
mkPackName = "mkPack"
mkUPackName = "mkUPack"
refProjName = "refinement_proj"
packProjName = "packPr_proj"
packInstanceName f = f ++ "_pack"
upackInstanceName f = f ++ "_upack"
uPackWfName = "uPack_wf"
{- ORMOLU_ENABLE -}

-- * Translating a refined data type to Coq

-- | elaborate a refined inductive data type from ECoq to an unrefined data type, a well-formedness predicate, some utility definitions and pseudo-constructors in ECoq
transRefTC :: [Decl] -> Id -> [CoqConstr] -> [Decl]
transRefTC decls' tc constrs = unrefTCDecl : (eqDecl : eqReflLem : eqReflHint : eqbEqLem : eqbEqLemHint : eqbInstanceDecl : tcRefDecls ++ constrDecls ++ constrWfDecls ++ hints) -- ++[rectThm, indThm]
  where
    decls = decls' ++ [unrefTCDecl, TCDecl tc constrs]
    unrefConstr (Constr c tp) = Constr (unrefinedConstrName c) (unrefRocqType tp)
    unrefTCDecl = CoqInductive (unrefinedTCName tc) [] (Sort SetSort) $ map unrefConstr constrs

    mkIntDecl :: Id -> [((Id, RocqType), Bool)] -> RocqType -> Either [CoqTactic] CoqTerm -> Decl
    mkIntDecl g args ret def = Definition g args ret defBody Transparent
      where
        defBody = case def of
          Left tacs -> ProofBody tacs
          Right term -> TermBody term

    xIHs :: [(Id, RocqType)] -> [((Id, RocqType), Bool)]
    xIHs = map isIHArg
      where
        isIHArg arg@(_, rt) = {-trace ("comparing "++tc++" and "++a)-} case rt of
          Subset _ (TC st _) _ -> (arg, st == tc)
          Subset {} -> (arg, False)
          Pack argTps uargTps z t p -> (arg, False)
          _ -> error "Found non normalized constructor type in CoqUtils.wfDecl."
    usedVars = concatMap (\(Constr _ cTp) -> typeArgs cTp) constrs
    indVar = mkFresh "x" usedVars
    p = mkFresh "p" (usedVars ++ [indVar])
    q = mkFresh "q" (usedVars ++ [indVar, p])
    v = mkFresh "v" (usedVars ++ [indVar, p, q])
    z = mkFresh "z" (usedVars ++ [indVar, p, q, v])
    z1 = mkFresh "z1" (usedVars ++ [indVar, p, q, v, z])
    z2 = mkFresh "z2" (usedVars ++ [indVar, p, q, v, z, z1])
    tmV = mkFresh "tm" (usedVars ++ [indVar, p, q, v, z, z1, z2])

    unrefTC = TC tc []
    unrefTCArg = (indVar, unrefTC)
    wfVar var = App (Def $ wfTCName tc) [Var var]

    -- Fixpoint definition of equality of two inductives
    eqDecl :: Decl
    eqDecl = Fix (tcEqName tc) [(("x", unrefTC), False), (("y", unrefTC), False)] boolTp matchExp
      where
        matchExp = Match [Var "x", Var "y"] Nothing (map (mkConstrEqBranch . unrefConstr) constrs ++ [defaultBranch | length constrs > 1])
        mkEq :: RocqType -> CoqTerm -> CoqTerm -> CoqTerm
        -- TODO: we could have an inductive tc' that is not the same one, but for which
        -- we need to use tc'_eq instead of boolean equality (the best would be to
        -- overload boolean equality)
        -- Is it really not possible to expand the boolean equality automatically?
        mkEq tp x x' | unrefRocqType tp == TC tc [] = mkApp (Def $ tcEqName tc) [x, x']
        mkEq _ x x' = Bop EqualB x x'
        mkConstrEqBranch :: CoqConstr -> ([(Id, [Id])], CoqTerm)
        mkConstrEqBranch (Constr c cTp) =
          let cargs = fst $ matchFunctionType [c] cTp
           in ( [(c, map fst cargs), (c, map ((++ "'") . fst) cargs)],
                foldl (\b (x, xTp) -> Bop Andb b (mkEq xTp (Var x) (Var $ x ++ "'"))) btrue cargs
              )
        defaultBranch = ([("_", []), ("_", [])], bfalse)

    eqReflLem :: Decl
    eqReflLem =
      mkCoqLemma
        (eqReflLemName tc)
        []
        (FAType ("x", unrefTC) $ Prop . IsTrue $ App (Def $ tcEqName tc) (map Var ["x", "x"]))
        [Custom "eq_refl"]

    eqReflHint = AddHint ResolveHint (eqReflLemName tc) EqHintDb

    eqbEqLem :: Decl
    eqbEqLem =
      mkCoqLemma
        (eqEqbEqLemName tc)
        []
        ( FAType ("s", unrefTC)
            $ FAType ("t", unrefTC)
              . Prop
            $ Impl (IsTrue $ App (Def $ tcEqName tc) (map Var ["s", "t"])) (Bop Eq (Var "s") (Var "t"))
        )
        [Custom "eqb_eq_lem"]

    eqbEqLemHint = AddHint ResolveHint (eqEqbEqLemName tc) EqHintDb

    eqbInstanceDecl :: Decl
    eqbInstanceDecl = Instance (leibnitzInstanceName tc) ["LeibnitzEqB"] [("equalB'", Def $ tcEqName tc), ("refl'", Def $ eqReflLemName tc), ("eqb_eq'", Def $ eqEqbEqLemName tc)]

    wfDecl =
      Fix (wfTCName tc) [(unrefTCArg, False)] (Sort PropSort) $
        Match
          [Var indVar]
          Nothing
          -- TODO: make something cleaner
          [ ( [(unrefinedConstrName c, map (indPatVarName . fst) cargs)],
              mkAnd (getCase cargs ++ [sub vv (App (Cr $ unrefinedConstrName c) (map (Var . fst) cargs)) crf])
            )
          | (Constr c cTp) <- constrs,
            let (cargs, Subset vv _ (And _ crf)) = matchFunctionType [] cTp
          ]
      where
        getCase :: [(Id, RocqType)] -> [CoqTerm]
        getCase cargs = concatMap argReqs (xIHs cargs')
          where
            cargs' = map subArgs cargs
            subArgs (v, Subset v' vBtp vr) = (v, Subset v vBtp (sub v' (Var v) vr))
            subArgs (v, Pack argTps uargTps z t p) = (v, Pack argTps uargTps z t p)
            argReqs ((_, Subset x _ r), _) = [ref]
              where
                ref = replaceSubterm (IdPat x, True) (Var $ indPatVarName x) r
            argReqs ((f, Pack {}), _) = [App (Def uPackWfName) [Var f]] -- TODO: add required conditions
    tm = (tmV, Subset v unrefTC $ And (wfVar v) (App (Var p) [Var v]))
    wfLem = mkCoqLemma (wfLemName tc) [((p, Arrow unrefTC (Sort PropSort)), True), (tm, False)] (Prop $ App (Def $ wfTCName tc) [Project $ Var tmV]) [destructSubsetArg tmV, Oracle]

    refTcDecl = CoqNewType tc (Subset indVar (TC tc []) (And (App (Def $ wfTCName tc) [Var indVar]) TT))

    mkPseudoConstr :: CoqConstr -> [Decl]
    mkPseudoConstr (Constr c cTp) = [argLem, mkIntDecl c (map (,False) args) ret (Right existTm)]
      where
        (args, ret@(Subset x _ xRef)) = matchFunctionType [c] cTp
        retRef = sub x unrefCrAppl xRef

        argPs = map (projTm decls . Var . fst) args
        unrefCrAppl = App (Def $ unrefinedConstrName c) argPs

        existTm = Exist TermHole unrefCrAppl (TermWitness $ App (Def $ psConstrLemName c) (map (Var . fst) args))
        argLem = mkIntDecl (psConstrLemName c) (map (,False) args) (Prop retRef) (Left lemTacs)
          where
            lemTacs = [Custom "repeat first [split; solver]"]
    {- [SplitB [argTacs] [Easy]]
    argTacs = if null args then Easy else foldr1 (\tac cur -> SplitB [tac] [cur]) argPOPrfs
    destructData :: [(Id, Bool)]
    destructData = map getData (xIHs args) where
      getData ((y, _), b) = (y, b)
    argPOPrfs = map solvePOs destructData where
      solvePOs (_, False) = Oracle -- Apply $ Var y
      solvePOs (y, True) = Apply $ PrfTerm TypeHole (RefWitness $ Var y) -}
    tcRefDecls = [wfDecl, wfLem, refTcDecl]
    constrDecls = concatMap mkPseudoConstr constrs

    constrWfDecls = concatMap mkConstrWf constrs
    mkConstrWf (Constr c cTp) =
      map mkConstrWfArg (filter (isTC . snd) args)
      where
        args = fst $ matchFunctionType [] cTp
        isTC (Subset _ (TC a []) _) = tc == a || isInductTp decls' a
        isTC (Subset {}) = False
        isTC (Pack {}) = False
        mkConstrWfArg (x, xTp) = mkIntDecl (constrWfName c x) (map (,True) argPs ++ [((p, Prop ass), False)]) (Prop goal) (Left constrWfPrf)
          where
            argPs = mapSnd unrefRocqType args
            argPTs = map (Var . fst) args
            unrefCrAppl = App (Def $ unrefinedConstrName c) argPTs
            ass = App (Def $ wfTCName tc) [unrefCrAppl]
            Subset _ (TC a []) _ = xTp
            goal = App (Def $ wfTCName a) [Var x]
            constrWfPrf = [Easy]

    wfConstrHints = (ResolveHint, wfLemName tc, WfDB) : [(UnfoldHint,,WfDB) (wfTCName tc)]
    refConstrHints = map (ResolveHint,) (tcEqName tc : map bindName constrWfDecls) ++ map ((UnfoldHint,) . cConstrNm) constrs

    hints = map (uncurry3 AddHint) $ wfConstrHints ++ map (\(kO, n) -> (kO, n, RefConstrDB)) refConstrHints

-- * Computing the unref relation of a function definition

data IndTree
  = Finish [(Id, [CoqTerm])] [Id]
  | -- | the flag indicates whether the induct represents merely a destruct (true) or an induction tactic
    Induct Id [((Id, CoqDestrPat), IndTree)] Bool
  | Cond CoqTerm [(Id, CoqDestrPat, IndTree)]
  deriving (Show, Eq)

constructProj :: RocqType -> CoqTerm
constructProj (Subset x' xStp xR) = Def refProjName
constructProj (Pack argTps uargTps z t q) = Def packProjName
constructProj rt = error $ "Unsupported: " ++ show rt

toPack :: [(Id, RocqType)] -> RocqType -> RocqType
toPack [] tp = error $ "Cannot create pack for non-function type: " ++ show tp
toPack xTs_ (Subset z' zTp_ pz_) = {- traceFuncRet ["toPack", show xTs, show (Subset z' zTp pz)] $ -} Pack argTps uargTps (argListCorPrf argTps uargTps) zTp p_
  where
    substs = map (\(w, _) -> (removeSuffix "_r" w, projectTm $ Var w)) xTs_
    fixDoubleProj :: (AppSuable a CoqTerm) => a -> a
    fixDoubleProj = replaceSubterms (map (\(w, _) -> ((TermPat (Project (Project (Var w))), True), Project (Var w))) xTs_)
    cleanupSubst substs_ = fixDoubleProj . subst substs_
    xTs = map (\(x, xTp) -> (x, cleanupSubst (filter (\(y, _) -> x /= y) substs) xTp)) xTs_
    zTp = cleanupSubst substs zTp_
    pz = fixDoubleProj $ subst substs pz_
    argTps = ArgListT xTs
    uargTps = UArgListT $ map (unrefRocqType . snd) xTs
    p = mkLam xTs (Lambda z' zTp pz)
    argsNm = "x_" ++ hashName argTps
    v = "v_" ++ argsNm
    p_ = Lambda argsNm (ArgumentList argTps) (Lambda v zTp (PrfTerm Hole (ByTac . Custom $ unwords ["flattenP", showP p, argsNm, v])))

toUPack :: [RocqType] -> RocqType -> RocqType
toUPack [] tp = tp
toUPack xs utp = UPack (UArgListT $ map unrefRocqType xs) (unrefRocqType utp)

-- | Generates the nested top-level inductive skeleton tactic in the functionhood and existence lemma proofs
-- | the flag indicates whether we should specialize ihs
mkInductiveSkeleton :: [(Id, RocqType)] -> IndTree -> Bool -> CoqTactic
mkInductiveSkeleton uArgs indBrs specIhs = {- traceFuncRet ["mkInductiveSkeleton", show uArgs, show indBrs, show specIhs] -} res
  where
    args = map fst uArgs
    res = case indBrs of
      Finish ihAppls ihs -> finishTac ihAppls ihs
      Cond tm caseBrs -> if unrefinedHeuristic tm caseBrs then Destruct tm $ map (\(c, pat, caseBr) -> (c, (pat, [recurse caseBr]))) caseBrs else Concat []
      Induct x xIndBrs' b -> Concat $ [GeneralizeDependent (reverse $ args \\ [x]) | not (null $ args \\ [x])] ++ [matchTac (Var x) xBranches, Intros [], Branches $ map recurse otherBrs]
        where
          matchTac = if b then Destruct else Induction
          xIndBrs = sortBy ordFunc xIndBrs'
          xBranches = map (second (,[]) . fst) xIndBrs
          otherBrs = map snd xIndBrs
      where
        finishTac ihAppls ihs = Concat $ [Custom "fix_notations" | specIhs] ++ [poseIHAppl $ App (Var ih) ts | specIhs, (ih, ts) <- ihAppls] ++ [Try $ Clear ih | specIhs, ih <- ihs]

        unrefinedHeuristic Var {} _ = True
        unrefinedHeuristic Def {} _ = True
        unrefinedHeuristic Cr {} _ = True
        unrefinedHeuristic (Bop _ s t) caseBrs = unrefinedHeuristic s caseBrs && unrefinedHeuristic t caseBrs
        unrefinedHeuristic (IsTrue tm) caseBrs = unrefinedHeuristic tm caseBrs
        unrefinedHeuristic (App tm ts) caseBrs = all (`unrefinedHeuristic` caseBrs) $ tm : ts
        unrefinedHeuristic _ _ = specIhs

        ordFunc :: ((Id, CoqDestrPat), IndTree) -> ((Id, CoqDestrPat), IndTree) -> Ordering
        ordFunc ((c1, _), _) ((c2, _), _) = compare c1 c2

        recurse :: IndTree -> CoqTactic
        recurse (Finish ihAppls ihs) = finishTac ihAppls ihs
        recurse (Cond tm caseBrs) = if unrefinedHeuristic tm caseBrs then Destruct tm $ map (\(c, pat, caseBr) -> (c, (pat, [recurse caseBr]))) caseBrs else Concat []
        recurse (Induct y brs' b') = Concat [indTac (Var y) yBranches, Intros [], Branches $ map recurse otherBrs]
          where
            indTac = if b' then Destruct else Induction
            brs = sortBy ordFunc brs'
            otherBrs = map snd brs
            yBranches = map (second (,[]) . fst) brs

-- | Generates various utility lemmata and hints after the declaration marking a reflected definition opaque
mkReflAuxDecls :: Id -> (Id, RocqType) -> [(Id, RocqType)] -> [(Id, RocqType)] -> [CoqTerm] -> [(Id, RocqType)] -> IndTree -> [Decl]
mkReflAuxDecls f retArg rArgs uArgs conds branches indBrs =
  -- For an arrow type (x_i: R_i)_{i ≤ n} -> R@{x:B | rx}:
  -- retArg = (x, TtoR(R))
  -- rArgs = (xi_r: TtoR(R_i))_{i ≤ n}
  -- uArgs = (x_i: TtoU(R_i))_{i ≤ n}
  {- trace (unwords ["mkReflAuxDecls", f, show retArg, show rArgs, show uArgs, show conds, show branches, show indBrs]) $ -}
  [exLem, exLemHint, refRelRwLem, refRelRwHint, refRelRwAuxHint, refRelMkLem, refRelMkLemHint]
    ++ [packInstance | not (null uArgs)]
    ++ relConstrLems
  where
    -- args = (x_i: cqTp)_{i ≤ n}
    -- where cqTp = TtoR(R_i) if R_i is an arrow and cqTp = TtoU(R_i) otherwise
    args = zipWith rArgIfUpack rArgs uArgs
    rArgIfUpack x_r (x, UPack {}) = (x, snd x_r)
    rArgIfUpack _ arg = arg
    -- vars = (packProj(x_i) if HO or x_i if FO)_{i ≤ n}
    vars = map (\case (g, Pack {}) -> App (Def projPackName) [Var g]; (x, _) -> Var x) args

    -- \| the refinement witnesses for the rArgs
    -- xiPs = (Just (y_p^i: r_i) if R_i = {y:_|r_i} or Nothing if R_i is HO)_{i ≤ n}
    xiPs = map getWit rArgs
      where
        getWit (_, rt) = case rt of
          Subset y _ r -> Just (subsetWitnessNm y, Prop r)
          _ -> Nothing -- error $ show rt -- | In this case we have a higher-order argument to a reflected function, this will be tricky
          -- \| the existential combining the uArgs with their refinement witnesses
          -- returns the injected version of each parameter: x_i if HO (already refined),
          -- or exist _ x_i x_i_p if FO (because splitted)
    injArgs = zipWith3 (\x (xr, _) -> \case Just (xp, _) -> Exist TermHole x (TermWitness $ Var xp); Nothing -> Var $ removeSuffix "_r" xr) vars rArgs xiPs

    relApp = App (Def $ relDefName f) (vars ++ [Var v])
    (v, _) = retArg
    retArgU = (v, unrefRocqType $ snd retArg)

    refRelRwLem = mkCoqTheorem (relDefRwLemName f) (map (,False) (args ++ catMaybes xiPs ++ [retArgU])) (Equiv (Bop Eq (Project $ mkApp (Def f) injArgs) (Var v)) relApp) [Custom "f__f_rel_rw"]

    relMkRet = Subset v Hole relApp
    refRelMkLem = mkCoqLemma (relDefMkLemName f) (map (,True) args ++ mapMaybe ((,False) <$>) xiPs) relMkRet [Concat [Intros [], Refine (SubCast relMkRet (Subset v Hole TermHole) (mkApp (Def f) injArgs) (TermWitness TermHole)), Rewrite (Just RwRL) (Def $ relDefLemName f) Nothing, Easy]]

    exLem =
      mkCoqTheorem
        (exLemName f)
        (map (,False) (args ++ catMaybes xiPs))
        (App (Def $ relDefName f) (vars ++ [Project $ mkApp (Def f) injArgs]))
        [ Concat
            [ Custom $ "existence_lemma_pre " ++ f,
              mkInductiveSkeleton uArgs indBrs True,
              Custom $ "existence_lemma_quicksolve " ++ f,
              Custom "f__f_rel_ex_body",
              Custom "f_rel_finish"
            ]
        ]

    relConstrLemmas :: [Decl]
    relConstrLemmas = mkRelBranchLemmas args retArgU univArgs univAxs conds' branches
      where
        matchAxs :: CoqTerm -> ([(Id, RocqType, RocqType)], CoqTerm)
        matchAxs (Forall [(z, zTp)] (Impl zDefTp p)) = first ((z, zTp, Prop zDefTp) :) $ matchAxs p
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

    [exLemHint, refRelRwHint, refRelRwAuxHint, refRelMkLemHint] = map (uncurry3 AddHint) [(ResolveHint, exLemName f, RelAxDB), (RewriteHint, relDefRwLemName f, GraphRelDB), (ResolveHint, relDefRwLemName f, RelAxDB), (ResolveHint, relDefMkLemName f, GraphRelDB)]
    -- \| relConstrLemmas interspaced with the corresponding hints
    relConstrLems = concatMap (\lem -> [lem, AddHint RewriteHint (bindName lem) GraphRelBackDB]) relConstrLemmas
    packInstance =
      TacInstance
        (packInstanceName f)
        (show pack)
        (Custom $ unwords ["\n\tbuildPackG", f, relDefName f, relDefThmName f, funcHoodLemName f] ++ ". ")
      where
        rfRetArg : rfArgs = retArg : rArgs
        pack = toPack rfArgs (snd rfRetArg)

mkRelBranchLemmas :: [(Id, RocqType)] -> (Id, RocqType) -> [(Id, RocqType)] -> [(Id, RocqType)] -> [CoqTerm] -> [(Id, RocqType)] -> [Decl]
mkRelBranchLemmas args retArg univArgs univAxs conds branches = {- traceFuncRet ["mkRelBranchLemmas", show args, show retArg, show univArgs, show univAxs, show conds, show branches] $ -} map mkBackwardsReasoningLemma univVarsClasses
  where
    -- \| a list of branches with the (nested) implication in the result unfolded into a list of antecedents and a final consequent
    deconstrBranches :: [(Id, [(Id, RocqType)], ([CoqTerm], CoqTerm))]
    deconstrBranches = map deconstrConstr branches
    -- mapThd
    --   ( \(Prop implRes) ->
    --       first (\\ map (\(_, Prop def) -> def) univAxs) $ matchImplProp implRes
    --   )
    --   branches
    deconstrConstr :: (Id, RocqType) -> (Id, [(Id, RocqType)], ([CoqTerm], CoqTerm))
    deconstrConstr (c, cTp) =
      let (cargs, cret) = matchFunctionType [] cTp
       in case cret of
            Prop implRes -> (c, cargs, first (\\ map (\(_, Prop def) -> def) univAxs) $ matchImplProp implRes)
            _ -> error "Prop expected as a return of branch in mkRelBranchLemmas"
    -- \| a list of triples of the result of a branch with fresh unification variables instead of the actual variables, the substitutions (represented as pairs of names) for the unification variables and the branch itself (with the variables substitutes to the unification variables in antecedent and result)
    univVarsBranches :: [(CoqTerm, [(Id, Id)], (Id, [(Id, RocqType)], [CoqTerm], CoqTerm))]
    univVarsBranches = map mkUnivVarBranch deconstrBranches
      where
        mkUnivVarBranch :: (Id, [(Id, RocqType)], ([CoqTerm], CoqTerm)) -> (CoqTerm, [(Id, Id)], (Id, [(Id, RocqType)], [CoqTerm], CoqTerm))
        mkUnivVarBranch (f_c, brArgs, (antes, res)) = {-traceFuncRet ["mkUnivVarBranch", show (f_c, brArgs, (antes, res))] $ -} (resUnivVars, univSubst, (f_c, brArgs' ++ relDefArgs, antes' \\ relDefAntes, res'))
          where
            (resUnivVars, univSubst, _) = mkUnivVars 0 res
            substUniv = map (\(x, y) -> (y, Var x)) univSubst
            antes' = map (subst substUniv) antes
            isRelDef (App frel ts@(_ : _)) = case last ts of
              fres@Var {} | fres `elem` map (subst substUniv . Var . fst) (brArgs ++ univArgs) && relPostfix `isSuffixOf` show frel -> True where
              _ -> False
            isRelDef _ = False
            relDefAntes = filter isRelDef antes'
            relDefArgs = map (\r -> ("h_" ++ hashName r, Prop r)) relDefAntes
            res' = subst substUniv res
            brArgs' = mapSnd (subst substUniv) brArgs
            isLit (StringLiteral _) = True
            isLit (IntLiteral _) = True
            isLit (FloatLiteral _) = True
            isLit _ = False
            isInert lit | isLit lit = True
            isInert (Cr lit) | lit `elem` [btrueTmName, bfalseTmName, unitTmName] = True
            isInert (Cr _) = True
            isInert (Def _) = True
            isInert _ = False
            mkUnivVars :: Integer -> CoqTerm -> (CoqTerm, [(Id, Id)], Integer)
            mkUnivVars i (Var v) = (Var $ "x_" ++ show (i + 1), [("x_" ++ show (i + 1), v)], i + 1)
            mkUnivVars i (App c ts) | isInert c = (App c ts', substs, j)
              where
                acc (prevTs', prevSubsts, k) t = (prevTs' ++ [t'], prevSubsts ++ newSubsts, l)
                  where
                    (t', newSubsts, l) = mkUnivVars k t
                (ts', substs, j) = foldl acc ([], [], i) ts
            mkUnivVars i atom | isInert atom = (atom, [], i)
            mkUnivVars i (Bop op s t) = (Bop op s' t', sSubsts ++ tSubsts, k)
              where
                (s', sSubsts, j) = mkUnivVars i s
                (t', tSubsts, k) = mkUnivVars j t
            mkUnivVars i (Project t) = (Project t', tSubsts, j)
              where
                (t', tSubsts, j) = mkUnivVars i t
            mkUnivVars _ other = error $ "unexpected term " ++ showP other ++ " in mkUnivVars."

    -- \| a list of equivalence classes of univVarsBranches with same first components (i.e. resulting relations of same shape)
    univVarsClasses :: [(CoqTerm, [([(Id, Id)], (Id, [(Id, RocqType)], [CoqTerm], CoqTerm))])]
    univVarsClasses = cls
      where
        mergedUnivBrs = map mergeBrs univVarsBranches
        mergeBrs :: (CoqTerm, [(Id, Id)], (Id, [(Id, RocqType)], [CoqTerm], CoqTerm)) -> (CoqTerm, [(Id, Id)], (Id, [(Id, RocqType)], [CoqTerm], CoqTerm))
        mergeBrs (univRes'@(App rel ts), sbst, br@(n, bargs, baxs, resTm)) = res
          where
            univConds = mapMaybe univCond otherBrs
            res = case univConds of
              [] -> (univRes', sbst, br)
              _ -> {- traceFuncRet ["commonBArgs:", show commonBArgs, "\naltBArgs:", show altBArgs, "\nconjConds:", show conjConds, "\ndisjArg:", show disjArg, "\nmergeBrs", show (univRes', sbst, br)] -} (univRes', sbst, (n, commonBArgs ++ [disjArg], baxs, resTm))
            otherBrs = filter ((univRes', sbst, br) /=) univVarsBranches
            commonBArgs = bargs \\ concatMap snd3 univConds
            altBArgs = [mapSnd (\case (Prop p) -> p) (rmArgs \\ commonBArgs) ++ newArgs | (rmArgs, _, newArgs) <- univConds]
            conjConds = map (mkAnd . map snd) $ mapSnd (\case (Prop p) -> p) (bargs \\ commonBArgs) : altBArgs
            disjArg = (\t -> ("h_" ++ hashName t, Prop t)) $ mkOr conjConds

            univCond other@(App rel' ts', sbst', br') | rel' /= rel = Nothing
            -- ToDo: generalize by removing the assumptions imposed by the subsequent two lines
            -- univCond other@(App rel' ts', sbst', br') | not (sbst' `isInfixOf` sbst) = Nothing
            -- univCond other@(App rel' ts', sbst', br'@(_,oArgs,oAxs,_)) | not (oAxs `isInfixOf` baxs) = Nothing
            univCond other@(App rel' ts', sbst', br'@(_, oArgs, oAxs, _)) = {- traceFuncRet ["univCond", show (univRes', sbst, br), "\nand\n", show other, if not (null mergeSubstsO) then unwords ["\nwith", "nonConflicting:", show nonConflicting, "\nextraConds:", show extraConds, "\nmatchConds:", show matchConds] else ""] -} resConds
              where
                resConds = if null mergeSubstsO || ts == ts' then Nothing else Just (nonConflicting, conflicting, extraConds ++ map (\t -> ("h_" ++ hashName t, t)) matchConds)
                -- missingSbst = sbst' \\ sbst

                mergeSubstsO = mergeSubst ts ts'
                mergeSubst [] [] = Just []
                mergeSubst (tm : xs) (tm' : ys) | tm == tm' = mergeSubst xs ys
                mergeSubst ((Var uniVar) : xs) (tm : ys) = ((Var uniVar, tm) :) <$> mergeSubst xs ys
                mergeSubst (tm : xs) ((Var uniVar') : ys) | (\case Var {} -> False; _ -> True) tm = ((tm, Var uniVar') :) <$> mergeSubst xs ys
                mergeSubst _ _ = Nothing
                extraSbst = sbst \\ sbst'
                backSubsts = [(v, tm) | (uniVar, v) <- extraSbst, (Var uniVar', tm) <- fromJust mergeSubstsO, uniVar == uniVar']
                univSubst' = [(uniVar', tm) | (tm, Var uniVar') <- fromJust mergeSubstsO, (\case Var {} -> False; _ -> True) tm]
                substConds = [Bop Eq (Var u) (Var v) | (uniVar, u) <- sbst, (uniVar', v) <- sbst', uniVar == uniVar', u /= v]
                matchConds = map (\(v, tm) -> Bop Eq (Var v) tm) backSubsts
                extraConds' = mapMaybe (\case (n_p, Prop p) -> Just (n_p, subst univSubst' p); _ -> Nothing) $ oArgs \\ bargs
                backRepl = foldl (.) id $ map (\(v, tm) -> replaceSubterm (TermPat tm, True) (Var v)) backSubsts
                extraConds = mapSnd backRepl extraConds' ++ map (\t -> ("h_" ++ hashName t, t)) substConds
                haveNoConflict :: CoqTerm -> CoqTerm -> Bool
                haveNoConflict (IsTrue (Bop EqualB matchedTm cApp)) (IsTrue (Bop EqualB matchedTm' cApp')) | matchedTm == matchedTm' = cApp == cApp'
                haveNoConflict (Bop Eq (Bop EqualB matchedTm cApp) (Cr "true")) (Bop Eq (Bop EqualB matchedTm' cApp') (Cr "true")) | matchedTm == matchedTm' = cApp == cApp'
                haveNoConflict (Bop Eq p (Cr "true")) (Bop Eq (Neg p') (Cr "true")) | p == p' = False
                haveNoConflict (Bop Eq (Neg p') (Cr "true")) (Bop Eq p (Cr "true")) | p == p' = False
                haveNoConflict (IsTrue p) (IsTrue (Neg p')) | p == p' = False
                haveNoConflict (Bop Eq (Neg p') (Cr "true")) (Bop Eq p (Cr "true")) | p == p' = False
                haveNoConflict p (Neg p') | p == p' = False
                haveNoConflict (Neg p') p | p == p' = False
                haveNoConflict (Bop Eq p (Cr "true")) (Bop Eq (App neg [p']) (Cr "true")) | neg == Def negb && p == p' = False
                haveNoConflict (Bop Eq (App neg [p']) (Cr "true")) (Bop Eq p (Cr "true")) | neg == Def negb && p == p' = False
                haveNoConflict p q = {- traceFuncRet ["haveNoConflict", show p, show q] -} True
                nonConflicting = filter (\case (_, Prop p) -> all (\case (_, q) -> haveNoConflict p q; _ -> True) extraConds; _ -> True) bargs
                conflicting = bargs \\ nonConflicting
            univCond (shape, sbst', br') = trace ("other branch has invalid shape: " ++ show shape ++ ". ") Nothing
        -- \| univVarBranches with branches of same result shape "merged" into one equivalence class
        cls = [(univRes, [(sbst, br) | (univRes', sbst, br) <- mergedUnivBrs, univRes' == univRes]) | univRes <- nub $ map fst3 mergedUnivBrs]

    mkBackwardsReasoningLemma :: (CoqTerm, [([(Id, Id)], (Id, [(Id, RocqType)], [CoqTerm], CoqTerm))]) -> Decl
    mkBackwardsReasoningLemma (univRes, branchs) =
      {- traceFuncRet ["mkBackwardsReasoningLemma", show (univRes, branchs), show conds] $ -}
      Definition
        lemName
        (map (,False) (commonUnivArgs ++ univArgs ++ univAxs ++ commonBrArgs ++ [(uv, Hole) | uv <- uncommonUnivVars]) ++ [(resArg, False) | resIsTm])
        (Prop $ Equiv relCApp (mkExists commonExistArgs disjuncts))
        (ProofBody [Custom $ "rel_back' " ++ addParens (unwords (map (++ " _::_") . nub . map showCond $ conds) ++ " _nil")])
        Opaque
      where
        isCrAppl (Cr c) = c `notElem` [btrueTmName, bfalseTmName]
        isCrAppl cAppl@(App Cr {} _) = True
        isCrAppl _ = False

        showCond :: CoqTerm -> String
        showCond (Forall [] tm) = showCond tm
        showCond (Exists [] tm) = showCond tm
        showCond (IsTrue (Bop EqualB tm cAppl)) | isCrAppl cAppl = showP tm
        showCond (Bop Eq (Bop EqualB tm cAppl) (Cr "true")) | isCrAppl cAppl = showP tm
        showCond (Bop Equal tm cAppl) | isCrAppl cAppl = showP tm
        showCond (IsTrue t) = showCond t
        showCond tm = showP tm

        globalVars = map fst (commonUnivArgs ++ univArgs ++ commonBrArgs)
        App _ univResVars = univRes
        sbsts = concatMap fst branchs

        uncommonUnivVars = nub $ [uv | Var uv <- univResVars, sbstBrs1 <- map fst branchs, (uv1, res1) <- sbstBrs1, uv == uv1, sbstBrs2 <- map fst branchs, (uv2, res2) <- sbstBrs2, uv1 == uv2, res1 /= res2, null $ [(res1, res2), (res2, res1)] `intersect` (sbstBrs1 ++ sbstBrs2), not (all (== res2) [res' | (uv', res') <- sbsts, uv1 == uv', res' /= res1] && res1 `elem` globalVars && res2 `elem` globalVars)]

        -- \| those commonResSubsts that are shared amongst all branchs
        commonResSubsts' = nub [(univVar, u) | substs <- map fst branchs, (univVar, u) <- substs {-, univVar `notElem` uncommonUnivVars-}]
        commonResSubsts = nub [(univVar, u) | (univVar, u) <- commonResSubsts', all (\(uV, w) -> not (univVar == uV && u /= w) || any (\(uV', w') -> w' == w && (uV' < uV)) commonResSubsts') commonResSubsts']
        commonResVars = nub [u | (_, u) <- commonResSubsts]
        -- \| the commonResVars with their types
        commonResArgs :: [(Id, RocqType)]
        commonResArgs = nub [(u, wTp) | u <- commonResVars, (w, wTp) <- concatMap ((\(_, brArgs, _, _) -> brArgs) . snd) branchs, u == w]
        brArgs = map (\(_, (_, ags, _, _)) -> ags) branchs
        freeVars (Var w) = [w]
        freeVars (Def _; Cr _; IntLiteral _; TT; FF) = []
        freeVars (App f ts) = nub $ freeVars f ++ concatMap freeVars ts
        freeVars (Bop _ s t) = nub $ freeVars s ++ freeVars t
        freeVars (And s t) = nub $ freeVars s ++ freeVars t
        freeVars (Or s t) = nub $ freeVars s ++ freeVars t
        freeVars (IsTrue t) = freeVars t
        freeVars TT = []
        freeVars FF = []
        -- \| no other cases can actually occur inside relations
        freeVars other = error $ "Unexpected term inside body of backwards reasoning lemma: " ++ show other
        inScope = all (`elem` map fst (commonUnivArgs ++ univArgs)) . freeVars . substitute
        commonBrArgs = [second substitute arg | arg@(_, Prop p) <- head brArgs, (\case App {} -> True; other -> other `elem` conds {-(Bop Eq (Bop EqualB Var{} Cr{}) (Cr "true")) -> True; (Bop Eq (Bop _ Var{} (App Cr{} _)) (Cr "true")) -> True; (Bop Eq _ Cr{}) -> True; (Bop Eq _ (App Cr{} _)) -> True;-}; _ -> False) p, all (arg `elem`) brArgs, inScope p]
        univBranches = map mkUnivBranch branchs
        substitute :: (Suable a CoqTerm) => a -> a
        substitute = subst $ mapSnd Var commonResSubsts
        resRelAppl = substitute univRes

        mkUnivBranch :: ([(Id, Id)], (Id, [(Id, RocqType)], [CoqTerm], CoqTerm)) -> ([(Id, RocqType)], [CoqTerm], [CoqTerm])
        mkUnivBranch (substs, (_, brArgs, antes, _)) = (brArgs' \\ commonResArgs, univConds, antes')
          where
            univConds = [Bop Eq (Var u) (Var w) | (wV, w) <- commonResSubsts, (uV', u) <- substs, wV == uV', w /= u] ++ [Bop Eq (Var uv) (Var v) | uv <- uncommonUnivVars, (uv2, v) <- substs, uv == uv2]
            brArgs' = mapSnd substitute brArgs
            antes' = map substitute antes
        f_cs = map (\(_, (fc, _, _, _)) -> fc) branchs
        f_prefix =
          {- trace ("\nunivRes: " ++ show univRes ++ ", \nbranchs: " ++ show branchs ++ ", \ncommonResVars: " ++ show commonResVars ++ ", \ncommonResSubsts': " ++ show commonResSubsts' ++ ", \ncommonResSubsts: " ++ show commonResSubsts ++ ", \nresRelAppl: " ++ show resRelAppl) $ -}
          head . split '_' $ head f_cs
        lemName = relBranchLemName $ f_prefix ++ concatMap (removePrefix f_prefix) f_cs

        v = fst retArg
        isVar = \case Var _ -> True; Def _ -> True; _ -> False
        isCAppl = \case Cr {} -> True; (App Cr {} _) -> True; _ -> False
        App rel indeces = resRelAppl
        resTm = last indeces
        -- if resTm is already an axiomatized variable, there is a point in creating another variable for it
        -- also resTm doesn't contain any bound variables, so it is fully determined by inverting relCApp
        resIsTm =
          not (isVar resTm)
            && not (isCAppl resTm)
            && not
              ( any
                  ( any (\bdVar -> hasMatch (TermPat . Var $ fst bdVar, True) resTm)
                      . (\(vars, _, _) -> filter (\arg -> any (hasMatch (TermPat . Var $ fst arg, True)) indeces) vars)
                  )
                  univBranches
              )

        resArgV = mkFresh "res" (map fst (args ++ commonResArgs ++ concatMap fst3 univBranches) ++ [v])
        relCApp = App rel (init indeces ++ [if resIsTm then Var resArgV else resTm])

        occurs w = hasMatch (TermPat $ Var w, True)
        commonExistArgs = [arg | arg@(w, _) <- commonResArgs, occurs w resTm, not (any (occurs w) $ init indeces), resIsTm, all ((/=) w . fst) univArgs]
        commonUnivArgs = commonResArgs \\ commonExistArgs
        resArg = (resArgV, snd retArg)

        disjuncts = mkOr $ map mkDisjuncts univBranches

        mkDisjuncts :: ([(Id, RocqType)], [CoqTerm], [CoqTerm]) -> CoqTerm
        mkDisjuncts (vars, univConds, antes) = {- traceFuncRet ["mkDisjuncts", show vars, show univConds, show antes] -} disjRes
          where
            isPreCond = all (`elem` globalVars) . freeVars
            boundVars = filter (\arg -> any (hasMatch (TermPat . Var $ fst arg, True)) indeces) vars
            existVars' = filter (\arg -> arg `notElem` boundVars && all ((/=) (fst arg) . fst) (univArgs ++ commonBrArgs)) vars
            propArgs = filter (\case (_, Prop p) -> True; _ -> False) (vars \\ commonBrArgs)
            existVars = existVars' \\ propArgs
            conjs' = map (\(_, Prop p) -> p) propArgs ++ univConds ++ antes
            preConjs = filter isPreCond conjs'
            postConjs = conjs' \\ preConjs
            isDefConj exVar (App rel ts) = case last ts of
              Var exV ->
                (exV == exVar)
                  || exV `elem` uncommonUnivVars && any (\(Bop Eq (Var uv) (Var w)) -> uv == exV && w == exVar) univConds
              _ -> False
            isDefConj _ _ = False

            mkExists' [] conjs = mkAnd conjs
            mkExists' [(_, Prop p)] [Cr "true"] = p
            mkExists' (arg@(h, Prop p) : tl) conjs = And p (mkExists' tl conjs)
            mkExists' (arg@(h, _) : tl) conjs = Exists [arg] $ case find (isDefConj h) conjs of
              Just conj -> And conj (mkExists' tl $ conjs \\ [conj])
              Nothing -> mkExists' tl conjs
            existTm = mkExists' existVars postConjs
            disjRes = mkAnd $ preConjs ++ [Bop Eq (Var resArgV) resTm | resIsTm] ++ [existTm]

-- | Concat the tactics but remove Oracle tactics, until the very end of the script
mkConcat :: CoqTactic -> CoqTactic -> CoqTactic
mkConcat t1 t2 = Concat $ t ++ [t2]
  where
    t = go t1
    go tc = case tc of
      Oracle {} -> []
      Concat ts -> concatMap (filter notOracle . go) ts
      other -> [other]
    notOracle Oracle {} = False
    notOracle _ = True

lookupTc :: Id -> [Decl] -> Maybe CoqTermTC
lookupTc a [] = trace ("Cannot find " ++ a ++ " in decls. ") Nothing
lookupTc a (d : tl) = case d of
  TCDecl a' constrs -> if a == a' {-trace ("Found ind data declaration: "++a) $-} then Just (InductiveData a' constrs) else lookupTc a tl
  _ -> lookupTc a tl

-- | projects a refined ECoq 'CoqTerm' to its unrefined value
projectTm :: CoqTerm -> CoqTerm
projectTm tm = case tm of
  Project t -> t
  Exist _ t _ -> t
  SubCast _ _ t _ -> projectTm t
  Cr c | isJust (stripSuffixO (unrefinedConstrName "") c) -> Cr c
  Cr c -> Cr (unrefinedConstrName c)
  App (Def projPackN) [Var g] | projPackName == projPackN -> tm
  App (Cr c) args | isJust (stripSuffixO (unrefinedConstrName "") c) -> App (Cr c) (map projectTm args)
  App (Cr c) args -> App (Cr . unrefinedConstrName $ c) (map projectTm args)
  {-
  Def f -> Def (redDefName f)
  App (Def f) args -> App fUnref (map projectTm args) where
    fUnref = Def $ redDefName f -}
  other -> Project other

-- | projects a refined ECoq 'CoqTerm' to its unrefined value, projects applications of a refined constructor to applications of the unrefined version of the constructor to the projections of its arguments
projTm :: [Decl] -> CoqTerm -> CoqTerm
projTm decls tm = case tm of
  (Cr c) | isJust (stripSuffixO (unrefinedConstrName "") c) -> Cr c
  Def c | isJust $ lookupTermBind c filteredDecls -> Cr (unrefinedConstrName c)
  App (Def c) args | isJust $ lookupTermBind c filteredDecls -> mkApp (Cr . unrefinedConstrName $ c) (map projectTm args)
  Def c | isJust $ lookupTermBind (unrefinedConstrName c) decls -> Cr (unrefinedConstrName c)
  App (Def c) args | isJust $ lookupTermBind (unrefinedConstrName c) decls -> mkApp (Cr . unrefinedConstrName $ c) (map projectTm args)
  _ -> projectTm tm
  where
    filteredDecls = filter (\case TCDecl {} -> True; _ -> False) decls

-- * Miscellaneous functions

getStRef :: RocqType -> Id -> (RocqType, CoqTerm)
getStRef (Subset x tp r) y = (tp, sub x (Var y) r)

destructSubsetArg :: Id -> CoqTactic
destructSubsetArg x = DestructSubsetTerm (Var x) (ConjDestrPat [SingleIdPat x, SingleIdPat $ subsetWitnessNm x])

unrefRocqType :: RocqType -> RocqType
unrefRocqType tp@(Builtin _) = tp
unrefRocqType tp@(Sort _) = tp
unrefRocqType (Subset _ tp _) = unrefRocqType tp
unrefRocqType (TC tc args) = TC tc (map unrefRocqType args)
unrefRocqType (Arrow tp1 tp2) = Arrow (unrefRocqType tp1) (unrefRocqType tp2)
unrefRocqType (FAType (_, tpx) tp) = Arrow (unrefRocqType tpx) (unrefRocqType tp)
-- \| trivialize proof obligation
unrefRocqType (Prop _) = TC "Unit" []
unrefRocqType tp@(UPack {}) = tp
unrefRocqType (Pack argTps uargTps z t q) = UPack uargTps t
unrefRocqType Hole = Hole

-- TODO: why is it different for TCDecl and CoqInductive?
lookupTermBind :: Id -> [Decl] -> Maybe (Id, RocqType)
lookupTermBind _ [] = Nothing
lookupTermBind n decls@(_ : _) = {- trace (unwords ["lookupTermBind", n, "..."]) $ -} go decls
  where
    go [] = Nothing
    go [decl] = {- trace (unwords ["go (in lookupTermBind)", n, "[" ++ show decl ++ "]"]) $ -} case decl of
      TCDecl _ constrs ->
        let lookupConstrBind (Constr c cTp) = (c, cTp)
         in lookupConstrBind <$> find (\(Constr c _) -> c == n) constrs
      Definition f args ret _ _ | f == n -> Just (f, mkFuncType (map fst args) ret)
      CoqAxiom ax args ret | ax == n -> Just (ax, mkFuncType (map fst args) ret)
      CoqInductive a _ _ constrs ->
        (\(Constr c cTp) -> (c, cTp)) <$> find (\(Constr _ tp) -> baseRetTp tp == a) constrs
      _ -> Nothing
    go (hd : tl) = case go [hd] of
      Just specs -> Just specs
      Nothing -> go tl

isInductTp :: [Decl] -> Id -> Bool
isInductTp decls a = isJust indTp || isJust builtinIndTp
  where
    indTp = a `lookupTc` decls
    builtinIndTp = find ((a ==) . fst3) coqBuiltinInductDataTypes

assertFresh :: Goal -> CoqTactic -> CoqTactic
assertFresh g tac = case tac of
  Concat [t] -> assertFresh g t
  Exact tm -> ProofPose hypName tm
  Refine tm -> ProofPose hypName tm
  _ -> Assert hypName g tac
  where
    hypName = "H_" ++ hashName g

poseIHAppl :: CoqTerm -> CoqTactic
poseIHAppl ihAppl = ProofPose hypName ihAppl
  where
    hypName = "IH_" ++ hashName ihAppl

-- * Miscellaneous functions for 'TypedTranslations'

injCast :: RocqType -> CoqTerm -> Maybe CoqTactic -> CoqTerm
injCast rt tm pO = Exist (Lambda "x" (unrefRocqType rt) ref) tm prfTm
  where
    ref = case rt of
      Subset {} -> snd $ getStRef rt "x"
      _ -> TermHole -- we might as well give up now, unless pO is defined, there is no way for Coq to figure out to what type to cast here
    prfTm = case pO of
      Just tac -> ByTac tac
      Nothing -> ProofHole Nothing

-- | models the totally weird ppForall operator in the Rocq grammar
ppForall :: Id -> RocqType -> (Id, [CoqTerm]) -> CoqTerm -> CoqTerm
ppForall z zTp (f, ts) p = Forall [(z, zTp)] $ Impl (App (Def f) ts) p
