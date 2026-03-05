{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE TupleSections #-}

module Lava.Temporary where

import Data.Bifunctor (bimap, first, second)
import Data.Either (isLeft)
import Data.List ((\\))
import Data.Maybe (catMaybes)
import qualified Data.Set as Set
import Lava.Calculus as LH
import Lava.Coq as Coq
import Lava.CoqSyntaxUtil (mkAnd, mkVarDestrPat, mkVarDestruct)
import Lava.CoqUtil
import Lava.Translation
import Lava.TypingEnvironment as TypEnv hiding (map)
import Lava.Util (freshVar)

{- -- | Inversion lemmas for the graph relation, one for each branch
relConstrLems :: Id -> RefType -> [Coq.Decl]
relConstrLems = undefined {- concatMap (\lem -> [lem, AddHint RewriteHint (bindName lem) GraphRelBackDB]) relConstrLemmas -} -}

relConstrLemmas :: Id -> RefType -> [Coq.Decl]
relConstrLemmas f tpf =
  mkRelBranchLemmas
    args -- args from the split (as in CoqUtil)
    (v, utrRefType ret)
    univArgs
    univAxs
    conds'
    (indBranches [] tac)
  where
    (args, ret@(RefType v _ _)) = arrs tpf
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

mkRelBranchLemmas :: [(Id, RocqType)] -> (Id, RocqType) -> [(Id, RocqType)] -> [(Id, RocqType)] -> [CoqTerm] -> [(Id, RocqType)] -> [Coq.Decl]
mkRelBranchLemmas args retArg univArgs univAxs conds branches = map mkBackwardsReasoningLemma univVarsClasses
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
            substUniv = map (\(x, y) -> (y, Coq.Var x)) univSubst
            antes' = map (subst substUniv) antes
            isRelDef (Coq.App frel ts@(_ : _)) = case last ts of
              fres@Coq.Var {} | fres `elem` map (subst substUniv . Coq.Var . fst) (brArgs ++ univArgs) && relPostfix `isSuffixOf` show frel -> True where
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
            isInert (Cr lit) | lit `elem` [btrueTmName, bfalseTmName, Coq.unitTmName] = True
            isInert (Cr _) = True
            isInert (Def _) = True
            isInert _ = False
            mkUnivVars :: Integer -> CoqTerm -> (CoqTerm, [(Id, Id)], Integer)
            mkUnivVars i (Coq.Var v) = (Coq.Var $ "x_" ++ show (i + 1), [("x_" ++ show (i + 1), v)], i + 1)
            mkUnivVars i (Coq.App c ts) | isInert c = (Coq.App c ts', substs, j)
              where
                acc (prevTs', prevSubsts, k) t = (prevTs' ++ [t'], prevSubsts ++ newSubsts, l)
                  where
                    (t', newSubsts, l) = mkUnivVars k t
                (ts', substs, j) = foldl acc ([], [], i) ts
            mkUnivVars i atom | isInert atom = (atom, [], i)
            mkUnivVars i (Coq.Bop op s t) = (Coq.Bop op s' t', sSubsts ++ tSubsts, k)
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
        mergeBrs (univRes'@(Coq.App rel ts), sbst, br@(n, bargs, baxs, resTm)) = res
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

            univCond other@(Coq.App rel' ts', sbst', br') | rel' /= rel = Nothing
            -- ToDo: generalize by removing the assumptions imposed by the subsequent two lines
            -- univCond other@(Coq.App rel' ts', sbst', br') | not (sbst' `isInfixOf` sbst) = Nothing
            -- univCond other@(Coq.App rel' ts', sbst', br'@(_,oArgs,oAxs,_)) | not (oAxs `isInfixOf` baxs) = Nothing
            univCond other@(Coq.App rel' ts', sbst', br'@(_, oArgs, oAxs, _)) = {- traceFuncRet ["univCond", show (univRes', sbst, br), "\nand\n", show other, if not (null mergeSubstsO) then unwords ["\nwith", "nonConflicting:", show nonConflicting, "\nextraConds:", show extraConds, "\nmatchConds:", show matchConds] else ""] -} resConds
              where
                resConds = if null mergeSubstsO || ts == ts' then Nothing else Just (nonConflicting, conflicting, extraConds ++ map (\t -> ("h_" ++ hashName t, t)) matchConds)
                -- missingSbst = sbst' \\ sbst

                mergeSubstsO = mergeSubst ts ts'
                mergeSubst [] [] = Just []
                mergeSubst (tm : xs) (tm' : ys) | tm == tm' = mergeSubst xs ys
                mergeSubst ((Coq.Var uniVar) : xs) (tm : ys) = ((Coq.Var uniVar, tm) :) <$> mergeSubst xs ys
                mergeSubst (tm : xs) ((Coq.Var uniVar') : ys) | (\case Coq.Var {} -> False; _ -> True) tm = ((tm, Coq.Var uniVar') :) <$> mergeSubst xs ys
                mergeSubst _ _ = Nothing
                extraSbst = sbst \\ sbst'
                backSubsts = [(v, tm) | (uniVar, v) <- extraSbst, (Coq.Var uniVar', tm) <- fromJust mergeSubstsO, uniVar == uniVar']
                univSubst' = [(uniVar', tm) | (tm, Coq.Var uniVar') <- fromJust mergeSubstsO, (\case Coq.Var {} -> False; _ -> True) tm]
                substConds = [Coq.Bop Coq.Eq (Coq.Var u) (Coq.Var v) | (uniVar, u) <- sbst, (uniVar', v) <- sbst', uniVar == uniVar', u /= v]
                matchConds = map (\(v, tm) -> Coq.Bop Coq.Eq (Coq.Var v) tm) backSubsts
                extraConds' = mapMaybe (\case (n_p, Prop p) -> Just (n_p, subst univSubst' p); _ -> Nothing) $ oArgs \\ bargs
                backRepl = foldl (.) id $ map (\(v, tm) -> replaceSubterm (TermPat tm, True) (Coq.Var v)) backSubsts
                extraConds = mapSnd backRepl extraConds' ++ map (\t -> ("h_" ++ hashName t, t)) substConds
                haveNoConflict :: CoqTerm -> CoqTerm -> Bool
                haveNoConflict (IsTrue (Coq.Bop EqualB matchedTm cApp)) (IsTrue (Coq.Bop EqualB matchedTm' cApp')) | matchedTm == matchedTm' = cApp == cApp'
                haveNoConflict (Coq.Bop Coq.Eq (Coq.Bop EqualB matchedTm cApp) (Cr "true")) (Coq.Bop Coq.Eq (Coq.Bop EqualB matchedTm' cApp') (Cr "true")) | matchedTm == matchedTm' = cApp == cApp'
                haveNoConflict (Coq.Bop Coq.Eq p (Cr "true")) (Coq.Bop Coq.Eq (Coq.Neg p') (Cr "true")) | p == p' = False
                haveNoConflict (Coq.Bop Coq.Eq (Coq.Neg p') (Cr "true")) (Coq.Bop Coq.Eq p (Cr "true")) | p == p' = False
                haveNoConflict (IsTrue p) (IsTrue (Coq.Neg p')) | p == p' = False
                haveNoConflict (Coq.Bop Coq.Eq (Coq.Neg p') (Cr "true")) (Coq.Bop Coq.Eq p (Cr "true")) | p == p' = False
                haveNoConflict p (Coq.Neg p') | p == p' = False
                haveNoConflict (Coq.Neg p') p | p == p' = False
                haveNoConflict (Coq.Bop Coq.Eq p (Cr "true")) (Coq.Bop Coq.Eq (Coq.App neg [p']) (Cr "true")) | neg == Def negb && p == p' = False
                haveNoConflict (Coq.Bop Coq.Eq (Coq.App neg [p']) (Cr "true")) (Coq.Bop Coq.Eq p (Cr "true")) | neg == Def negb && p == p' = False
                haveNoConflict p q = {- traceFuncRet ["haveNoConflict", show p, show q] -} True
                nonConflicting = filter (\case (_, Prop p) -> all (\case (_, q) -> haveNoConflict p q; _ -> True) extraConds; _ -> True) bargs
                conflicting = bargs \\ nonConflicting
            univCond (shape, sbst', br') = trace ("other branch has invalid shape: " ++ show shape ++ ". ") Nothing
        -- \| univVarBranches with branches of same result shape "merged" into one equivalence class
        cls = [(univRes, [(sbst, br) | (univRes', sbst, br) <- mergedUnivBrs, univRes' == univRes]) | univRes <- nub $ map fst3 mergedUnivBrs]

    mkBackwardsReasoningLemma :: (CoqTerm, [([(Id, Id)], (Id, [(Id, RocqType)], [CoqTerm], CoqTerm))]) -> Coq.Decl
    mkBackwardsReasoningLemma (univRes, branchs) =
      {- traceFuncRet ["mkBackwardsReasoningLemma", show (univRes, branchs), show conds] $ -}
      Coq.Definition
        lemName
        (map (,False) (commonUnivArgs ++ univArgs ++ univAxs ++ commonBrArgs ++ [(uv, Hole) | uv <- uncommonUnivVars]) ++ [(resArg, False) | resIsTm])
        (Prop $ Equiv relCApp (mkExists commonExistArgs disjuncts))
        (ProofBody [Custom $ "rel_back' " ++ addParens (unwords (map (++ " _::_") . nub . map showCond $ conds) ++ " _nil")])
        Opaque
      where
        isCrAppl (Cr c) = c `notElem` [btrueTmName, bfalseTmName]
        isCrAppl cAppl@(Coq.App Cr {} _) = True
        isCrAppl _ = False

        showCond :: CoqTerm -> String
        showCond (Forall [] tm) = showCond tm
        showCond (Exists [] tm) = showCond tm
        showCond (IsTrue (Coq.Bop EqualB tm cAppl)) | isCrAppl cAppl = showP tm
        showCond (Coq.Bop Coq.Eq (Coq.Bop EqualB tm cAppl) (Cr "true")) | isCrAppl cAppl = showP tm
        showCond (Coq.Bop Equal tm cAppl) | isCrAppl cAppl = showP tm
        showCond (IsTrue t) = showCond t
        showCond tm = showP tm

        globalVars = map fst (commonUnivArgs ++ univArgs ++ commonBrArgs)
        Coq.App _ univResVars = univRes
        sbsts = concatMap fst branchs

        uncommonUnivVars = nub $ [uv | Coq.Var uv <- univResVars, sbstBrs1 <- map fst branchs, (uv1, res1) <- sbstBrs1, uv == uv1, sbstBrs2 <- map fst branchs, (uv2, res2) <- sbstBrs2, uv1 == uv2, res1 /= res2, null $ [(res1, res2), (res2, res1)] `intersect` (sbstBrs1 ++ sbstBrs2), not (all (== res2) [res' | (uv', res') <- sbsts, uv1 == uv', res' /= res1] && res1 `elem` globalVars && res2 `elem` globalVars)]

        -- \| those commonResSubsts that are shared amongst all branchs
        commonResSubsts' = nub [(univVar, u) | substs <- map fst branchs, (univVar, u) <- substs {-, univVar `notElem` uncommonUnivVars-}]
        commonResSubsts = nub [(univVar, u) | (univVar, u) <- commonResSubsts', all (\(uV, w) -> not (univVar == uV && u /= w) || any (\(uV', w') -> w' == w && (uV' < uV)) commonResSubsts') commonResSubsts']
        commonResVars = nub [u | (_, u) <- commonResSubsts]
        -- \| the commonResVars with their types
        commonResArgs :: [(Id, RocqType)]
        commonResArgs = nub [(u, wTp) | u <- commonResVars, (w, wTp) <- concatMap ((\(_, brArgs, _, _) -> brArgs) . snd) branchs, u == w]
        brArgs = map (\(_, (_, ags, _, _)) -> ags) branchs
        freeVars (Coq.Var w) = [w]
        freeVars (Def _; Cr _; IntLiteral _; TT; FF) = []
        freeVars (Coq.App f ts) = nub $ freeVars f ++ concatMap freeVars ts
        freeVars (Coq.Bop _ s t) = nub $ freeVars s ++ freeVars t
        freeVars (Coq.And s t) = nub $ freeVars s ++ freeVars t
        freeVars (Coq.Or s t) = nub $ freeVars s ++ freeVars t
        freeVars (IsTrue t) = freeVars t
        freeVars TT = []
        freeVars FF = []
        -- \| no other cases can actually occur inside relations
        freeVars other = error $ "Unexpected term inside body of backwards reasoning lemma: " ++ show other
        inScope = all (`elem` map fst (commonUnivArgs ++ univArgs)) . freeVars . substitute
        commonBrArgs = [second substitute arg | arg@(_, Prop p) <- head brArgs, (\case Coq.App {} -> True; other -> other `elem` conds {-(Coq.Bop Coq.Eq (Coq.Bop EqualB Coq.Var{} Cr{}) (Cr "true")) -> True; (Coq.Bop Coq.Eq (Coq.Bop _ Coq.Var{} (Coq.App Cr{} _)) (Cr "true")) -> True; (Coq.Bop Coq.Eq _ Cr{}) -> True; (Coq.Bop Coq.Eq _ (Coq.App Cr{} _)) -> True;-}; _ -> False) p, all (arg `elem`) brArgs, inScope p]
        univBranches = map mkUnivBranch branchs

        -- substitute :: (Suable a CoqTerm) => a -> a
        substitute = subst $ mapSnd Coq.Var commonResSubsts
        resRelAppl = substitute univRes

        mkUnivBranch :: ([(Id, Id)], (Id, [(Id, RocqType)], [CoqTerm], CoqTerm)) -> ([(Id, RocqType)], [CoqTerm], [CoqTerm])
        mkUnivBranch (substs, (_, brArgs, antes, _)) = (brArgs' \\ commonResArgs, univConds, antes')
          where
            univConds = [Coq.Bop Coq.Eq (Coq.Var u) (Coq.Var w) | (wV, w) <- commonResSubsts, (uV', u) <- substs, wV == uV', w /= u] ++ [Coq.Bop Coq.Eq (Coq.Var uv) (Coq.Var v) | uv <- uncommonUnivVars, (uv2, v) <- substs, uv == uv2]
            brArgs' = mapSnd substitute brArgs
            antes' = map substitute antes
        f_cs = map (\(_, (fc, _, _, _)) -> fc) branchs
        f_prefix =
          {- trace ("\nunivRes: " ++ show univRes ++ ", \nbranchs: " ++ show branchs ++ ", \ncommonResVars: " ++ show commonResVars ++ ", \ncommonResSubsts': " ++ show commonResSubsts' ++ ", \ncommonResSubsts: " ++ show commonResSubsts ++ ", \nresRelAppl: " ++ show resRelAppl) $ -}
          head . split '_' $ head f_cs
        lemName = relBranchLemName $ f_prefix ++ concatMap (removePrefix f_prefix) f_cs

        v = fst retArg
        isVar = \case Coq.Var _ -> True; Def _ -> True; _ -> False
        isCAppl = \case Cr {} -> True; (Coq.App Cr {} _) -> True; _ -> False
        Coq.App rel indeces = resRelAppl
        resTm = last indeces
        -- if resTm is already an axiomatized variable, there is a point in creating another variable for it
        -- also resTm doesn't contain any bound variables, so it is fully determined by inverting relCApp
        resIsTm =
          not (isVar resTm)
            && not (isCAppl resTm)
            && not
              ( any
                  ( any (\bdVar -> hasMatch (TermPat . Coq.Var $ fst bdVar, True) resTm)
                      . (\(vars, _, _) -> filter (\arg -> any (hasMatch (TermPat . Coq.Var $ fst arg, True)) indeces) vars)
                  )
                  univBranches
              )

        resArgV = mkFresh "res" (map fst (args ++ commonResArgs ++ concatMap fst3 univBranches) ++ [v])
        relCApp = Coq.App rel (init indeces ++ [if resIsTm then Coq.Var resArgV else resTm])

        occurs w = hasMatch (Coq.Var w, True)
        commonExistArgs = [arg | arg@(w, _) <- commonResArgs, occurs w resTm, not (any (occurs w) $ init indeces), resIsTm, all ((/=) w . fst) univArgs]
        commonUnivArgs = commonResArgs \\ commonExistArgs
        resArg = (resArgV, snd retArg)

        disjuncts = mkOr $ map mkDisjuncts univBranches

        mkDisjuncts :: ([(Id, RocqType)], [CoqTerm], [CoqTerm]) -> CoqTerm
        mkDisjuncts (vars, univConds, antes) = {- traceFuncRet ["mkDisjuncts", show vars, show univConds, show antes] -} disjRes
          where
            isPreCond = all (`elem` globalVars) . freeVars
            boundVars = filter (\arg -> any (hasMatch (TermPat . Coq.Var $ fst arg, True)) indeces) vars
            existVars' = filter (\arg -> arg `notElem` boundVars && all ((/=) (fst arg) . fst) (univArgs ++ commonBrArgs)) vars
            propArgs = filter (\case (_, Prop p) -> True; _ -> False) (vars \\ commonBrArgs)
            existVars = existVars' \\ propArgs
            conjs' = map (\(_, Prop p) -> p) propArgs ++ univConds ++ antes
            preConjs = filter isPreCond conjs'
            postConjs = conjs' \\ preConjs
            isDefConj exVar (Coq.App rel ts) = case last ts of
              Coq.Var exV ->
                (exV == exVar)
                  || exV `elem` uncommonUnivVars && any (\(Coq.Bop Coq.Eq (Coq.Var uv) (Coq.Var w)) -> uv == exV && w == exVar) univConds
              _ -> False
            isDefConj _ _ = False

            mkExists' [] conjs = mkAnd conjs
            mkExists' [(_, Prop p)] [Cr "true"] = p
            mkExists' (arg@(h, Prop p) : tl) conjs = Coq.And p (mkExists' tl conjs)
            mkExists' (arg@(h, _) : tl) conjs = Exists [arg] $ case find (isDefConj h) conjs of
              Just conj -> Coq.And conj (mkExists' tl $ conjs \\ [conj])
              Nothing -> mkExists' tl conjs
            existTm = mkExists' existVars postConjs
            disjRes = mkAnd $ preConjs ++ [Coq.Bop Coq.Eq (Coq.Var resArgV) resTm | resIsTm] ++ [existTm]
