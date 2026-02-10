{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}


-- | Translation from ILH to Coq via bidirectional typechecking
module Lava.TypedTranslation
  ( translateTyping,
  )
where

import Control.Monad (foldM, void)
import Lava.Coq (projPackName, subsetWitnessNm)
import qualified Lava.Coq as Coq
import Lava.CoqUtil (assertFresh, funcHoodLemName, relDefBranchName, ihName, injCast, mkForallT, mkReflAuxDecls, mkIsTrue, mkInductiveSkeleton, IndTree (..), ppForall, projectTm, relDefName, relDefThmName, relDefLemName, relPostfix, transRefTC, mkCoqTheorem, packInstanceName, packDefName, destructSubsetArg, unrefRocqType)
import Lava.CoqSyntaxUtil (mkArrowT, matchFunctionType, matchImplFunctionType, mkFuncType, packGetF)
import Data.Bifunctor (bimap, first, second)
import Data.Either.Extra (maybeToEither)
import Data.List (uncons, (\\), union)
import Data.List.Tools (dropUntil)
import qualified Data.Map as Map
import Data.Tuple.Extra (uncurry3)
import qualified Data.Set as Set (toList, unions, difference, fromList)
import Lava.InternalLH as ILH
import Lava.PaperUtils
import qualified Lava.TypingContext as Ctx
import Lava.UntypedTranslations
import Lava.Util -- (Id, freshVar, mapSnd, thd3, sub, fromJust, safeHead)

-- TODO:
-- - annotations
-- - post-processing for IHs

-- Matching context, containing for each argument of the function under consideration
-- the argument itself or the constructor application it has been destructed to
type MatchCtx = ([LHSimpleTerm], [(Id, [Id])])

-- | Entrypoint
translateTyping :: [ILH.LHDecl] -> Either TransError [Coq.CoqDecl]
-- We forget the typing context return by wfDecls as we have the full list of declarations
translateTyping decls = snd <$> wfDecls Ctx.initial decls

-- * Well-formedness of contexts and types, does not translate anything

-- TODO: rewrite
{- wfCtx :: Ctx.TypingCtx -> Bool
wfCtx γ = Ctx.foldrWithKey (\k bind acc -> acc && test k bind) True γ
  where
    test _ (Left tp) = wfArrType γ tp
    test k (Right consts) =
      all
        ( \(c, tp) ->
            wfArrType γ tp
              && c `Ctx.notMember` γ
              && argTp (retTp tp) == TDat k
        )
        consts -}

-- (WF-Fun)
wfArrType :: Ctx.TypingCtx -> ArrType -> Either TransError ()
wfArrType γ (ArrType args ret) = do
  γ' <- foldM (\γi arg -> wfRefType γi (snd arg) >> Ctx.insertRefType arg γi) γ args
  wfRefType γ' ret

-- (WF-Base)
wfRefType :: Ctx.TypingCtx -> RefType -> Either TransError ()
wfRefType γ (RefType x tp r) = do
  γ' <- Ctx.insertRefType (x, RefType x tp ttTm) γ
  void $ checkSmpTerm γ' r (RefType x' boolTp ttTm) ("", ([], []))
  where
    x' = show x ++ "'"

-- * Bidirectional type checking and translation

-- | Well-formedness of modules (WF-Mod)
wfModule :: Ctx.TypingCtx -> LHModule -> Either TransError (Ctx.TypingCtx, Coq.CoqModule)
wfModule γ (LHModule x decls) = second (Coq.CoqModule x) <$> wfDecls γ decls

-- | Well-formedness of a list of declarations (auxiliary function)
wfDecls :: Ctx.TypingCtx -> [LHDecl] -> Either TransError (Ctx.TypingCtx, [Coq.CoqDecl])
wfDecls = wfDeclsAux
wfDeclsAux :: Ctx.TypingCtx -> [LHDecl] -> Either TransError (Ctx.TypingCtx, [Coq.CoqDecl])
wfDeclsAux γ [] = return (γ, [])
wfDeclsAux γ (d : decls') = do
  (γ', d') <- wfDecl γ d
  (γ'', declsT) <- wfDeclsAux γ' decls'
  return (γ'', d' ++ declsT)


-- | Well-formedness of declarations
-- We also return the updated context, so that we can use it for the next declarations in the program
wfDecl :: Ctx.TypingCtx -> LHDecl -> Either TransError (Ctx.TypingCtx, [Coq.CoqDecl])
wfDecl γ decl =
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
        else return {- traceFuncRet ["wfDecl", "...", show decl] -} (γ', transDefinition γ f tp tacs)

-- | Checking of expressions
-- The additional argument (f, mCtx) is a list of replacements of ILH applications
-- paired with calls to the appropriate IH in Coq
checkTerm :: Ctx.TypingCtx -> LHTerm -> RefType -> (Id, MatchCtx) -> Either TransError [Coq.CoqTactic]
checkTerm γ e tp (f, mCtx@(fCtx, matchedVars)) = {- traceFuncRet ["checkTerm", "...", showP e, showP tp, show (f, mCtx)] $ -} case e of
  -- An if-then-else written as a match
  Case cond [("False", [], elseE), ("True", [], thenE)] _ -> do
    let
      condT = utrSmpTerm (fetchFuncts γ) cond
      transBrExpr _ expr = checkTerm γ expr tp (f, mCtx)
    elseET <- transBrExpr Coq.btrue elseE
    thenET <- transBrExpr Coq.btrue thenE
    return [Coq.Destruct condT [("true", (Coq.ConjDestrPat [], thenET)), ("false", (Coq.ConjDestrPat [], elseET))]]

  -- | (C-Case) 
  -- TODO: check that the left of the arrows are correctly typed? That R is an inductive?
  Case r alts _ -> do
    (tpR@(RefType v b r0), _) <- synSmpTerm γ r (f, mCtx)
    rT <- checkSmpTerm γ r tpR (f, mCtx)
    tc <- case b of
      TDat itc -> Right itc
      _ -> Left . CheckingErr $ "Cannot match on term " ++ show r ++ " of non-inductive type " ++ show b ++ "."
    tcConstrTps <- case Ctx.lookupTC tc γ of
          Nothing -> Left . SynErr $ "Cannot synthetise type for type constructor " ++ show tc
          Just tpsTC -> Right tpsTC

    let
      -- | the function arguments 
      args = concatMap (Set.toList . freeVars) fCtx
      -- | whether to translate using induction (when isInduction=True) or using destruct (when isInduction=False)
      (isInduction, xO) = case r of
        Var x -> (x `elem` args, Just x)
        _ -> (False, Nothing)
      onToplevel = all (\case (Var _) -> True; _ -> False) fCtx
    {-  getConstrTp c = maybeToEither (SynErr $ "Cannot synthetise type for constructor " ++ show c ++ ", tcConstrTps:" ++ show tcConstrTps) $
              Prelude.lookup c tcConstrTps
      cis = map fst3 alts

    ciTps <- mapM getConstrTp cis
    ri <- mapM (\(ArrType _ (RefType _ bi ri)) -> if bi == b then Right ri else Left . CheckingErr $ "Constructor is of wrong base type. ") ciTps
    let ciArgs = map (\(ArrType args _) -> args) ciTps -}

    let
      checkBranch :: (Id, [Id], LHTerm) -> Either TransError (Id, (Coq.CoqDestrPat, [Coq.CoqTactic]))
      checkBranch alt@(c, ys, e) = do
        -- New matching context
        bi <- case xO of
          Just x -> replaceVarByConstr x (c, ys) fCtx
          Nothing -> Right fCtx
        -- Type of c
        tpc@(ArrType args ret) <- maybeToEither (SynErr $ "Cannot synthetise type for constructor " ++ show c ++ ", tcConstrTps:" ++ show tcConstrTps) $
            Prelude.lookup c tcConstrTps
        γi <- branchCtx γ alt xO tpR tpc
        -- New variables that are of the same inductive type as x
        let indVars = [yij | (yij, (_, tpj)) <- zip ys args, argTp tpj == argTp ret, isInduction]

        {- traceFuncRet ["checkBranch", show isInduction, show tpx, show alt] . -}

        let tpReplaced = case xO of
              Just x -> sub x (App (Var c) $ map Var ys) tp
              Nothing -> tp
        (c,) . (desPattern ys indVars,) . (:) (Coq.Intros []) <$> checkTerm γi (thd3 alt) tpReplaced (f, (bi, matchedVars ++ maybe [] (singleton . (, ys `union` indVars)) xO))
      -- For a branch with binders ys under matching context bi, build the destruction patterns, with an induction
      -- hypothesis for each binder of the same inductive types as x
      -- Having an empty indVars creates the correct patterns for a destruct
      desPattern ys indVars =
        let varPattern y =
              Coq.SingleIdPat y : [Coq.SingleIdPat (ihName y) | y `elem` indVars]
        in Coq.ConjDestrPat $ concatMap varPattern ys

    branchesT <- mapM checkBranch alts
    -- ToDo: type-check the expressions on the branches

    return . singleton $
      if isInduction
        -- TODO: need to add the variables to generalize
        then
          let x = fromJust xO in
          Coq.Concat $ [Coq.GeneralizeDependent (reverse $ args \\ [x]) | not (null $ args \\ [x]) && onToplevel] ++ [Coq.Induction (Coq.Var x) branchesT]
        else Coq.Destruct (projectTm rT) branchesT

  -- An if
  Let x _ (BasicTerm cond) (Case (Var x') [("False", [], elseE), ("True", [], thenE)] _) | x == x' -> do
    let
      condT = utrSmpTerm (fetchFuncts γ) cond
      transBrExpr _ expr = checkTerm γ expr tp (f, mCtx)
    elseET <- transBrExpr Coq.btrue elseE
    thenET <- transBrExpr Coq.btrue thenE
    return [Coq.Destruct condT [("true", (Coq.ConjDestrPat [], thenET)), ("false", (Coq.ConjDestrPat [], elseET))]]
  -- A destruct
  Let x _ (BasicTerm r) (Case (Var x') cases rC) | x == x' -> checkTerm γ (Case r (mapThd (sub x r) cases) rC) tp (f, mCtx)
  -- TODO: (C-Let)
  Let x tpx' e1 e2 -> do
    -- NOTE: we try to synthesize the type to keep current examples working.
    -- We probs want to change it later
    (tpx, tacs1) <- case (synTerm γ e1 (f, mCtx), tpx') of
        (Right (tpx, tacs1), _) -> return (tpx, tacs1)
        (Left _, Just tpx) -> do
          tacs1 <- checkTerm γ e1 tpx (f, mCtx)
          return (tpx, tacs1)
    γ' <- Ctx.insertRefType (x, tpx) γ
    tacs2 <- checkTerm γ' e2 tp (f, mCtx)
    case tpx of
      RefType xT xTp@Pi{} xR -> return $ Coq.Assert g gTp (Coq.Concat tacs1) : assertF : tacs2 where
        gTp = trRefType γ tpx
        g = "f_" ++ hashName gTp
        assertF = Coq.Custom $ "unshelve refine (let " ++ x ++ " : ltac:(buildPackG_spec " ++ g ++ ") := (ltac:(fun_to_pack " ++ g ++ ")) in _)"
      _ -> return $ Coq.Assert x (trRefType γ tpx) (Coq.Concat tacs1) : tacs2

    -- C-Lam
  Lambda x bdy -> case tp of
    RefType _ (Pi (x', xTp') codom) _ -> do
      γ' <- Ctx.insertRefType (x, sub x' (Var x) xTp') γ
      tacs2 <- checkTerm γ' bdy (sub x' (Var x) codom) (f, mCtx)
      return $ [Coq.Intros [Coq.DestrPat $ Coq.SingleIdPat x]]++[destructSubsetArg x |(\case Pi{} -> False; _ -> True) (argTp xTp')] ++ tacs2
    _ -> error $ "Pi-type expected but found type "++show tp++" for lambda expression: "++show e
  -- (Chk-Undef)
  Undefined -> return [Coq.Concat [Coq.Intros [], Coq.Exfalso, Coq.Oracle]]
  -- (C-Hint)
  QMark e1 e2 -> do
    (tp2, tacs2) <- synTerm γ e2 (f, mCtx)
    if argTp tp2 /= unitTp
      then Left . CheckingErr $ "Hint " ++ show e2 ++ " is not of unit type, but of type " ++ show tp2
      else do
        -- TODO: create insertWithFresh function
        γ' <- Ctx.insertRefType (argName tp2, tp2) γ
        tacs1 <- checkTerm γ' e1 tp (f, mCtx)
        let
          asserted = Coq.Prop . utrSmpTermProp γ $ argRef tp2
          transHint = case tacs2 of
            [pp@(Coq.ProofPose h tm)] -> [Coq.Custom "fix_notations", pp, Coq.Assert (h++"'") asserted Coq.Oracle]-- assertFresh asserted Coq.Oracle]
            _ -> [assertFresh asserted (Coq.Concat tacs2)]
        return $ transHint ++ Coq.Custom "fix_notations" : tacs1
  BasicTerm r -> singleton . Coq.Exact <$> checkSmpTerm γ r tp (f, mCtx)
  _ -> do
    (tp', tacs) <- synTerm γ e (f, mCtx)
    if isCompatible tp' tp
      then return $ transSubTacs tp' tp tacs
      else Left . SubtypingErr $ "Synthetised type " ++ show tp' ++ " for " ++ show e ++ " is not a subtype of " ++ show tp ++ " in context:\n" ++ Ctx.showCtx γ
    where
      refinesUnit rt = argTp rt == unitTp
      transSubTacs from to tacs = case tacs of
        [Coq.Exact tm] -> if isSubtype γ from to then
          [Coq.Exact $ transSub γ from to tm]
          else [Coq.Exact $ castFctTp γ tm from to]
        [Coq.ProofPose h tm] | refinesUnit to ->
          [Coq.Concat [Coq.ProofPose h tm, Coq.Refine $ Coq.Exist Coq.TermHole Coq.unitTm (Coq.TermWitness Coq.unitTm), Coq.Oracle]]
        [Coq.ProofPose h tm] -> if isSubtype γ from to then
          [Coq.ProofPose h tm, Coq.Concat [Coq.Refine $ transSub γ from to (Coq.Var h)]]
          else [Coq.Concat [Coq.ProofPose h tm, Coq.Refine $ castFctTp γ (Coq.Var h) from to]]
        _ -> error $ "tacs: " ++ show tacs

-- | Synthesis of expressions
synTerm :: Ctx.TypingCtx -> LHTerm -> (Id, MatchCtx) -> Either TransError (RefType, [Coq.CoqTactic])
synTerm γ e (f, mCtx) = {- trace (unwords ["synTerm", show e]) $ -} case e of
  BasicTerm r -> do
    (tp, cqtm) <- synSmpTerm γ r (f, mCtx)
    return (tp, [Coq.Exact cqtm])
  -- (Syn-Eq)
  SEqn r1 r2 hint -> do
    (RefType x a r, cqtm1) <- synSmpTerm γ r1 (f, mCtx)
    {- checkTerm :: Ctx.TypingCtx -> LHTerm -> RefType -> (Id, MatchCtx) -> Either TransError [Coq.CoqTactic] -}
    (tpHint, tacs) <- synTerm γ hint (f, mCtx)
    cqtm2 <- do
      γ' <- Ctx.insertRefType (argName tpHint, tpHint) γ
      checkSmpTerm γ' r2 (RefType x a (Bop And r (Bop Eq (Var x) r))) (f, mCtx)
    if argTp tpHint == unitTp
      then return (RefType x baseTp (Bop And r (Bop Eq r1 r2)), transSEqn cqtm1 cqtm2 tacs)
      else Left . SynErr $ "The type of the hint is not Unit in " ++ show e
    where
      transSEqn tm1 tm2 tacs = [assertFresh (Coq.Prop $ Coq.Bop Coq.Eq tm1 tm2) (Coq.Concat tacs)]
      baseTp = unitTp -- a
  -- (Syn-Ann)
  Annot e' tp -> (tp,) <$> checkTerm γ e' tp (f, mCtx)
  _ -> Left . SynErr $ "Type annotation needed for the term " ++ show e

-- | Checking of simple term: always by (Chk-Syn)
checkSmpTerm :: Ctx.TypingCtx -> LHSimpleTerm -> RefType -> (Id, MatchCtx) -> Either TransError Coq.CoqTerm
checkSmpTerm γ r tp (f, mCtx) = {- traceFuncRet ["checkSmpTerm", "...", "...", showP r, showP tp, "..."] $ -} do
  (tp', cqtm) <- synSmpTerm γ r (f, mCtx)
  if isSubtype γ tp' tp
    then return {- $ traceFuncRet ["checkSmpTerm", "...", showP r, showP tp, show (f, mCtx)] -} $ transSub γ tp' tp cqtm
    else if
      isCompatible tp' tp
      then return $ castFctTp γ cqtm tp' tp
      else Left . SubtypingErr $ "Inferred type " ++ show tp' ++ " for " ++ show r ++ " is not a subtype of " ++ show tp ++ " in context:\n" ++ Ctx.showCtx γ

-- | Cast a function type
castFctTp :: Ctx.TypingCtx -> Coq.CoqTerm -> RefType -> RefType -> Coq.CoqTerm
castFctTp γ r have@(RefType x Pi{} xRef) need@(RefType y needBaseTp@Pi{} _) =
  transSub γ interTp need $ castFctTp γ r have interTp where
    interTp = RefType x (sub y (Var x) needBaseTp) xRef
{- castFctTp γ r (RefType x (Pi (_, dom) codom) xRef) (RefType x' (Pi (x_2', dom') codom') xRef') | x == x' && xRef == xRef' = case r of
  Coq.Lambda y _ body -> Coq.Lambda y tp' . transSub γ codom codom' $ sub y (yCast y) body
  _ -> Coq.Lambda x_2' tp' . transSub γ codom codom' $ Coq.App r [yCast x_2']
  where
    tp' = trRefType γ dom'
    yCast y = transSub γ dom' dom (Coq.Var y) -}
castFctTp γ r have need | isSubtype γ have need = transSub γ have need r
castFctTp _ _ have need = error $ "Cannot cast type " ++ show have ++ " into " ++ show need ++ ": not a subtype."

-- | Partial applications of substitutions of the refinements in an application
-- (x_i:R_i)_{i < n} -> (r_i)_{i < n} -> Maybe (σn, R_iσ_i) where σ_i = {r_j\x_j}_{j < i}
substCqArgs :: [(Id, Coq.RocqType)] -> [Coq.CoqTerm] -> Either TransError ([(Id, Coq.CoqTerm)], [Coq.RocqType])
substCqArgs = aux []
  where
    -- The first argument is the current substitution built with previous arguments
    aux :: [(Id, Coq.CoqTerm)] -> [(Id, Coq.RocqType)] -> [Coq.CoqTerm] -> Either TransError ([(Id, Coq.CoqTerm)], [Coq.RocqType])
    aux σ [] [] = return (σ, [])
    aux σ ((x, tp) : tps) (r : rs) = do
      (σ', rs') <- aux ((x, r) : σ) tps rs
      return (σ', subst σ tp : rs')
    aux σ args ts = Left . SubstErr $ unwords ["Error2 in substitution:", show σ, show args, show ts]

-- | Synthesis of simple terms when expecting a RefType
synSmpTerm :: Ctx.TypingCtx -> LHSimpleTerm -> (Id, MatchCtx) -> Either TransError (RefType, Coq.CoqTerm)
synSmpTerm γ r (f, mCtx@(fCtx, matchVars)) = {- traceFuncRet ["synSmpTerm", show γ, showP r, show (f, mCtx)] $ -} case r of
  -- (S-Var)
  Var x -> do
    tp <-
      maybeToEither (SynErr $ "Variable or constructor " ++ show x ++ " not bound in context with a simple refinement type in the translation of " ++ f ++ ".") $
        Ctx.lookupRefType x γ
    let tp' = selfification x tp
        isBuildin = x `elem` [ttTmName, ffTmName, unitTmName]
        isConstr =  not . null $ Ctx.lookupDC x γ
        isRefFunc = not . null $ Ctx.lookupDef x γ
        isRef = isConstr && not isBuildin || isRefFunc
        isLocal = not isRef
        arity = getArity tp
        castTm
          | isLocal && arity == 0
          = injCast (trRefType γ tp') (Coq.Var x) Nothing
          | arity > 0 && isRefFunc = Coq.Def $ packInstanceName x
          | isRef && isDC x = Coq.Cr x
          | otherwise = Coq.Var x
    return (tp', castTm)
  -- (Lit)
  StringLit _ -> error "Strings not yet included in Coq"
  -- return (RefType "VV" (Buildin String) (Bop Eq (Var "VV") r))
  IntLit n -> return (RefType "VV" (Buildin Integer) (Bop Eq (Var "VV") (IntLit n)), Coq.Exist Coq.TermHole (Coq.IntLiteral n) (Coq.CoqProofTerm "eq_refl"))
    -- error $ "The integer literal "++show n++" is not of a refined type"
  FloatLit _ -> error "Floats not yet included in Coq"
  -- return $ RefType "VV" (Buildin Double) (Bop Eq (Var "VV") r)
  -- (S-App)
  App (Var g) rs -> do
    (ArrType tpArgs' ret', cqtm_) <- synSmpTermArr γ (Var g)
    let
      cqtm = if (not . null $ Ctx.lookupDef g γ) || isDC g then cqtm_ else packGetF cqtm_
      tp = ArrType tpArgs ret
      tpArgs = tpArgs' ++ tpArgs''
      (tpArgs'', ret) = go ret' where
        go :: RefType -> ([(Id, RefType)], RefType)
        go (RefType _ (Pi (x,xTp) retx) _) = first ([(x,xTp)] ++) $ go retx
        go smpRef = ([], smpRef)
    -- infer types for/translate the arguments
    cqTmTps <- mapM (\ri -> synSmpTerm γ ri (f, mCtx)) rs
    let
      tpArgNames = map fst tpArgs
      (rTps, cqtms') = unzip cqTmTps

    -- and the expected and inferred types (so far w/o substitutions)
      (args, _) = matchFunctionType [] $ trArrType γ tp
      cqTps = map (trRefTypeAux True True γ) rTps
      cqArgs = {- (if length tpArgNames < length rs then trace (g ++":: "++show tp++" applied to "++show rs++", tpArgs: " ++ show tpArgs ++ ", tpArgNames: "++show tpArgNames) else id) $ -} zip tpArgNames cqTps

    -- figure out the Coq substitutions required

    (cqSubsts, cqSubstTps) <- substCqArgs cqArgs cqtms'
    let
      substitute :: Suable a Coq.CoqTerm => a -> a
      substitute = subst cqSubsts

    -- Apply the substitutions to the Coq types and terms and insert the required casts
      sbstArgs = map (\(_, rt) -> substitute rt) args
      cqtms = zipWith3 (\tm need have -> Coq.SubCast need have tm $ Coq.ProofHole Nothing) cqtms' sbstArgs cqSubstTps
      cqtmTps = zip cqtms cqTps

    -- Apply the successive substitutions in the refinements, to compute the return type
    (substs, _) <- substArgs (take (length rs) tpArgs) rs -- ^ only take first (length rs) many tpArgs for the case of partial applications
    let returnTp = {- trace (unwords ["\n\tThe function application:\n", show (App (Var g) rs), "\nrTps:", show rTps, "\ncqtms':", show cqtms', "\nargs:", show args, "\ncqTps:", show cqTps, "\ncqArgs:", show cqArgs, "\ncqSubsts:", show cqSubsts, "\nsbstArgs:", show sbstArgs, "\ncqtms", show cqtms]) $ -} substInRefType substs ret

    let
        indVars = concatMap snd matchVars
        mainInductVariableO = safeHead [x | x <- indVars, Var x `elem` rs]
        rRts = zip rs cqtmTps
        remainingRs =
          takeWhile (\case (Var x, (_,_)) -> x `elem` takeWhile ((/= mainInductVariableO) . Just) (reverse indVars) || x `notElem` indVars; _ -> False) rRts
          ++ dropUntil (\case (Var x,(_,_)) -> Just x == mainInductVariableO; _ -> False) rRts
        nonInductiveArgs = [(rT,tp) | (tm, (rT,tp)) <- remainingRs, tm `notElem` map Var (dropUntil ((==mainInductVariableO) . Just) $ reverse indVars)]
        ihHyp = case mainInductVariableO of
          Just x -> ihName x
          Nothing -> error $ "No main induct variable: "++show indVars++", "++show rs
        oracle = Coq.PrfTerm Coq.Hole $ Coq.ProofHole (ihName <$> mainInductVariableO)
        containsNotEqual n tm = tm /= Var n && occurs (IdPat n, True) where
          occurs :: SubtermPattern LHSimpleTerm -> Bool
          occurs p = hasMatch p tm
        numAntes = case mainInductVariableO of
          Nothing -> 0
          Just mainIndVar | mainIndVar `elem` map fst matchVars -> 0
          Just mainIndVar -> if any (\case (App _ ys) | any (containsNotEqual mainIndVar) ys -> True; _ -> False) fCtx then 1 else 0
        argsWithOracle = replicate (numAntes + 1) oracle ++ concatMap (uncurry argPair) nonInductiveArgs
        argPair arg argTp = case argTp of
          Coq.Pack{} -> [arg]
          _ -> [projectTm arg, oracle]
    return {- . traceFuncRet ["synSmpTerm", "...", showP r, show (f, mCtx), "\nwith rs:", show rs, "\nsbstArgs:", show sbstArgs, "\nrRts:", show rRts, "\nret:", showP ret, "\nreturnTp:", showP returnTp, "\nindVars:", show indVars, "\nmainInductVariableO", showP mainInductVariableO, "\nremainingRs:", show remainingRs, "\nnonInductiveArgs:", show nonInductiveArgs, "\nargsWithOracle:", show argsWithOracle] -} $
      if f /= g -- the call is not recursive
        then (returnTp, Coq.App cqtm cqtms)
        else (returnTp, Coq.App (Coq.Var ihHyp) argsWithOracle)
  App {} -> error "App not starting with Id"
  -- (Bop)
  Bop bop r1 r2 ->
    if bop == Eq || bop == Neq
      then do
        (tp1@(RefType _ a _), cqtm1) <- synSmpTerm γ r1 (f, mCtx)
        (RefType _ b _, cqtm2) <- synSmpTerm γ r2 (f, mCtx)
        if a == b
          then
            let tpApp = RefType "VV" boolTp ttTm
             in return (tpApp, bopTrans tp1 cqtm1 cqtm2 tpApp)
          else Left . SynErr $ "Different types on both sides of (in)equality " ++ show r ++ ": found " ++ show a ++ " and " ++ show b
      else case lookup bop bopTypes of
        Just tp@(ArrType [(_, tp1), (_, tp2)] _) -> do
          cqtm1 <- checkSmpTerm γ r1 tp1 (f, mCtx)
          cqtm2 <- checkSmpTerm γ r2 tp2 (f, mCtx)
          let tpApp = applyArrType tp [r1, r2]
          return (tpApp, bopTrans tp1 cqtm1 cqtm2 tpApp)
        _ -> Left . SynErr $ "No type found for operator " ++ show bop
    where
      bopTrans (RefType x1 _ _) cqtm1 cqtm2 tpApp = if bop `elem` [Leq, Lt, Plus, Minus, Times, Div, Mod]
        then
          Coq.Bop (trBop bop) cqtm1 cqtm2'
        else
          injCast (trRefType γ tpApp) (Coq.Bop (trBop bop) cqtm1 cqtm2) Nothing
         where
            cqtm2' = sub x1 (projectTm cqtm1) cqtm2
  -- (Neg)
  Neg r' -> do
    cqtm <- checkSmpTerm γ r' (trivialRefTp boolTp) (f, mCtx)
    let tp = RefType "VV" boolTp ttTm -- (Bop Eq (Var "VV") r)
     in return (tp, {- injCast (trRefType γ tp) -} Coq.App (Coq.Def Coq.negB) [cqtm] {-Nothing-})

-- | Synthesis of simple terms when expecting an arrow (variables and data constructors)
-- (Syn-Varr) and (Syn-Data)
synSmpTermArr :: Ctx.TypingCtx -> LHSimpleTerm -> Either TransError (ArrType, Coq.CoqTerm)
-- TODO: fix when builtin booleans and Unit have been removed from the Coq grammar
synSmpTermArr _ r | r == ttTm = return (ArrType [] (RefType "VV" boolTp ttTm), Coq.btrue)
synSmpTermArr _ r | r == ffTm = return (ArrType [] (RefType "VV" boolTp ttTm), Coq.bfalse)
synSmpTermArr _ r | r == unitTm = return (ArrType [] (RefType "VV" unitTp ttTm), Coq.unitTm)
synSmpTermArr γ (Var x) =
  -- if Var x `elem` builtinDCs
  --   then return (lookup γ x, Cq.Var x)
  case Ctx.lookupDC x γ of
    Just tp -> return (tp, Coq.Cr $ Coq.refinedConstrName x)
    -- If x is not a data constructor, it is a normal variable
    Nothing -> case Ctx.lookupArrType x γ of
      Just tp -> return (tp, Coq.Var x)
      Nothing -> Left . SynErr $ "Variable " ++ show x ++ " not bound in context."
synSmpTermArr _ r = Left . SynErr $ "The simple term " ++ show r ++ " should not have an arrow type."

-- * Subtyping

-- | Subtyping is assumed to hold, as the program has been checked by Liquid Haskell
-- (S-Ref)
isSubtype :: Ctx.TypingCtx -> RefType -> RefType -> Bool
isSubtype _ tp1 tp2 = argTp tp1 == argTp tp2

isCompatible :: RefType -> RefType -> Bool
isCompatible (RefType _ a _) (RefType _ b _) = a == b || case (a, b) of
  (Pi (_, dom) codom, Pi (_, dom') codom') -> isCompatible dom dom' && isCompatible codom codom'
  _ -> False

-- * Types of primitives

bopTypes :: [(Bop, ArrType)]
bopTypes =
  [ (Plus, buildType Plus (Buildin Integer) (Buildin Integer) (Buildin Integer)),
    (Minus, buildType Minus (Buildin Integer) (Buildin Integer) (Buildin Integer)),
    (Times, buildType Times (Buildin Integer) (Buildin Integer) (Buildin Integer)),
    (Div, ArrType [ ("x_1", RefType "x_1" (Buildin Integer) ttTm), ("x_2", RefType "x_2" (Buildin Integer) (Bop Neq (Var "x_2") (IntLit 0)))]
        $ RefType "x_3" (Buildin Integer) ttTm),
    (Mod, ArrType [ ("x_1", RefType "x_1" (Buildin Integer) ttTm), ("x_2", RefType "x_2" (Buildin Integer) (Bop Neq (Var "x_2") (IntLit 0)))]
        $ RefType "x_3" (Buildin Integer) ttTm),
    (Leq, buildType Leq (Buildin Integer) (Buildin Integer) boolTp),
    (Geq, buildType Geq (Buildin Integer) (Buildin Integer) boolTp),
    (Lt, buildType Lt (Buildin Integer) (Buildin Integer) boolTp),
    (Gt, buildType Gt (Buildin Integer) (Buildin Integer) boolTp),
    (And, buildType And boolTp boolTp boolTp),
    (Or, buildType Or boolTp boolTp boolTp),
    (Impl, buildType Impl boolTp boolTp boolTp)
  ]
  where
    buildType _ a1 a2 a3 =
      ArrType
        [ ("x_1", RefType "x_1" a1 ttTm),
          ("x_2", RefType "x_2" a2 ttTm)
        ]
        $ RefType "x_3" a3 ttTm -- (Bop Eq (Var "x_3") (Bop bop (Var "x_1") (Var "x_2")))

-- * Factorized translations

-- | Translation of (Sub) for an expression
transSub :: Ctx.TypingCtx -> RefType -> RefType -> Coq.CoqTerm -> Coq.CoqTerm
transSub γ from to tm =
  {- if fromT == toT -- this check is superfluous, redundant cast will be removed by the printer
    then tm
    else-} Coq.SubCast toT fromT tm (Coq.ProofHole Nothing)
  where
    fromT = trRefType γ from
    toT = trRefType γ to

-- ** Declarations

-- | Translation of a data declaration
transDataDecl :: Ctx.TypingCtx -> Id -> [(Id, ArrType)] -> [Coq.CoqDecl]
transDataDecl γ tc alts = transRefTC [] tc (map (uncurry Coq.Constr) $ mapSnd (trArrType γ) alts)

{- CR: I really don't understand what is going on here -- and in any case there are things missing -- so I'm just using the refined inductive data types of ECoq here, for now
[ Coq.CoqInductive tcu (map (bimap Coq.unrefinedConstrName utrArrType) alts) Coq.Setsort,
  Coq.Fix (Coq.wfTCName tc) (Cq.Forall x (Just $ Cq.TCApp tcu []) Cq.PropSort) $
    Coq.Match x (map transConstrRef alts)
]
where
  x = "x_wf"
  tcu = Coq.unrefinedTCName tc
  -- Translation of each alternative into a branch of the match
  transConstrRef (c, ArrType args ret) =
    let pjs = map (getRef . trRefType . snd) args
        renamedRetRef = substSmpTerm (Var x) (argName ret) (argRef ret)
        wfC = foldl Cq.PpAnd (utrSmpTermProp renamedRetRef) pjs
     in -- We use the name inside the refinement type of the arguments (instead of fst args) to avoid renamings
        ((Coq.unrefinedConstrName c, map (argName . snd) args), Cq.Prop wfC)
    where
      getRef (Coq.SimpRef srt) = thd3 $ getStRef srt
      getRef _ = error "higher-order refinement types not supported in arguments of inductive data types" -- "Problem in the translation: a refinement type not translated to Cq.RefT (check definition of ILH.trRefType)"
-}

-- | Translation of an unreflected definition
transDefinition :: Ctx.TypingCtx -> Id -> ArrType -> [Coq.CoqTactic] -> [Coq.CoqDecl]
transDefinition γ f tp tacs =
  [Coq.Definition f (map (,False) args) ret (Coq.ProofBody $ destructs ++ cleanInductions (usedIHs tacs) tacs) Coq.Transparent]
  where
    argsNames = map fst $ filter ((\case Pi{} -> False; _ -> True) . argTp . snd) (argsTps tp) -- = map fst args
    destructs = map (\x -> Coq.DestructSubsetTerm (Coq.Var x) (Coq.ConjDestrPat [Coq.SingleIdPat x, Coq.SingleIdPat $ subsetWitnessNm x])) argsNames
    (args, ret) = matchFunctionType [] $ trArrType γ tp

-- *** Reflected definitions

-- | Translation of a reflected definition
transReflDefinition :: Ctx.TypingCtx -> Id -> ArrType -> LHTerm -> [Coq.CoqTactic] -> Either TransError [Coq.CoqDecl]
transReflDefinition γ f arrTp e tacs = do
  -- Expression splitted into its branches
  sepBranches <- separateBranches e (map (Var . fst) (argsTps arrTp))
  -- | used so that f_rel is recognized as globally defined in the translation
  γ'' <- Ctx.insertRelType (f, arrTp) γ
  γ' <- Ctx.insertHOArgs arrTp γ''
  let
      -- Translated branches
      branches' = map (createRelationBranch γ' f) sepBranches
      branches = uncurry zip $ first mkDistinct $ unzip branches'

      utransCond tm = if null forallsTm then utrSmpTerm fs tm else Coq.Project res where
        (forallsTm, tmBody) = extractApps [] tm
        fs = fetchFuncts γ
        Right (_, res) = synSmpTerm γ tm (f, (map (Var . fst) $ argsTps arrTp, []))

      -- TODO: This is a bug. The below line will produce Props, but we want bools so we can match on them
      -- The boolean expressions matched on in the branches
      condss = map (utrSmpTermsProp γ . snd3) sepBranches
      fs = fetchFuncts γ
      condTs' = concat condss
      -- | We can drop the negated conditions from the else cases of if-then-else
      notNegatedCond (Coq.Neg _) = False
      notNegatedCond (Coq.App (Coq.Def "negb") [_]) = False
      notNegatedCond (Coq.App zrel [_, _, ttOrFf]) = not (show zrel `elem` ["ltbZ_rel", "lebZ_rel", "gebZ_rel", "gtbZ_rel"] && show ttOrFf `elem` ["true", "false"])
      notNegatedCond (Coq.IsTrue (Coq.Bop Coq.Neqb s t)) = False
      notNegatedCond (Coq.Bop Coq.Neq s t) = False
      notNegatedCond (Coq.App neg _) | neg == Coq.Def Coq.negb = False
      notNegatedCond (Coq.Bop Coq.Neqb _ _) = False
      notNegatedCond (Coq.IsTrue p) = notNegatedCond p -- case only needed because of bug
      notNegatedCond t = True
      condTs = filter notNegatedCond condTs'
     -- Name of the relation and of the bridging lemmas
      fu = relDefName f
      f_fu = f ++ "__" ++ fu
      f_fu' = f_fu ++ "'"
      -- Name for the result of f (chosen different from the names of the arguments)
      resTp = trRefType γ $ retTp arrTp
      x = case resTp of
        Coq.Subset v _ _ -> v
        _ -> freshVar (map fst $ argsTps arrTp)
      -- Unrefined bindings of arguments
      xis = map (second utrRefType) $ argsTps arrTp
      xiVars = map (Coq.Var . fst) xis
      -- Refined bindings of arguments
      xirs = map (bimap (++ "_r") (trRefTypeAux True False γ)) $ argsTps arrTp
      xirVars = map (Coq.Var . fst) xirs
      xirProjArgs = map (\case (xr,Coq.Pack{}) -> Coq.App (Coq.Def projPackName) [Coq.Var xr]; (xr,_) -> Coq.Project $ Coq.Var xr) xirs
      -- The equivalence in the lemmas
      equivalence fuArgs =
        Coq.Equiv
          (Coq.Bop Coq.Eq (projectTm $ Coq.App (Coq.Def f) xirVars) (Coq.Var x))
          (Coq.App (Coq.Def fu) $ fuArgs ++ [Coq.Var x])
      -- The supplementary hypotheses for f_fu, xi = `(xir) for each i
      xiEqxir = zipWith (\xi -> \case (xr,Coq.Pack{}) -> Coq.Bop Coq.Eq (Coq.Var $ fst xi) (Coq.App (Coq.Def projPackName) [Coq.Var xr]); (xr,_) -> Coq.Bop Coq.Eq (Coq.Var $ fst xi) (Coq.Project (Coq.Var xr))) xis xirs

      substs = foldl (.) id $ zipWith (\(x_,_) -> \case (xr,Coq.Pack{}) -> sub x_ (Coq.App (Coq.Def projPackName) [Coq.Var xr]); (xr,_) -> sub x_ (Coq.Project $ Coq.Var xr)) xis xirs
      xir's = mapSnd substs xirs
      -- Auxiliary lemma f_fu' relating relation and definition of f
      refUnrefLemma' =
        mkCoqTheorem
          f_fu
          (map (,False) $ xir's ++ [(x, utrRefType $ retTp arrTp)])
          (equivalence xirProjArgs)
          [Coq.Custom "f__f_rel"]
      -- Lemma f_fu relating relation and definition of f
      refUnrefLemma =
        Coq.Definition
          f_fu'
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

      retArg = (x, resTp)
      retArgU = (x, unrefRocqType resTp)
      retArgU' = first (++ "'") retArgU

      indBranches ihs allTacs = {- traceFuncRet ["indBranches", show ihs, show allTacs, ", where \nmatchTacs:", show matchTacs] $ -} maybe (Finish [] ihs) extractInds (safeHead matchTacs) where
        matchTacs = filterMatchTacs allTacs

        extractInds :: Coq.CoqTactic -> IndTree
        extractInds tac = {- traceFuncRet ["extractInds", show ihs, show tac] $ -} case tac of
          Coq.Destruct (Coq.Var y) brs -> Induct y (map (\(c, (pats, ts)) -> ((c, pats), indBranches ihs ts)) brs) True
          Coq.Induction (Coq.Var y) brs -> Induct y (map (\(c, (pats, ts)) -> ((c, pats), indBranches (ihs ++ getIHs pats) ts)) brs) False
          Coq.Destruct condT cases -> Cond condT $ map (\(c,(pat,caseExpr)) -> (c,pat,indBranches ihs caseExpr)) cases
          -- Coq.Destruct condT [("true", (Coq.ConjDestrPat [], thenET)), ("false", (Coq.ConjDestrPat [], elseET))] -> Cond condT (indBranches ihs thenET) (indBranches ihs elseET)
          _ -> Finish (concatMap getIHAppls ihs) ihs where
            getIHAppls ih = fromMaybe [] $ find (not . null)
              [[(ih, wit:ts) | Coq.App (Coq.Var ih') (wit:ts) <- findSubterm (AppPat (TermPat $ Coq.Var ih) (replicate n AnyPat), True) tac, ih' == ih] |  n <- [8, 7..1]]

        filterMatchTacs [] = []
        filterMatchTacs (Coq.Concat ctacs:ts) = filterMatchTacs $ ctacs ++ ts
        filterMatchTacs (tac:ts) | (\case (Finish [] _) -> False; _ -> True) (extractInds tac) = tac:filterMatchTacs ts
        filterMatchTacs (_:ts) = {- trace ("discarding tactic: " ++show tac) $ -} filterMatchTacs ts

        getIHs :: Coq.CoqDestrPat -> [Id]
        getIHs pat = case pat of
          Coq.ConjDestrPat pats -> concatMap getIHs pats
          Coq.SingleIdPat ih -> [ih | ihName "" `isPrefixOf` ih]
          Coq.DisjDestrPat patBranches -> concatMap getIHs patBranches
          Coq.UnnamedIdPat -> []

      indBrs = indBranches [] tacs
      inductTac = mkInductiveSkeleton xis indBrs False
      funchoodTacs = [Coq.Concat [inductTac, Coq.Custom "rel_functionhood_body"]]
      h = ("H", Coq.Prop $ Coq.App (Coq.Def $ relDefName f) (map (Coq.Var . fst) xis ++ [Coq.Var $ fst retArg]))
      k = ("K", Coq.Prop $ Coq.App (Coq.Def $ relDefName f) (map (Coq.Var . fst) xis ++ [Coq.Var $ fst retArgU']))
      functionhoodLem =
        Coq.Definition
          (funcHoodLemName f)
          (map (,True) xis)
          (mkForallT
              [retArgU, retArgU', h, k]
              (Coq.Prop $ Coq.Bop Coq.Eq (Coq.Var $ fst retArgU) (Coq.Var $ fst retArgU'))
          )
          (Coq.ProofBody funchoodTacs)
          Coq.Opaque

      -- \| change the branches into a shape actually accepted by the 'mkReflAuxDecls' function
      -- by pulling all arguments which aren't of shape f_u ... out of the third argument and into the second
      fixBranch :: ((Id, Coq.RocqType), [Id]) -> (Id, Coq.RocqType)
      fixBranch ((f_c, tp), _) = (f_c, mkFuncType brArgs brRet)
        where
          (tpImplArgs, tpRet) = matchImplFunctionType [] tp

          isRelApp (_, Coq.Prop (Coq.App (Coq.Def f_u) _)) | relPostfix `isSuffixOf` f_u = True
          isRelApp _ = False

          relAntes = filter isRelApp tpImplArgs
          brArgs = tpImplArgs \\ relAntes
          brRet = case tpRet of
            Coq.Prop tpRetR -> Coq.Prop $ foldr (Coq.Impl . (\ (_, Coq.Prop r) -> r)) tpRetR relAntes
            _ -> tpRet
      relHints = Coq.AddHint Coq.ConstructorsHint (relDefName f) Coq.CoreDB
      funchoodHint = Coq.AddHint Coq.ResolveHint (funcHoodLemName f) Coq.GraphRelDB
      refRelThmHint = Coq.AddHint Coq.RewriteHint (relDefThmName f) Coq.GraphRelDB
      refRelLemHint = Coq.AddHint Coq.ResolveHint (relDefLemName f) Coq.GraphRelDB

      exLem : exLemHint : refRelRwLem : refRelRwHint : refRelRwAuxHint : refRelMkLem : refRelMkLemHint : pIRCLs =
        mkReflAuxDecls f retArg xirs xis condTs (map fixBranch branches) indBrs
      (packInstances, relConstrLems) = if not (null xis) then splitAt 1 pIRCLs else splitAt 0 pIRCLs

      rel = createRelation f arrTp (map (uncurry Coq.Constr . fst) branches)

      lookupDecl = Coq.Instance (f ++ "_lookup_rel") ["dictionary", "rel", f] [("lookup'", Coq.Def $ f ++ "_rel")]
      getFDecl = Coq.Instance (f ++ "_getF") ["getFunc", relDefName f] [("getF'", Coq.Def f)]
      Coq.AddHint _ rwLemName _ = refRelRwHint
      rwLookupDecl = Coq.Instance (f ++ "_lookup_rw") ["dictionary", "rwLem", f] [("lookup'", Coq.Def rwLemName)]
      firstOrder = all (\case (_, Coq.Subset {}) -> True; _ -> False) xirs

  return $
    transDefinition γ f arrTp tacs
      ++ [rel, relHints, lookupDecl, getFDecl, functionhoodLem, funchoodHint]
      ++ relConstrLems
      ++ (if True then [exLem, exLemHint, Coq.CoqMarkVisibility (Coq.ChangeVisibility f Coq.Opaque), refRelRwLem, refRelRwHint, refRelRwAuxHint] else [])
      ++ [rwLookupDecl, refUnrefLemma', refRelThmHint, refUnrefLemma, refRelLemHint, refRelMkLem, refRelMkLemHint]
      ++ (if firstOrder then packInstances else [])

-- | Create the inductive Prop relation for f
createRelation :: Id -> ArrType -> [Coq.CoqConstr] -> Coq.CoqDecl
createRelation f tp = Coq.CoqInductive (relDefName f) [] (concatProp $ utrArrType tp)
  where
    -- Add Prop as a type of the relation
    concatProp t = mkArrowT (map snd args ++ [ret]) (Coq.Sort Coq.PropSort)
      where
        (args, ret) = matchFunctionType [] t
{- (transArgs tp) Coq.PropSort
  where
    -- Add Prop as a type of the relation
    transArgs t = args ++ [(mkFresh "v" (map fst args), ret)]
      where
        (args, ret) = matchFunctionType [] $ utrArrType t-}

-- | Translates one branch of the function graph for the unrefined translation
createRelationBranch :: Ctx.TypingCtx -> Id -> (([LHSimpleTerm], LHSimpleTerm), [LHSimpleTerm], [Id]) -> ((Id, Coq.RocqType), [Id])
createRelationBranch γ f ((pats, body), antes, matchedVars) = {- traceFuncRet ["createRelationBranch", showP γ, f, "(("++show pats ++ ", " ++ show body ++ ")", show antes, show matchedVars++")", "hoArgs:", show hoArgs] $ -} ((nameBranch f antes pats False, prop), matchedVars)
  where
    fs = fetchFuncts γ
    hoArgs = fetchHOArgs False γ
    hoArgMap :: Map.Map Id Coq.RocqType
    hoArgMap = Map.fromList hoArgs
    -- Creating the type of the constructor
    -- The relation for f applied to the translation of the patterns and “returning” the translation of the body
    fuArgs = Coq.App (Coq.Def $ relDefName f) $ trPats ++ [trBody]

    -- | We can use utrSmpTerm directly because the free variables are already bound as part of patFV
    transSTm :: [LHSimpleTerm] -> ([(Id, Coq.RocqType, (Id, [Coq.CoqTerm]))], [Coq.CoqTerm])
    transSTm [] = ([], [])
    transSTm tms = second (:map (utrSmpTerm fs) rTl) $ utrSmpTermGenericAux γ (extracted, rHd) True where
      rHd:rTl = rs
      -- | the fold is needed to avoid duplicating result variables
      (extracted, rs) = foldr (\r (φ, r_cores) -> second (:r_cores) $ extractApps φ r) ([], []) tms
    (patForalls, trPats) = transSTm pats
    (anteForalls, trAntes) = transSTm antes
    (foralls, trBody) = utrSmpTermGeneric γ body True
    -- Adding the relations as hypothesis
    prop' = foldr (uncurry3 ppForall) fuArgs (foralls++patForalls)

    -- | cancel double negations (from ifs with negated conditions) and convert the bool to a Prop 
    toProp (Coq.Neg (Coq.Neg p)) = toProp p
    toProp p = mkIsTrue p
    {-toProp (Coq.Neg p) = Coq.Bop Coq.Eq p Coq.bfalse
    toProp p = {- Coq.IsTrue p -} Coq.Bop Coq.Eq p Coq.btrue-}

    -- | add the relations for the result variables in the antecedents and the nthe antecedents as hypothesis to prop'
    anteProp = foldr (uncurry3 ppForall) (foldr (Coq.Impl . toProp) prop' trAntes) anteForalls
    -- Adding the free variables of the patterns and antecedents
    patFVs = Set.toList . flip Set.difference (Set.fromList fs) . Set.unions $ map freeVars (pats ++ antes)
    -- TODO: Can we somehow figure out the types here?
    patArgs = map (\x -> (x, fromMaybe Coq.Hole $ Map.lookup x hoArgMap)) patFVs
    prop = mkForallT patArgs $ Coq.Prop anteProp

-- | From an LHTerm with matches, create the graph of the term
-- This function only works if induction is done on one of the arguments of the function
-- In the resulting branches, the expression is a simple term (necessary for the translation)
-- We σ-reduce the term before decomposing, so that matches are pushed to the
-- top and let to the bottom
-- A branch in the result is made of a list of variables and constructors
-- applied to variables associated to an LH simple term, e.g.:
-- ([x, C y1 y2, z, C' y3], True)
-- TODO: problem with case for booleans (and any introduced non-inductive algebraic types) that are simply if-the-else
separateBranches ::
  -- | The term for which to create a graph
  LHTerm ->
  -- | The list of arguments of the Haskell function
  [LHSimpleTerm] ->
  -- | A pair consisting of (the list of patterns, the definien), the list of assumptions and of the list of matched variables
  Either TransError [(([LHSimpleTerm], LHSimpleTerm), [LHSimpleTerm], [Id])]
separateBranches e = {- traceFuncRet ["separateBranches", show e] $ -} separateBranches' (sigmaReduce e)
  where
    separateBranches' (Let x _ (BasicTerm cond) (Case (Var x') [("False", [], elseE), ("True", [], thenE)] _)) args | x == x' = do
      thenBrs <- map (\(x_,y,z) -> (x_,cond:y,z)) <$> separateBranches' thenE args
      elseBrs <- map (\(x_,y,z) -> (x_,Neg cond:y,z)) <$> separateBranches' elseE args
      return $ thenBrs ++ elseBrs
    --separateBranches' (Let x (BasicTerm cond) (Case (Var x') cases _)) args | x == x' = do
    separateBranches' (Case matchedExpr cases _) args = concat <$> mapM separateBranch cases where
      separateBranch :: (Id, [Id], LHTerm) -> Either TransError [(([LHSimpleTerm], LHSimpleTerm), [LHSimpleTerm], [Id])]
      separateBranch (c, ys, body) =
        map (\(destrParams,conds,c_) -> (destrParams,newCond++conds,c_++ [x | Var x <- [matchedExpr]]))
          <$> ( args' >>= separateBranches' body )
        where
          (args', newCond) = case matchedExpr of
            -- | add the variable x inside matchedExpr (if any) to the list of matched variables in the branch
            Var x -> (replaceVarByConstr x (c, ys) args, [])
            _ -> (Right args, [cond]) where
              cond = case c of
                "True" -> matchedExpr
                "False" -> Neg matchedExpr
                _ -> Bop Eq matchedExpr (App (Var c) (map Var ys))
    separateBranches' Undefined _ = return []
    separateBranches' e' args = singleton . (,[],[]) . (args,) <$> simplifyLHTerm e'

-- ** Expressions: case (where substitutions of recursive calls are created)

-- | Build the typing context for branches
branchCtx ::
  -- | Current context
  Ctx.TypingCtx ->
  -- | Branch
  (Id, [Id], LHTerm) ->
  -- | The variable being matched against
  Maybe Id ->
  -- | Type of that variable
  RefType ->
  -- | Type of the consructor for this branch
  ArrType ->
  -- | Updated context
  Either TransError Ctx.TypingCtx
branchCtx γ (ci, ys, _) xO (RefType x' (TDat tc) rx) (ArrType args ret) = do
  (σ, argsSubst) <- substArgs args (map Var ys)
  let -- Bindings for each ys
      bindsYs = zip ys argsSubst
  case xO of
    Just x ->
      let
        bindX = (x, RefType x' (TDat tc) $ Bop And rx (Bop And rci' req))
        -- req is a equality between x/x' and the pattern
        req = Bop Eq (Var x') (App (Var ci) (map Var ys))
        -- rci' is the refinement of the return type of tpci, with the substitutions to ys
        rci' = foldr (uncurry substSmpTerm) (argRef ret) ((Var x', argName ret) : σ)
      in Ctx.replace x (bindX : bindsYs) γ
    Nothing -> foldM (flip Ctx.insertRefType) γ bindsYs
branchCtx _ _ _ _ _ = Left $ CheckingErr "Variable in match does not have an inductive type"

-- * Post-processing of translations

-- | Remove superfluous induct tactics in a list of tactics obtained from the
-- translation of a term, based on the ihs used as recursive calls
-- Also replace named induction hypothesis by _ (experimental, don't think it
-- always works)
--
-- > Ex: generalize dependent n; induction m as [|m' IHm']; intros.
-- > --> destruct m.
cleanInductions :: [Id] -> [Coq.CoqTactic] -> [Coq.CoqTactic]
cleanInductions ihs = map recurse
  where
    recurse tac = case tac of
      Coq.Concat [gd@(Coq.GeneralizeDependent _), Coq.Induction tm branches, intros@(Coq.Intros _)] ->
        let (filteredBranches, noIH) = unzip $ map filterBranch branches
         in if and noIH
              then Coq.Destruct tm filteredBranches
              else Coq.Concat [gd, Coq.Induction tm filteredBranches, intros]
      Coq.Concat tacs -> Coq.Concat (cleanInductions ihs tacs)
      Coq.Destruct tm branches ->
        Coq.Destruct tm $ map (second (second (cleanInductions ihs))) branches
      Coq.SplitB tacs1 tacs2 ->
        Coq.SplitB (cleanInductions ihs tacs1) (cleanInductions ihs tacs2)
      Coq.SubgoalMarkers tacs ->
        Coq.SubgoalMarkers $ cleanInductions ihs tacs
      _ -> tac
    -- Replace superfluous IHs by _ in patterns. Also returns true if all IHs have been thus erased
    -- TODO: This function should be put on top-level for readability
    filterBranch (x, (Coq.ConjDestrPat ys, tacs)) =
      let tacs' = cleanInductions ihs tacs
          (ys', noIH) = filterPat ys
       in ((x, (Coq.ConjDestrPat ys', tacs')), noIH)
    filterBranch _ = error "Badly formed induction branch."
    -- This first case should not be necessary
    filterPat (y@(Coq.SingleIdPat _) : hole@Coq.UnnamedIdPat : ys) =
      let (ys', noIH) = filterPat ys in (y : hole : ys', noIH)
    filterPat (y@(Coq.SingleIdPat _) : Coq.SingleIdPat ih : ys)
      | take 2 ih == "IH" =
          let (ys', noIH) = filterPat ys
           in if ih `elem` ihs
                then (y : Coq.SingleIdPat ih : ys', False)
                else (y : Coq.UnnamedIdPat : ys', noIH)
    filterPat (y@(Coq.SingleIdPat _) : ys) =
      let (ys', noIH) = filterPat ys in (y : ys', noIH)
    filterPat [] = ([], True)
    filterPat _ = error "Badly formed pattern in induction tactic"

-- | List the induction hypothesis that appear in the list of tactics
-- obtained from the translation of a term
usedIHs :: [Coq.CoqTactic] -> [Id]
usedIHs = trace "TODO: define TypedTranslation.usedIHs or remove it." undefined

-- * Utility functions

-- | In a list @ids@ of simple terms, replace the first occurence of the variable @x@ by @c ys@
replaceVarByConstr :: Id -> (Id, [Id]) -> [LHSimpleTerm] -> Either TransError [LHSimpleTerm]
replaceVarByConstr x (c, ys) ids =
  case uncons post of
    Just found -> return $ pre ++ (App (Var c) (map Var ys) : snd found)
    Nothing | any (occurs (IdPat x, True)) ids -> return $ map (sub x (App (Var c) $ map Var ys)) ids
    Nothing ->
      Left . TransErr $
        "Match on variable "
          ++ x
          ++ " is incorrect in context: " ++ show ids ++ ": It is not bound by a previous match and additionally it either isn't an argument of the function or has been already matched."
    where
      (pre, post) = span (/= Var x) ids
      occurs :: SubtermPattern LHSimpleTerm -> LHSimpleTerm -> Bool
      occurs = hasMatch

-- | Create a name for a constructor based on the patterns.
-- The flag takeVars indicates if we want the variables alone between the constructors
-- Used with true to create names of IH, and with false to create names for the relation
nameBranch :: Id -> [LHSimpleTerm] -> [LHSimpleTerm] -> Bool -> Id
nameBranch f [] [] _ = relDefBranchName f
nameBranch f antes pats takeVars = {- traceFuncRet ["nameBranch", f, show antes, show pats, show takeVars] $ -} foldl (++) base $ concatMap getConstructor pats ++ map anteSign antes
  where
    getConstructor v = case (v, takeVars) of
      (Var x, True) -> ["_" ++ x]
      (Var x, False) -> ["_" ++ x | isDC x]
      (App (Var x) _, _) -> ["_" ++ x]
      _ -> []
    anteSign (Neg (Neg s)) = anteSign s
    anteSign (Neg _) = "_false"
    anteSign _ = "_true"
    base = if null antes && all (null . getConstructor) pats then relDefBranchName f else f

-- | Selfification of variables
selfification :: Id -> RefType -> RefType
selfification y (RefType z a r') = RefType y a $ sub z (Var y) r' -- RefType z a $ Bop And r' (Bop Eq (Var y) (Var z))

-- | Trivial refinement of a builtin type
trivialRefTp :: LHType -> RefType
trivialRefTp a = RefType "VV" a (Var "true")
