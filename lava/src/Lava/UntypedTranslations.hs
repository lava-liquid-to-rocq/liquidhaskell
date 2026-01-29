{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}

-- | Translation from ILH to Coq via bidirectional typechecking
module Lava.UntypedTranslations where

import Data.Bifunctor (second)
-- (Id, mapSnd, isSuffixOf, sub)

import Data.List ((\\))
import qualified Data.Map as Map
import qualified Data.Set as Set (toList)
import Data.Tuple.Extra (uncurry3)
import Lava.Coq (unrefinedConstrName)
import qualified Lava.Coq as Coq
import Lava.CoqSyntaxUtil
import Lava.CoqUtil (funcHoodLemName, mkIsTrue, mkUPackName, ppForall, projectTm, relDefName, relPostfix, toPack, toUPack, upackFunctName, upackRelName)
import Lava.InternalLH as ILH
import Lava.PaperUtils
import qualified Lava.TypingContext as Ctx
import Lava.Util
import Prelude

-- * Unrefined translations

-- | Unrefined translation of any simple term
-- This only works on terms *not* containing applications (the terms must come from extractApps)
-- TODO (CR): that restriction is completely unnecessary, quite restrictive and should be removed (this requires some extra work though)
utrSmpTerm :: [Id] -> LHSimpleTerm -> Coq.CoqTerm
utrSmpTerm fs r = {- traceFuncRet ["utrSmpTerm", show fs, showP r] $ -} case r of
  Var x | isDC x -> Coq.Cr (Coq.unrefinedConstrName x)
  Var x | x `elem` fs -> Coq.Project $ Coq.Var x
  Var x -> Coq.Var x
  IntLit i -> Coq.IntLiteral i
  StringLit _ -> error "No strings in Coq yet"
  FloatLit _ -> error "No floats in Coq yet"
  Bop Plus r1 r2 -> Coq.Bop Coq.PlusU (utrSmpTerm fs r1) (utrSmpTerm fs r2)
  Bop Minus r1 r2 -> Coq.Bop Coq.MinusU (utrSmpTerm fs r1) (utrSmpTerm fs r2)
  Bop Times r1 r2 -> Coq.Bop Coq.TimesU (utrSmpTerm fs r1) (utrSmpTerm fs r2)
  Bop Div r1 r2 -> Coq.Bop Coq.DivU (utrSmpTerm fs r1) (utrSmpTerm fs r2)
  Bop Mod r1 r2 -> Coq.Bop Coq.ModU (utrSmpTerm fs r1) (utrSmpTerm fs r2)
  Bop bop r1 r2 -> Coq.Bop (trBop bop) (utrSmpTerm fs r1) (utrSmpTerm fs r2)
  Neg r' -> Coq.App (Coq.Def Coq.negb) [utrSmpTerm fs r']
  App (Var c) args | isDC c -> Coq.App (Coq.Cr $ Coq.unrefinedConstrName c) (map (utrSmpTerm fs) args)
  App (Var f) args | f `elem` fs -> Coq.App (Coq.Def $ relDefName f) (map (utrSmpTerm fs) args)
  App {} -> error $ "Calling utrSmpTerm with a term containing applications:" ++ show r

-- | Unrefined translation of simple terms to a pair of the environment with the
-- relations and the core of the translated term
-- the final flag indicates whether this function is called to create a graph relations and thus the packs will be uPacks
utrSmpTermGeneric :: Ctx.TypingCtx -> LHSimpleTerm -> Bool -> ([(Id, Coq.RocqType, (Id, [Coq.CoqTerm]))], Coq.CoqTerm)
utrSmpTermGeneric γ r = {- traceFuncRet ["utrSmpTermGeneric", "...", showP r] $ -} utrSmpTermGenericAux γ (extractApps [] r)

utrSmpTermGenericAux :: Ctx.TypingCtx -> ([(LHSimpleTerm, Id)], LHSimpleTerm) -> Bool -> ([(Id, Coq.RocqType, (Id, [Coq.CoqTerm]))], Coq.CoqTerm)
utrSmpTermGenericAux γ (φ, r_core) isUnrefined = {- traceFuncRet ["utrSmpTermGenericAux", showP γ, showP φ, showP r_core, showP isUnrefined] $ -} (map createForalls φ, utrSmpTerm fs r_core)
  where
    relMap = constructMap γ
    fs = fetchFuncts γ
    fArgs = fetchFunctArgs γ

    lookupRelTp f = {- traceFuncRet ["lookupRelTp" ,f] $ -} Map.lookup (relDefName f) relMap
    lookupRel f = case lookupRelTp f of
      Just _ -> {- Coq.Def $ -} relDefName f
      Nothing -> show $ (if isUnrefined then upackGetRel else packGetRel) (Coq.Def f)

    -- An environment containing the translations of the applications to refinements
    createForalls :: (LHSimpleTerm, Id) -> (Id, Coq.RocqType, (Id, [Coq.CoqTerm]))
    createForalls (App (Var f) args, z) =
      let fArgTps = snd <$> find ((== f) . fst) fArgs
          transArg :: Int -> LHSimpleTerm -> Coq.CoqTerm
          transArg i tm = tmT
            where
              tmTp = (!! max 0 (i - 1)) <$> fArgTps
              tmT = case tmTp of
                Just (_, gTp@(RefType _ Pi {} _)) -> case tm of
                  Var g ->
                    if g `elem` fs
                      then ltacTerm $ Coq.Concat [Coq.Pose "Rel" (Coq.Def $ relDefName g), Coq.Pose "Funct" (Coq.Def $ funcHoodLemName g), Coq.Custom "buildUPackG Rel Funct"]
                      -- Coq.InlineInstance [(upackRelName, Coq.Def $ relDefName g), (upackFunctName, Coq.Def $ funcHoodLemName g)]
                      else Coq.App (Coq.Def Coq.projPackName) [Coq.Var g]
                    where
                      castOp = if g `elem` fs then mkUPackName else Coq.projPackName
                  _ -> utrSmpTerm fs tm
                _ -> utrSmpTerm fs tm
          args' = zipWith transArg [1 ..] args
       in (z, fromMaybe Coq.Hole (lookupRelTp f), (lookupRel f, args' ++ [Coq.Var z]))
    createForalls (Bop op r1 r2, z) =
      let r1' = utrSmpTerm fs r1
          r2' = utrSmpTerm fs r2
          (relResTp, opRel) = case op of
            Lt -> (Coq.boolTp, "ltbZ_rel")
            Leq -> (Coq.boolTp, "lebZ_rel")
            Plus -> (Coq.Builtin Coq.CTInt, "addZ_rel")
            Minus -> (Coq.Builtin Coq.CTInt, "subZ_rel")
            Times -> (Coq.Builtin Coq.CTInt, "multZ_rel")
            Div -> (Coq.Builtin Coq.CTInt, "divZ_rel")
            Mod -> (Coq.Builtin Coq.CTInt, "modZ_rel")
            _ -> error $ "this operation is currently not yet fully supported " ++ show op
       in (z, relResTp, (opRel, [r1', r2', Coq.Var z]))
    createForalls (App _ _, _) = error "Fix: applications should start with an identifier"
    createForalls _ = error "Expected application in map of applications to fresh variables φ"

utrSmpTermPropAux :: [(Id, Coq.RocqType, (Id, [Coq.CoqTerm]))] -> Coq.CoqTerm -> Coq.CoqTerm
utrSmpTermPropAux foralls r' = if null foralls then mkIsTrue r' else foldr (uncurry3 ppForall) r'' initForalls
  where
    initForalls :: [(Id, Coq.RocqType, (Id, [Coq.CoqTerm]))]
    initForalls = init foralls
    (z, zTp, (fu, args_z)) = last foralls
    args = init args_z
    r'' = case r' of
      Coq.Var _ -> Coq.App (Coq.Def fu) (args ++ [Coq.btrue])
      {-
      Coq.Bop Coq.Eq (Coq.Var z_) tm | z_ == z -> Coq.App (Coq.Def fu) (args ++ [tm])
      Coq.Bop Coq.Eqb (Coq.Var z_) tm | z_ == z -> Coq.App (Coq.Def fu) (args ++ [tm])
      Coq.Bop Coq.EqBool (Coq.Var z_) tm | z_ == z -> Coq.App (Coq.Def fu) (args ++ [tm])
      Coq.Bop Coq.EqProp (Coq.Var z_) tm | z_ == z -> Coq.App (Coq.Def fu) (args ++ [tm])
      Coq.Bop Coq.EqualB (Coq.Var z_) tm | z_ == z -> Coq.App (Coq.Def fu) (args ++ [tm])
      Coq.Bop Coq.Eq tm (Coq.Var z_) | z_ == z -> Coq.App (Coq.Def fu) (args ++ [tm])
      Coq.Bop Coq.Eqb tm (Coq.Var z_) | z_ == z -> Coq.App (Coq.Def fu) (args ++ [tm])
      Coq.Bop Coq.EqBool tm (Coq.Var z_) | z_ == z -> Coq.App (Coq.Def fu) (args ++ [tm])
      Coq.Bop Coq.EqProp tm (Coq.Var z_) | z_ == z -> Coq.App (Coq.Def fu) (args ++ [tm])
      Coq.Bop Coq.EqualB tm (Coq.Var z_) | z_ == z -> Coq.App (Coq.Def fu) (args ++ [tm])
      -}
      _ -> Coq.Forall [(z, zTp)] $ Coq.Impl (Coq.App (Coq.Def fu) args_z) (mkIsTrue r')

-- | unrefined translation of a bunch of nested conditions to propositions
utrSmpTermsProp :: Ctx.TypingCtx -> [LHSimpleTerm] -> [Coq.CoqTerm]
utrSmpTermsProp _ [] = []
utrSmpTermsProp γ (r : rs) = {- traceFuncRet ["utrSmpTermsProp", show (r : rs)] $ -} zipWith utrSmpTermPropAux forallss rs'
  where
    foldlF :: ([[(Id, Coq.RocqType, (Id, [Coq.CoqTerm]))]], [(LHSimpleTerm, Id)], [Coq.CoqTerm]) -> LHSimpleTerm -> ([[(Id, Coq.RocqType, (Id, [Coq.CoqTerm]))]], [(LHSimpleTerm, Id)], [Coq.CoqTerm])
    foldlF (foralls, lhForalls, prevs) r = (foralls ++ [fr \\ concat foralls], lhForalls', prevs ++ [r'])
      where
        extractRes@(lhForalls', _) = extractApps lhForalls r
        (fr, r') = utrSmpTermGenericAux γ extractRes False
    (forallss, _, rs') = foldl foldlF (let (hdFrs, hdR') = utrSmpTermGeneric γ r False in ([hdFrs], fst $ extractApps [] r, [hdR'])) rs

-- | Unrefined translation of simple terms to propositions
utrSmpTermProp :: Ctx.TypingCtx -> LHSimpleTerm -> Coq.CoqTerm
utrSmpTermProp γ r = utrSmpTermPropAux foralls r'
  where
    (foralls, r') = utrSmpTermGeneric γ r False

-- | Returns an association of each application in the input to a fresh variable and the term where replacements of the applications by the associated variable have been done
-- In the list associating terms to variables, the replacements have also been done
-- Ex: extractApps ((f 0 1) + (f 0 1) + x) = ([(f 0 1, f_res)], f_res + f_res + x)
extractApps :: [(LHSimpleTerm, Id)] -> LHSimpleTerm -> ([(LHSimpleTerm, Id)], LHSimpleTerm)
extractApps env r = {- traceFuncRet ["extractApps", show r] $ -} case r of
  Var {} -> (env, r)
  StringLit {} -> (env, r)
  FloatLit {} -> (env, r)
  IntLit {} -> (env, r)
  Neg r' -> second Neg $ extractApps env r'
  App (App f' ts') ts -> extractApps env (App f' $ ts' ++ ts)
  App (Var c) args | isDC c -> (env', App (Var c) args')
    where
      (env', args') = foldr seqNames (env, []) args
  App (Var f_rel) args | relPostfix `isSuffixOf` f_rel -> (env, App (Var f_rel) args)
  App (Var f) args ->
    let (env', args') = foldr seqNames (env, []) args
        r' = App (Var f) args'
     in case lookup r' env' of
          Just z -> (env', Var z)
          Nothing ->
            let z = fresh f env'
             in (env' ++ [(r', z)], Var z)
  Bop zop r1 r2
    | zop `elem` [Lt, Leq, Geq, Gt] ->
        let (env1, r1') = extractApps env r1
            (env', r2') = extractApps env1 r2
         in (env', Bop zop r1' r2')
  Bop zop r1 r2
    | zop `elem` [Plus, Minus, Times, Div, Mod] ->
        let (env1, r1') = extractApps env r1
            (env', r2') = extractApps env1 r2
            res = Bop zop r1' r2'
         in case lookup res env' of
              Just z -> (env', Var z)
              Nothing ->
                let zopS = case zop of
                      Plus -> "addZ"
                      Minus -> "subZ"
                      Times -> "multZ"
                      Div -> "divZ"
                      Mod -> "modZ"
                    z = fresh zopS env'
                 in (env' ++ [(res, z)], Var z)
  App {} -> error "App not starting with an id"
  Bop bop r1 r2 ->
    let (env1, r1') = extractApps env r1
        (env2, r2') = extractApps env1 r2
     in (env2, Bop bop r1' r2')
  where
    seqNames arg (curEnv, curArgs) = second (: curArgs) $ extractApps curEnv arg
    fresh f zs =
      -- Number of calls to f
      let nbOfCalls = foldr ((+) . isF) 0 zs
       in if nbOfCalls == 0
            then f ++ "res"
            else f ++ "_res_" ++ show (nbOfCalls + 1)
      where
        isF :: (LHSimpleTerm, Id) -> Int
        isF (App (Var f') _, _) | f' == f = 1
        isF _ = 0

-- | Unrefined translation of LHType
utrLHType :: LHType -> Coq.RocqType
utrLHType tp = case tp of
  Buildin b -> Coq.Builtin $ trBuiltin b
  TDat tc -> Coq.TC tc' []
    where
      tc' = case tc of
        _ | tc == boolTpName -> "bool"
        _ | tc == unitTpName -> "Unit"
        _ -> tc
  Pi (_, RefType _ a _) cod -> toUPack ts tT
    where
      (xs, RefType _ t _) = unapplyPi cod
      ts = map utrLHType (a : map (\(_, RefType _ typ _) -> typ) xs)
      tT = utrLHType t

-- | Unrefined translation of RefType
utrRefType :: RefType -> Coq.RocqType
utrRefType (RefType _ tp _) = utrLHType tp

-- | Unrefined translation of ArrType
utrArrType :: ArrType -> Coq.RocqType
utrArrType (ArrType args ret) = foldr buildFun (utrRefType ret) args
  where
    buildFun (_, tp) = Coq.Arrow $ utrRefType tp

-- * Refined translations

-- | Refined translation of RefType
-- the flag indicates whether free variables are assumed to be refined
--  (as is the case in specs) and thus projected in the translated refinements
-- the first flag indicates whether this is the argument type of a larger function type
trRefTypeAux :: Bool -> Bool -> Ctx.TypingCtx -> RefType -> Coq.RocqType
trRefTypeAux argTp inSpec γ rt0@(RefType x0 tp0 r0) = case tp0 of
  Buildin b -> Coq.Subset x0 (Coq.Builtin $ trBuiltin b) r'
  _ | tp0 == unitTp -> Coq.Subset x0 (Coq.TC "Unit" []) r'
  _ | tp0 == boolTp -> Coq.Subset x0 (Coq.TC "bool" []) r'
  TDat tc -> Coq.Subset x0 (Coq.TC tc []) $ Coq.And (Coq.getTCRef x0 tc) r'
  Pi (x, RefType x' xTp xRef) ret@(RefType y yTp yRef) ->
    if argTp
      then
        {-traceFuncRet ["trRefTypeAux", show argTp, show inSpec, "...", show rt0] $ -} toPack ((x, xTpT) : xsT) (trRefTypeAux False True γ finalRet)
      else
        foldl
          (\rt (Coq.Subset y yTp py) -> Coq.FAType (y, Coq.Subset y yTp py) rt)
          (trRefTypeAux False True γ ret)
          (map (\(y, RefType y0 yTp py) -> trRefTypeAux False True γ (RefType y yTp (sub y0 (Var y) py))) xRTps)
    where
      xTpT = trRefTypeAux False True γ (RefType x xTp (sub x' (Var x) xRef))
      (xs, finalRet) = unapplyPi ret
      xsT :: [(Id, Coq.RocqType)]
      xsT = map (uncurry transRT) xs

      transRT y (RefType y0 yTp py) = (y, trRefTypeAux False True γ (RefType y yTp (sub y0 (Var y) py)))
      fixProjs tm = foldr (\y -> replaceSubterm (TermPat (Coq.Project (Coq.Def y)), True) (Coq.Var y)) tm boundVars
  where
    (xRTps, ret@(RefType x _ _)) = unapplyPi rt0
    r_ = utrSmpTermProp γ r0
    boundVars = map fst xRTps
    fv_r = {- traceFuncRet ["rt0: ", show rt0, "boundVars:", show boundVars, "fv_r: "] $ -} if inSpec then Set.toList (freeVars r0) \\ (x0 : boundVars) else []
    projFixes y =
      replaceSubterm (TermPat (Coq.Project (Coq.Project (Coq.Def y))), True) (Coq.Project (Coq.Def y))
        : [ replaceSubterm (TermPat (Coq.App (Coq.Def Coq.projPackName) [Coq.Project (Coq.Def y)]), True) (Coq.App (Coq.Def Coq.projPackName) [Coq.Var y]),
            replaceSubterm (TermPat (Coq.App (Coq.Def mkUPackName) [Coq.Project (Coq.Def y)]), True) (Coq.App (Coq.Def mkUPackName) [Coq.Var y])
          ]
    r' = foldr (\y -> foldl (.) id (projFixes y ++ [sub y (projectTm (if isDC y then Coq.Cr y else Coq.Def y))])) r_ fv_r

trRefType :: Ctx.TypingCtx -> RefType -> Coq.RocqType
trRefType = trRefTypeAux False False

-- | Refined translation of ArrType
-- | Invariant: the names of the arguments (outside the refinement) should not change
trArrType :: Ctx.TypingCtx -> ArrType -> Coq.RocqType
trArrType γ (ArrType args ret) =
  foldr Coq.FAType (trRefTypeAux False True γ ret) (mapSnd (trRefTypeAux True True γ) args)

-- * Translations of builtins

-- | Translation of builtin to Coq (to remove maybe)
trBuiltin :: BuildInTps -> Coq.Builtin
trBuiltin Integer = Coq.CTInt
trBuiltin Double = error "Doubles not yet supported in Coq (function UntypedTranslations.trBuiltin)"
trBuiltin String = error "Strings not yet supported in Coq (function (UntypedTranslations.trBuiltin)"

-- | Translation of ILH binary operators to Coq binary operators
trBop :: Bop -> Coq.Bop
trBop Plus = Coq.Plus
trBop Minus = Coq.Minus
trBop Times = Coq.Times
trBop Div = Coq.Div
trBop Mod = Coq.Mod
trBop Eq = Coq.EqualB
trBop Neq = Coq.Neqb
trBop Leq = Coq.Leqb
trBop Geq = Coq.Geqb
trBop Lt = Coq.Ltb
trBop Gt = Coq.Gtb
trBop And = Coq.Andb
trBop Or = Coq.Orb
trBop Impl = Coq.ImplB

-- * Conversions of ILH terms

-- | Reduction from ILH terms to ILH simple terms
simplifyLHTerm :: LHTerm -> Either TransError LHSimpleTerm
simplifyLHTerm (BasicTerm r) = Right r
simplifyLHTerm (Let x e1 e2) = do
  r1 <- simplifyLHTerm e1
  e2' <- substSmpTmTm r1 x e2
  simplifyLHTerm e2'
simplifyLHTerm e = Left . TransErr $ "Cannot reduce the expression " ++ show e ++ " to a simple term."

-- | implements the function pp from the POPL paper
sigmaReduce :: LHTerm -> LHTerm
sigmaReduce expr = {-traceFuncRet ["sigmaReduce", show e] $ -} case expr of
  (Annot e _) -> sigmaReduce e
  (QMark e1 _) -> sigmaReduce e1
  (SEqn _ r2 _) -> sigmaReduce (BasicTerm r2)
  BasicTerm _ -> expr
  -- The case of if-then-else is subsumed by the one for pattern matching
  Lambda {} -> error "Cannot σ-reduce λ-expression."
  (Case y alts b) -> Case y (mapThd sigmaReduce alts) b
  Undefined -> Undefined
  Let x _ e | not (hasMatch xPat e) -> sigmaReduce e
    where
      xPat :: SubtermPattern LHTerm
      xPat = (IdPat x, True)
  Let x (BasicTerm r) (Case (Var x') cases rC) | x == x' -> sigmaReduce $ Case r (mapThd (sub x r) cases) rC
  Let x ex e -> case ex of
    BasicTerm r -> sigmaReduce $ sub x r e
    Lambda {} -> error "Cannot σ-reduce let-bound λ-expression."
    Annot tm _ -> sigmaReduce $ Let x tm e
    QMark tm _ -> sigmaReduce $ Let x tm e
    SEqn _ tm _ -> sigmaReduce $ sub x tm e
    lt@Let {} -> sigmaReduce $ Let x (sigmaReduce lt) e
    -- Again the if-then-else case is subsumed by the one for pattern matches
    (Case r alts rC) -> Case r (mapThd (\t -> sigmaReduce (Let x t e)) alts) rC
    Undefined -> error "Cannot reduce let-bound Undefined constructor."

constructMap :: Ctx.TypingCtx -> Map.Map Id Coq.RocqType
constructMap γ = {- traceFuncRet ["constructMap", show γ] $ -} Map.fromList relTs
  where
    rels = concatMap (\case (rel, Ctx.ΓRel _ ret) -> [(rel, ret)]; _ -> []) γ
    relTs = mapSnd utrLHType rels

fetchFuncts :: Ctx.TypingCtx -> [Id]
fetchFuncts = concatMap (\case (f, Ctx.ΓDef _) -> [f]; _ -> [])

fetchHOArgs :: Bool -> Ctx.TypingCtx -> [(Id, Coq.RocqType)]
fetchHOArgs isRefined γ = concatMap (\case (f, Ctx.ΓFHOVar rt) -> [(f, toRocq rt)]; _ -> []) γ
  where
    toRocq rt@(RefType f Pi {} rf) = if isRefined then trRefTypeAux True False γ rt else utrRefType rt
    toRocq _ = error "IMPOSSIBLE"

fetchFunctArgs :: Ctx.TypingCtx -> [(Id, [(Id, RefType)])]
fetchFunctArgs = concatMap (\case (f, Ctx.ΓDef arrTp) -> [(f, argsTps arrTp)]; _ -> [])
