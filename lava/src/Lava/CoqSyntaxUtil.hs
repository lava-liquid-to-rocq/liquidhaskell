{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OrPatterns #-}

-- | Utility functions manipulating Rocq terms and types
module Lava.CoqSyntaxUtil where

import Lava.Coq
import Lava.Util

-- * Tactic names for "projections" out of packs

getPackFName = "getPackF"

getPackRelName = "getPackRel"

getPackCorName = "getPackCor"

getPackFunctName = "getPackFunct"

getUPackRelName = "getUPackRel"

getUPackFunctName = "getUPackFunct"

-- * Wrappers for Rocq terms

mkCoqLemma :: Id -> [((Id, RocqType), Bool)] -> RocqType -> [CoqTactic] -> Decl
mkCoqLemma f args ret tacs = Definition f args ret (ProofBody tacs) Opaque

mkCoqTheorem :: Id -> [((Id, RocqType), Bool)] -> CoqTerm -> [CoqTactic] -> Decl
mkCoqTheorem f args ret = mkCoqLemma f args (Prop ret)

-- | Wrapper for Forall, defined as id for empty argument list
mkForall :: [(Id, RocqType)] -> CoqTerm -> CoqTerm
mkForall args r = if null args then r else Forall args r

-- | Wrapper for Exists, defined as id for empty argument list
mkExists :: [(Id, RocqType)] -> CoqTerm -> CoqTerm
mkExists [] r = r
mkExists ((_, Prop prp@(Bop Eq _ trueOrFalse)) : tl) r | trueOrFalse `elem` [btrue, bfalse] = mkAnd [prp, mkExists tl r]
mkExists (hd : tl) r = case mkExists tl r of
  Exists args r' -> Exists (hd : args) r'
  res -> Exists [hd] res

-- | Wrapper for ForallT, defined as id for empty argument list
mkForallT :: [(Id, RocqType)] -> RocqType -> RocqType
mkForallT args ret = foldr FAType ret args

-- | Wrapper for ForallT, defined as id for empty argument list
mkArrowT :: [RocqType] -> RocqType -> RocqType
mkArrowT args ret = foldr Arrow ret args

-- | Wrapper for And, defined as TT for empty conjuncts list
mkAnd :: [CoqTerm] -> CoqTerm
mkAnd args = if null args' then TT else foldl1 And args'
  where
    args' = filter (/= TT) args

-- | Wrapper for Or, defined as FF for empty conjuncts list
mkOr :: [CoqTerm] -> CoqTerm
mkOr args = if null args' then FF else foldl1 Or args'
  where
    args' = filter (/= FF) args

-- | Wrapper for App, defined as its first argument for empty argument list
mkApp :: CoqTerm -> [CoqTerm] -> CoqTerm
mkApp f [] = f
mkApp f ts = App f ts

-- | Wrapper for Is_true with some simplifications
mkIsTrue :: CoqTerm -> CoqTerm
mkIsTrue tm = case tm of
  Var "true" -> TT
  Cr "true" -> TT
  Bop zrel r1 r2 | zrel `elem` [Ltb, Leqb, Geqb, Gtb] -> mkZrel zrel r1 r2 btrue
  Neg (Neg b) -> mkIsTrue b
  Neg (Bop zrel r1 r2) | zrel `elem` [Ltb, Leqb, Geqb, Gtb] -> mkZrel zrel r1 r2 bfalse
  App (Def neg) [Bop zrel r1 r2] | neg == negb && zrel `elem` [Ltb, Leqb, Geqb, Gtb] -> mkZrel zrel r1 r2 bfalse
  _ -> {- traceFuncRet ["mkIsTrue", show r] $ -} IsTrue tm
  where
    mkZrel zrel r1 r2 res = App zrel_rel [r1, r2, res]
      where
        zrel_rel = Def $ case zrel of
          Ltb -> "ltbZ_rel"
          Leqb -> "lebZ_rel"
          Geqb -> "gebZ_rel"
          Gtb -> "gtbZ_rel"

-- | Create a destruction pattern [x x_p] for the variable x
mkVarDestrPat :: Id -> CoqDestrPat
mkVarDestrPat x = ConjDestrPat [SingleIdPat x, SingleIdPat $ subsetWitnessNm x]

-- | mkVarDestruct(x) = destruct x as [x x_p].
mkVarDestruct :: Id -> CoqTactic
mkVarDestruct x = DestructSubsetTerm (Var x) (mkVarDestrPat x)

-- * Normalization of arrow types

freshenArgs :: (AppSuable a CoqTerm) => [Id] -> Bool -> ([(Id, RocqType)], a) -> ([(Id, RocqType)], a)
freshenArgs _ False funcTp = funcTp
freshenArgs usedNames True (args, ret) =
  if args' == args
    then (args, ret {- traceFuncRet ["freshenArgs", show usedNames, show args, show ret] -})
    else
      (args', ret_)
  where
    args_ = map (flip mkFresh usedNames . fst) args
    args' = zipWith (\(x, xT) x' -> (x', sub x (Var x') xT)) args args_
    substs = zip (map fst args) (map Var args_)
    repl = foldl (.) id $ map (\(x, tm) -> if tm == Var x then id else replaceSubterm (TermPat (Var x), True) tm) substs
    ret_ = repl ret

-- | match on the given 'RocqType' and return the domain 'Arg's and the result 'RocqType,
--     in case of simple function types (with unnamed domain arguments), create a name that is fresh w.r.t. the given list of names
-- |
matchFunctionTypeFresh :: [Id] -> Bool -> RocqType -> ([(Id, RocqType)], RocqType)
matchFunctionTypeFresh usedNames makeFresh tp = case tp of
  Arrow dom codom -> ((domArgNm, dom) : args, ret)
    where
      domArgNm = freshVar usedNames
      (args, ret) = matchFunctionTypeFresh (domArgNm : usedNames) makeFresh codom
  FAType arg codom -> (args_ ++ argTps, ret)
    where
      (args_, codom_) = freshenArgs usedNames makeFresh ([arg], codom)
      (argTps, ret) = matchFunctionTypeFresh (fst arg : usedNames) makeFresh codom_
  Prop (Forall args' ret') -> (args_ ++ args, ret)
    where
      (args_, ret_) = freshenArgs usedNames makeFresh (args', ret')
      (args, ret) = matchFunctionTypeFresh (usedNames ++ map fst args_) makeFresh (Prop ret_)
  -- Non-function types
  (Prop {}; Builtin {}; Sort {}; Subset {}; TC {}; UPack {}; Pack {}; Hole) -> ([], tp)

-- | match on the given 'CoqType' and return the domain 'Arg's and the result 'CoqType',
--     in case of simple function types (with unnamed domain arguments), create a name that is fresh w.r.t. the given list of names
-- |
matchFunctionType :: [Id] -> RocqType -> ([(Id, RocqType)], RocqType)
matchFunctionType usedNames = matchFunctionTypeFresh usedNames False

-- | like 'matchFunctionType', but additionally also matches implications in the type
matchImplFunctionType :: [Id] -> RocqType -> ([(Id, RocqType)], RocqType)
matchImplFunctionType usedNames tp = case tp of
  Prop (ante `Impl` conseq) -> (anteArg : args, ret)
    where
      h = "h_" ++ hashName conseq
      anteArg = (h, Prop ante)
      (args, ret) = matchImplFunctionType (usedNames ++ [h]) (Prop conseq)
  _ -> case matchFunctionType usedNames tp of
    ([], _) -> ([], tp)
    (args, ret) -> (args ++ args', ret')
      where
        (args', ret') = matchImplFunctionType (usedNames ++ map fst args) ret

-- | like 'matchImplFunctionType', but only matches implications
matchImplProp :: CoqTerm -> ([CoqTerm], CoqTerm)
matchImplProp (Impl ante conseq) = (ante : antes, res)
  where
    (antes, res) = matchImplProp conseq
matchImplProp other = ([], other)

-- | Create the function type with given domain 'Arg's and return 'CoqType'.
-- This is the inverse of function 'matchFunctionType'
mkFuncType :: [(Id, RocqType)] -> RocqType -> RocqType
mkFuncType args (Prop claim) = Prop (mkForall args claim)
mkFuncType args ret = mkForallT args ret

-- | Return the names of the arguments of a type (outside of Prop)
typeArgs :: RocqType -> [Id]
typeArgs (Builtin {}; Sort {}; Subset {}; Prop {}; TC {}; UPack {}; Pack {}; Hole) = []
typeArgs (Arrow _ ret) = typeArgs ret
typeArgs (FAType (n, _) ret) = n : typeArgs ret

-- | Given an arrow (potentially 0-ary), return the name of the type constructor
-- in the return type
baseRetTp :: RocqType -> Id
baseRetTp (Builtin {}; Sort {}; Prop {}; UPack {}; Pack {}; Hole) =
  error "Expected arrow or subset type in baseRetTp."
baseRetTp (TC n _) = n
baseRetTp (Subset _ (TC n _) _) = n
baseRetTp (Subset {}) = error "Refinement of non-inductive datatype found in baseRetTp."
baseRetTp (Arrow _ tp) = baseRetTp tp
baseRetTp (FAType _ tp) = baseRetTp tp

argListCorT :: ArgListT -> UArgListT -> RocqType
argListCorT argList uargList = Prop $ App (Def "projectsArgListT") [mkArgListT argList, mkUArgListT uargList]

argListCorPrf :: ArgListT -> UArgListT -> CoqTerm
argListCorPrf argTps uargTps = PrfTerm (argListCorT argTps uargTps) (ByTac . Custom . unwords $ ["mkProjectsArgListTG", showP argTps, showP uargTps])

mkLam :: [(Id, RocqType)] -> CoqTerm -> CoqTerm
mkLam [] tm = tm
mkLam ((x, xTp) : xTs) tm = Lambda x xTp $ mkLam xTs tm

ltacTerm :: CoqTactic -> CoqTerm
ltacTerm tac = PrfTerm Hole (ByTac tac)

packGetF :: CoqTerm -> CoqTerm
packGetF pack = App (Def getPackFName) [pack]

packGetRel :: CoqTerm -> CoqTerm
packGetRel pack = App (Def getPackRelName) [pack]

packGetCor :: CoqTerm -> CoqTerm
packGetCor pack = App (Def getPackCorName) [pack]

packGetFunct :: CoqTerm -> CoqTerm
packGetFunct pack = App (Def getPackFunctName) [pack]

upackGetRel :: CoqTerm -> CoqTerm
upackGetRel upack = App (Def getUPackRelName) [upack]

upackGetFunct :: CoqTerm -> CoqTerm
upackGetFunct upack = App (Def getUPackFunctName) [upack]
