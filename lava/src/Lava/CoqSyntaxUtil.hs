{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE TupleSections #-}

-- | Utility functions manipulating Rocq terms and types
module Lava.CoqSyntaxUtil where

import Text.PrettyPrint.HughesPJClass

import Language.Haskell.Liquid.RefCore.Names

import Lava.Coq

-- * Tactic names for "projections" out of packs

{- ORMOLU_DISABLE -}
getPackFName :: Id;
getPackRelName :: Id
getPackCorName :: Id
getPackFunctName :: Id
getUPackRelName :: Id
getUPackFunctName :: Id
getPackFName = "getPackF"
getPackRelName = "getPackRel"
getPackCorName = "getPackCor"
getPackFunctName = "getPackFunct"
getUPackRelName = "getUPackRel"
getUPackFunctName = "getUPackFunct"
{- ORMOLU_ENABLE -}

-- * Wrappers for Rocq terms

mkCoqLemma :: Id -> [((Id, RocqType), Bool)] -> RocqType -> [Tactic] -> Decl
mkCoqLemma f args ret tacs = Definition f args ret (ProofBody tacs) Opaque

mkCoqTheorem :: Id -> [((Id, RocqType), Bool)] -> CoqTerm -> [Tactic] -> Decl
mkCoqTheorem f args ret = mkCoqLemma f args (Prop ret)

-- | Wrapper for Forall, defined as id for empty argument list
mkForall :: [(Id, RocqType)] -> CoqTerm -> CoqTerm
mkForall args r = if null args then r else Forall args r

-- | Build forall (x)_{x in xs}, cqtm
mkForallXs :: [Id] -> CoqTerm -> CoqTerm
mkForallXs xs cqtm = Forall (map (,Hole) xs) cqtm

-- | Wrapper for Exists, defined as id for empty argument list
mkExists :: [(Id, RocqType)] -> CoqTerm -> CoqTerm
mkExists [] r = r
mkExists ((_, Prop prp@(Bop (Binop Eq PropOp) _ trueOrFalse)) : tl) r | trueOrFalse `elem` [btrue, bfalse] = mkAnd [prp, mkExists tl r]
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
mkAnd args = if null args' then PropLit True else foldl1 (Bop (Binop And PropOp)) args'
  where
    args' = filter (/= PropLit True) args

-- | Wrapper for Or, defined as FF for empty conjuncts list
mkOr :: [CoqTerm] -> CoqTerm
mkOr args = if null args' then PropLit False else foldl1 (Bop (Binop Or PropOp)) args'
  where
    args' = filter (/= PropLit False) args

-- | Wrapper for App, defined as its first argument for empty argument list
mkApp :: CoqTerm -> [CoqTerm] -> CoqTerm
mkApp f [] = f
mkApp f ts = App f ts

-- | Wrapper for Is_true with some simplifications
mkIsTrue :: CoqTerm -> CoqTerm
-- mkIsTrue tm | trace ("mkIsTrue(" ++ show tm ++ ")") False = undefined
mkIsTrue tm = case tm of
  _ | tm == btrue -> PropLit True
  _ | tm == bfalse -> PropLit False
  Neg _ (Neg _ b) -> mkIsTrue b
  Neg _ (Bop (Binop zrel UnrefOp) r1 r2)
    | zrel `elem` [Lt, Leq, Geq, Gt] ->
        mkZrel zrel r1 r2 bfalse
  Neg _ b -> Neg PropOp (mkIsTrue b)
  Bop (Binop zrel UnrefOp) r1 r2
    | zrel `elem` [Lt, Leq, Geq, Gt] ->
        mkZrel zrel r1 r2 btrue
  Bop (Binop bop UnrefOp) r1 r2
    | bop `elem` [Eq, Neq] ->
        Bop (Binop bop PropOp) r1 r2
  Bop (Binop bop UnrefOp) r1 r2
    | bop `elem` [And, Or, Impl, Equiv] ->
        Bop (Binop bop PropOp) (mkIsTrue r1) (mkIsTrue r2)
  _ -> IsTrue tm
  where
    mkZrel zrel r1 r2 res = App zrel_rel [r1, r2, res]
      where
        zrel_rel = Def $ case zrel of
          Lt -> "ltbZ_rel"
          Leq -> "lebZ_rel"
          Geq -> "gebZ_rel"
          Gt -> "gtbZ_rel"

-- | Wrapper for exist, using the proof term I for a trivial refinement
mkExist :: Bool -> RocqType -> CoqTerm -> CoqTerm
mkExist eq (Subset x tp r) tm =
  Exist (Lambda x tp r) tm (if isTrivial r then CoqProofTerm "I" else if eq then ProofHole else ByTac Oracle)
mkExist _ tp _ = error . render $ text "Subset type expected to build exist, found" <+> pPrint tp

-- | Create a destruction pattern [x x_p] for the variable x
mkVarDestrPat :: Id -> CoqDestrPat
mkVarDestrPat x = ConjDestrPat [SingleIdPat x, SingleIdPat $ subsetWitnessNm x]

-- | mkVarDestruct(x) = destruct x as [x x_p].
mkVarDestruct :: Id -> Tactic
mkVarDestruct x = DestructSubsetTerm (Var x) (mkVarDestrPat x)

-- | mkOpaque(x) = Opaque x.
mkOpaque :: Id -> Decl
-- mkOpaque x | trace ("mkOpaque(" ++ x ++ ")") False = undefined
mkOpaque x = ChangeVisibility x Opaque

argListCorT :: ArgListT -> UArgListT -> RocqType
argListCorT argList uargList = Prop $ App (Def "projectsArgListT") [mkArgListT argList, mkUArgListT uargList]

argListCorPrf :: ArgListT -> UArgListT -> CoqTerm
argListCorPrf argTps uargTps =
  PrfTerm
    (argListCorT argTps uargTps)
    (ByTac . Custom . unwords $ ["mkProjectsArgListTG", render . parens $ pPrint argTps, render . parens $ pPrint uargTps])

mkLam :: [(Id, RocqType)] -> CoqTerm -> CoqTerm
mkLam [] tm = tm
mkLam ((x, xTp) : xTs) tm = Lambda x xTp $ mkLam xTs tm

ltacTerm :: Tactic -> CoqTerm
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
