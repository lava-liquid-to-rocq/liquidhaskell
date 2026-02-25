{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

-- | This module contains the functions for the translation of declarations
module Lava.Declaration where

import Data.Bifunctor (bimap, first, second)
import Lava.Calculus as LH
import Lava.Coq as Coq
import Lava.CoqUtil -- (exLemName, funcHoodLemName, mkCoqTheorem, packInstanceName, relDefLemName, relDefName, relDefThmName, toPack, toUPack)
import Lava.Translation
import Lava.TypingEnvironment as TypEnv hiding (map)
import Lava.Util (freshVar)

-- | Main function for the translation of declarations
trDecl :: LH.Decl -> [Coq.Decl]
trDecl (LH.Data tc alts) = undefined
trDecl (LH.Definition f tpf e False) = [trDefRefDef f (arrs tpf) e]
trDecl (LH.Definition f tpf e True) =
  [ trDefRefDef f (arrs tpf) e, -- f
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
         refUnrefLemma' f,
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
trDefRefDef :: Id -> ([(Id, RefType)], RefType) -> Expr -> Coq.Decl
trDefRefDef f (args, ret) e = Coq.Definition f argsT (trRefType ret) (ProofBody tacs) Transparent
  where
    argsT = map (\(id, arg) -> ((id, trRefType arg), False)) args
    tacs =
      let destructArgs = map (varDestruct . fst) $ onlyFOArgs args
       in -- TODO: maybe use cleanInductions (usedIHs eT) eT
          destructArgs ++ trExprTacs (map (LH.VarPat . fst) args) e

-- | Translation of a definition `f` to the unrefined graph relation `f_rel`
trDefGraphRel :: Id -> RefType -> Expr -> Coq.Decl
trDefGraphRel f tp e =
  CoqInductive (relDefName f) [] (utrRefTypeTop tp) (map (uncurry Coq.Constr . fst) branches)
  where
    branches = undefined

-- * Functions for the construction of the graph relation

-- | Represents one path for a function.
-- The first element contains a map from arguments to their patterns,
-- the second from additional applications to the patterns for their results (“with”),
-- the third is the term of the branch, that is always a refinement
type FunctionPath = ([(Id, Pattern)], [(Reft, Pattern)], Reft)

-- | Creates the function paths of an expression by calling separateBranches:
-- function paths(e; x1...xn) of the paper (definition B.2)
functionPaths :: Expr -> [Id] -> [FunctionPath]
functionPaths e xs = {- map (\(σxs, σp, r) -> (map snd σxs, σp, r)) $ -} separateBranches (zip xs (map VarPat xs)) [] e

-- | Actually create the function paths of an expression: function P from the paper (definition B.3)
separateBranches :: [(Id, Pattern)] -> [(Reft, Pattern)] -> Expr -> [FunctionPath]
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
      _ -> concatMap (\((c, ys), e) -> separateBranches σxs (σp ++ [(r, TCPat c (map VarPat ys))]) e) cleanBranches
  where
    -- Reachable branches only
    cleanBranches = concatMap (\case (_, Nothing) -> []; (pat, Just x) -> [(pat, x)]) branches
    -- Returns the pattern to which r is matched if it is already
    alreadyMatched =
      apps . patternToReft <$> case r of
        LH.Var x _ _ -> case lookup x σxs of Just (VarPat y) -> Nothing; pat -> pat
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

-- | Create a destruction pattern [x x_p] for the variable x
varDestrPat :: Id -> CoqDestrPat
varDestrPat x = Coq.ConjDestrPat [Coq.SingleIdPat x, Coq.SingleIdPat $ subsetWitnessNm x]

-- | varDestruct(x) = destruct x as [x x_p].
varDestruct :: Id -> CoqTactic
varDestruct x = Coq.DestructSubsetTerm (Coq.Var x) (varDestrPat x)

-- | Filter arguments with a non-arrow refinement type (those that usually need to be destructed)
onlyFOArgs :: [(Id, RefType)] -> [(Id, RefType)]
onlyFOArgs args = [(id, tp) | (id, tp) <- args, isFO tp]
  where
    isFO (RefType {}) = True
    isFO (ArrType {}) = False
