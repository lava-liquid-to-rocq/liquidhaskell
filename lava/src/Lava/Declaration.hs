{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

-- | This module contains the functions for the translation of declarations
module Lava.Declaration where

import Data.Bifunctor (first, second)
import Lava.Calculus as LH
import Lava.Coq as Coq
import Lava.CoqUtil -- (exLemName, funcHoodLemName, mkCoqTheorem, packInstanceName, relDefLemName, relDefName, relDefThmName, toPack, toUPack)
import Lava.Translation
import Lava.TypingEnvironment as TypEnv hiding (map)
import Lava.Util (freshVar)

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
