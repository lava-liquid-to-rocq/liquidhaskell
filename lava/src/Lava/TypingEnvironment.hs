{-# LANGUAGE OverloadedStrings #-}

-- | λr typing environements
module Lava.TypingEnvironment where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)
import Data.Set (fromList)
import Lava.Calculus
import Lava.Names (Id, freshVar)
import Text.PrettyPrint.HughesPJClass

data TypeError
  = WfErr Doc
  | CheckingErr Doc
  | SynErr Doc
  | SubstErr Doc
  | SubtypingErr Doc
  | LookupErr Doc
  | SmpTpErr Doc

mapTypeErrorDoc :: (Doc -> Doc) -> TypeError -> TypeError
mapTypeErrorDoc f (WfErr err) = WfErr (f err)
mapTypeErrorDoc f (CheckingErr err) = CheckingErr (f err)
mapTypeErrorDoc f (SynErr err) = SynErr (f err)
mapTypeErrorDoc f (SubstErr err) = SubstErr (f err)
mapTypeErrorDoc f (SubtypingErr err) = SubtypingErr (f err)
mapTypeErrorDoc f (LookupErr err) = LookupErr (f err)
mapTypeErrorDoc f (SmpTpErr err) = SmpTpErr (f err)

annotateErr :: Id -> TypeError -> TypeError
annotateErr i =
  mapTypeErrorDoc (\err -> parens ("In" <+> text i) <+> err)

instance Pretty TypeError where
  pPrint te = case te of
    WfErr err -> aux "Well-formedness" err
    CheckingErr err -> aux "Type checking" err
    SynErr err -> aux "Type synthesis" err
    SubtypingErr err -> aux "Subtyping" err
    SubstErr err -> aux "Substitution" err
    LookupErr err -> aux "Environment lookup" err
    SmpTpErr err -> aux "Simple type checking" err
    where
      aux kind err = "——" <+> kind <+> "failed with error:" <+> err <+> "——"

-- For recursive variables, the inductive variable and state are not used
data Image
  = ΓVar Localization RefType
  | ΓTyVar
  | ΓTC [Id] [(Id, RefType)]

type TypEnv = Map Id Image

empty :: TypEnv
empty = Map.empty

initial :: TypEnv
initial =
  Map.fromList
    [ ( boolTpName,
        ΓTC
          []
          [ (ttTmName, defaultRef boolTp),
            (ffTmName, defaultRef boolTp)
          ]
      ),
      (unitTpName, ΓTC [] [(unitTmName, defaultRef unitTp)]),
      ( listTpName,
        ΓTC
          ["α"]
          [ (nilTmName, listαRef),
            (consTmName, ArrType "VV" (defaultRef (TyVar "α")) listαRef)
          ]
      )
    ]
  where
    listαRef = defaultRef (listTp . defaultRef $ TyVar "α")

insertVar :: (Id, Localization, RefType) -> TypEnv -> TypEnv
insertVar (x, loc, tp) = Map.insert x (ΓVar loc tp)

insertLocalVar :: (Id, RefType) -> TypEnv -> TypEnv
insertLocalVar (x, tp) = insertVar (x, Local, tp)

insertLocalVars :: [(Id, RefType)] -> TypEnv -> TypEnv
-- We do not use union because we want to be right-biased
insertLocalVars xs γ = foldl (flip insertLocalVar) γ xs

insertGlobalVar :: (Id, RefType) -> TypEnv -> TypEnv
insertGlobalVar (x, tp) = insertVar (x, Global, tp)

-- | Inserts recursive variable in the context. We use an empty String
-- and an empty list as placeholders for the induction variable and branch pattern
insertRecVar :: (Id, RefType) -> TypEnv -> TypEnv
insertRecVar (x, tp) = insertVar (x, Recursive "" [], tp)

-- | Changes the localization Y of a variable to G
changeRecToGlobal :: Id -> TypEnv -> Either TypeError TypEnv
changeRecToGlobal f γ =
  case Map.lookup f γ of
    Just (ΓVar (Recursive {}) tp) -> return $ Map.adjust (const $ ΓVar Global tp) f γ
    _ -> Left . LookupErr $ "Variable" <+> text f <+> "is not recursive in the environment"

adjust :: (Image -> Image) -> Id -> TypEnv -> TypEnv
adjust = Map.adjust

insertTC :: (Id, [Id], [(Id, RefType)]) -> TypEnv -> TypEnv
insertTC (x, αs, alts) = Map.insert x (ΓTC αs alts)

insertDCinTC :: (Id, RefType) -> Id -> TypEnv -> Either TypeError TypEnv
insertDCinTC constr tc γ = do
  (αs, γconstrs) <- lookupTC tc γ
  return $ insertTC (tc, αs, γconstrs ++ [constr]) γ

insertTyVar :: Id -> TypEnv -> TypEnv
insertTyVar α = Map.insert α ΓTyVar

lookupVar :: Id -> TypEnv -> Either TypeError (Localization, RefType)
lookupVar x γ =
  case Map.lookup x γ of
    Just (ΓVar loc tp) -> return (loc, tp)
    _ -> Left . LookupErr $ "Variable" <+> text x <+> "not bound in context"

lookupTC :: Id -> TypEnv -> Either TypeError ([Id], [(Id, RefType)])
lookupTC x γ =
  case Map.lookup x γ of
    Just (ΓTC αs tpTC) -> return (αs, tpTC)
    _ -> Left . LookupErr $ "Type" <+> text x <+> "not bound in context"

lookupDC :: Id -> TypEnv -> Either TypeError RefType
lookupDC x γ =
  case Map.foldr findTypes [] γ of
    [tp] -> return tp -- Data constructor identifiers must be unique across type constructors
    _ : _ -> error . render $ "Constructor" <+> text x <+> "bound several times in context."
    _ -> Left . LookupErr $ "Constructor" <+> text x <+> "not bound in context"
  where
    findTypes :: Image -> [RefType] -> [RefType]
    findTypes (ΓTC _ alts) acc =
      case lookup x alts of
        Just arr -> arr : acc
        Nothing -> acc
    findTypes _ acc = acc

lookupTyVar :: Id -> TypEnv -> Bool
lookupTyVar α γ = isJust (Map.lookup α γ)

mkFresh :: Id -> TypEnv -> Id
mkFresh x γ = freshVar x (fromList $ Map.keys γ)

member :: Id -> TypEnv -> Bool
member = Map.member

notMember :: Id -> TypEnv -> Bool
notMember = Map.notMember

-- * Types of primitives

-- | Singleton type of a literal
litType :: Builtin -> Reft -> RefType
litType tp l = RefType "VV" (Builtin tp) (Bop Eq (Var "VV" 0 Local) l)

-- | Type of negation, with singleton return type
negType :: RefType
negType = ArrType "x" (RefType "x" boolTp ttTm) (RefType "VV" boolTp (Bop Eq (Var "VV" 0 Local) (Neg . Proj $ Var "x" 0 Local)))

-- | Types of binary operators, with singleton return type
bopTypes :: [(Bop, RefType)]
bopTypes =
  [ (Plus, mkBopType Plus (Builtin Integer) (Builtin Integer) ttTm (Builtin Integer)),
    (Minus, mkBopType Minus (Builtin Integer) (Builtin Integer) ttTm (Builtin Integer)),
    (Times, mkBopType Times (Builtin Integer) (Builtin Integer) ttTm (Builtin Integer)),
    (Div, mkBopType Div (Builtin Integer) (Builtin Integer) (Bop Neq (Var "x_2" 0 Local) (IntLit 0)) (Builtin Integer)),
    (Mod, mkBopType Mod (Builtin Integer) (Builtin Integer) (Bop Neq (Var "x_2" 0 Local) (IntLit 0)) (Builtin Integer)),
    (Leq, mkBopType Leq (Builtin Integer) (Builtin Integer) ttTm boolTp),
    (Geq, mkBopType Geq (Builtin Integer) (Builtin Integer) ttTm boolTp),
    (Lt, mkBopType Lt (Builtin Integer) (Builtin Integer) ttTm boolTp),
    (Gt, mkBopType Gt (Builtin Integer) (Builtin Integer) ttTm boolTp),
    (And, mkBopType And boolTp boolTp ttTm boolTp),
    (Or, mkBopType Or boolTp boolTp ttTm boolTp),
    (Impl, mkBopType Impl boolTp boolTp ttTm boolTp),
    (Iff, mkBopType Iff boolTp boolTp ttTm boolTp)
  ]

-- | Type of the equality and inequality for any base type
eqneqTypes :: BaseType -> [(Bop, RefType)]
eqneqTypes b = [(Eq, mkBopType Eq b b ttTm boolTp), (Neq, mkBopType Neq b b ttTm boolTp)]

-- | Wrapper for the arrow type for a binary operator, with specialization of the output refinement
mkBopType :: Bop -> BaseType -> BaseType -> Reft -> BaseType -> RefType
mkBopType bop a1 a2 r2 a3 =
  ArrType "x_1" (RefType "x_1" a1 ttTm) $
    ArrType "x_2" (RefType "x_2" a2 r2) $
      RefType "VV" a3 (Bop Eq (Var "VV" 0 Local) (Bop bop (Proj $ Var "x_1" 0 Local) (Proj $ Var "x_2" 0 Local)))
