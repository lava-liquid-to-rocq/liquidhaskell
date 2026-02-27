-- | ILH typing contexts
module Lava.TypingEnvironment where

-- import qualified Data.Map.Strict as Map

import Control.Monad (foldM)
import Data.Bifunctor (second)
import Debug.Trace (trace)
import Lava.Calculus
import Lava.CoqUtil (relDefName)
import Lava.PaperUtils hiding (TransError (..))
import qualified Lava.Util as Util (mkFresh)

data TypeError
  = WfErr String
  | CheckingErr String
  | SynErr String
  | SubstErr String
  | SubtypingErr String
  | LookupErr String
  | SmpTpErr String

instance Show TypeError where
  show te = case te of
    WfErr err -> aux "Well-formedness" err
    CheckingErr err -> aux "Type checking" err
    SynErr err -> aux "Type synthesis" err
    SubtypingErr err -> aux "Subtyping" err
    SubstErr err -> aux "Substitution" err
    LookupErr err -> aux "Environment lookup" err
    SmpTpErr err -> aux "Simple type checking" err
    where
      aux kind err = "—— " ++ kind ++ " failed with error: " ++ err ++ " ——"

-- import Lava.Util (Id, intercalate)

data Image
  = ΓVar Localization RefType
  | ΓTC [(Id, RefType)]

type TypEnv = [(Id, Image)]

{- instance Show Image where
  show (ΓVar w) = "local " ++ show w
  show (ΓFHOVar w) = "hoArg " ++ show w
  show (ΓDef w) = show w
  show (ΓRel argTps ret) = intercalate " -> " $ Prelude.map show $ argTps ++ [ret]
  show (ΓTC cs) = "<" ++ intercalate ", " (Prelude.map (\(c, w) -> show c ++ ": " ++ show w) cs) ++ ">"
  show (ΓMod decls) = intercalate "\n" (Prelude.map show decls) -}

{- showCtx :: TypEnv -> String
showCtx γ = "[" ++ intercalate "\n" (Prelude.map show $ reverse γ) ++ "]" -}

empty :: TypEnv
empty = []

initial :: TypEnv
initial =
  [ ( boolTpName,
      ΓTC
        [ (ttTmName, defaultRef boolTp),
          (ffTmName, defaultRef boolTp)
        ]
    ),
    (unitTpName, ΓTC [(unitTmName, defaultRef unitTp)])
  ]

{- toList :: TypEnv -> [(Id, Image)]
toList = reverse -}

member :: Id -> TypEnv -> Bool
member x γ = x `elem` Prelude.map fst γ

{- notMember :: Id -> TypEnv -> Bool
notMember x γ = x `notElem` Prelude.map fst γ -}

{- map :: (Image -> Image) -> TypEnv -> TypEnv
map f = Prelude.map (second f) -}

{-
isFresh :: Id -> TypEnv -> Bool
isFresh x γ = x `elem` Prelude.map fst γ
-}

{- insert :: (Id, Image) -> TypEnv -> Either TypeError TypEnv
insert (x, img) γ =
  if not $ isFresh x γ
    then return $ (x, img) : γ
    else
      Left . WfErr $
        "The variable " ++ x ++ " is already in the context:\n" ++ showCtx γ -}

insert :: TypEnv -> (Id, Image) -> Either TypeError TypEnv
insert γ (x, img) = return $ (x, img) : remove x γ

insertVar :: TypEnv -> (Id, Localization, RefType) -> Either TypeError TypEnv
insertVar γ (x, loc, tp) = insert γ (x, ΓVar loc tp)

insertLocalVar :: TypEnv -> (Id, RefType) -> Either TypeError TypEnv
insertLocalVar γ (x, tp) = insertVar γ (x, Local, tp)

insertGlobalVar :: TypEnv -> (Id, RefType) -> Either TypeError TypEnv
insertGlobalVar γ (x, tp) = insertVar γ (x, Global, tp)

{- insertHOArgs :: ArrType -> TypEnv -> Either TypeError TypEnv
insertHOArgs (ArrType argTps _) γ = foldM (flip insert) γ hoArgTps
  where
    hoArgTps :: [(Id, Image)]
    hoArgTps = concatMap (\case (x, rt@(RefType f Pi {} rf)) -> [(x, ΓFHOVar rt)]; _ -> []) argTps -}

insertTC :: TypEnv -> (Id, [(Id, RefType)]) -> Either TypeError TypEnv
insertTC γ (x, alts) = insert γ (x, ΓTC alts)

lookupVar :: Id -> TypEnv -> Either TypeError (Localization, RefType)
lookupVar x γ =
  case lookup x γ of
    Just (ΓVar loc tp) -> return (loc, tp)
    _ -> Left . LookupErr $ "Variable " ++ show x ++ " not bound in context"

lookupTC :: Id -> TypEnv -> Either TypeError [(Id, RefType)]
lookupTC x γ =
  case lookup x γ of
    Just (ΓTC tpTC) -> return tpTC
    _ -> Left . LookupErr $ "Type " ++ show x ++ " not bound in context"

lookupDC :: Id -> TypEnv -> Either TypeError RefType
lookupDC x γ =
  case foldr (findTypes . snd) [] γ of
    [tp] -> return tp -- Data constructor identifiers must be unique across type constructors
    _ -> Left . LookupErr $ "Constructor " ++ show x ++ " not bound in context"
  where
    findTypes :: Image -> [RefType] -> [RefType]
    findTypes (ΓTC alts) acc =
      case lookup x alts of
        Just arr -> arr : acc
        Nothing -> acc
    findTypes _ acc = acc

remove :: Id -> TypEnv -> TypEnv
remove x = filter ((/=) x . fst)

replace :: Id -> [(Id, Image)] -> TypEnv -> Either TypeError TypEnv
replace x binds γ = foldM insert (remove x γ) binds

mkFresh :: TypEnv -> Id -> Id
mkFresh γ x = Util.mkFresh x (map fst γ)
