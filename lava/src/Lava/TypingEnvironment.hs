-- | ILH typing contexts
module Lava.TypingEnvironment where

-- import qualified Data.Map.Strict as Map

import Control.Monad (foldM)
import Data.Bifunctor (second)
import Debug.Trace (trace)
import Lava.Calculus
import Lava.CoqUtil (relDefName)
import Lava.PaperUtils

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

notMember :: Id -> TypEnv -> Bool
notMember x γ = x `notElem` Prelude.map fst γ

map :: (Image -> Image) -> TypEnv -> TypEnv
map f = Prelude.map (second f)

{-
isFresh :: Id -> TypEnv -> Bool
isFresh x γ = x `elem` Prelude.map fst γ
-}

{- insert :: (Id, Image) -> TypEnv -> Either TransError TypEnv
insert (x, img) γ =
  if not $ isFresh x γ
    then return $ (x, img) : γ
    else
      Left . WfErr $
        "The variable " ++ x ++ " is already in the context:\n" ++ showCtx γ -}

insert :: (Id, Image) -> TypEnv -> Either TransError TypEnv
insert (x, img) γ = return $ (x, img) : remove x γ

insertVar :: (Id, Localization, RefType) -> TypEnv -> Either TransError TypEnv
insertVar (x, loc, tp) = insert (x, ΓVar loc tp)

{- insertHOArgs :: ArrType -> TypEnv -> Either TransError TypEnv
insertHOArgs (ArrType argTps _) γ = foldM (flip insert) γ hoArgTps
  where
    hoArgTps :: [(Id, Image)]
    hoArgTps = concatMap (\case (x, rt@(RefType f Pi {} rf)) -> [(x, ΓFHOVar rt)]; _ -> []) argTps -}

insertTC :: (Id, [(Id, RefType)]) -> TypEnv -> Either TransError TypEnv
insertTC (x, alts) = insert (x, ΓTC alts)

lookupVar :: Id -> TypEnv -> Maybe (Localization, RefType)
lookupVar x γ =
  case lookup x γ of
    Just (ΓVar loc tp) -> Just (loc, tp)
    _ -> Nothing

lookupTC :: Id -> TypEnv -> Maybe [(Id, RefType)]
lookupTC x γ =
  case lookup x γ of
    Just (ΓTC tpTC) -> Just tpTC
    _ -> Nothing

lookupDC :: Id -> TypEnv -> Maybe RefType
lookupDC x γ =
  case foldr (findTypes . snd) [] γ of
    [tp] -> Just tp -- Data constructor identifiers must be unique across type constructors
    _ -> Nothing
  where
    findTypes :: Image -> [RefType] -> [RefType]
    findTypes (ΓTC alts) acc =
      case lookup x alts of
        Just arr -> arr : acc
        Nothing -> acc
    findTypes _ acc = acc

remove :: Id -> TypEnv -> TypEnv
remove x = filter ((/=) x . fst)

replace :: Id -> [(Id, Image)] -> TypEnv -> Either TransError TypEnv
replace x binds γ = foldM (flip insert) (remove x γ) binds
