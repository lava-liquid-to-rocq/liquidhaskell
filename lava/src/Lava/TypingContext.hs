{-# LANGUAGE LambdaCase #-}

-- | ILH typing contexts
module Lava.TypingContext
  ( TypingCtx,
    Image (..),
    empty,
    initial,
    notMember,
    Lava.TypingContext.map,
    insertRefType,
    lookupRefType,
    insertArrType,
    insertRelType,
    insertHOArgs,
    lookupArrType,
    insertTC,
    lookupTC,
    lookupDC,
    lookupDef,
    lookupRel,
    insertDecls,
    lookupDecls,
    toList,
    replace,
    showCtx,
  )
where

-- import qualified Data.Map.Strict as Map

import Control.Monad (foldM)
import Data.Bifunctor (second)
import Debug.Trace (trace)
import Lava.CoqUtil (relDefName)
import Lava.InternalLH as ILH
import Lava.PaperUtils
import Lava.Util (Id, intercalate)

data Image
  = ΓVar ArrType
  | ΓFHOVar RefType
  | ΓDef ArrType
  | ΓRel [LHType] LHType
  | ΓTC [(Id, ArrType)]
  | ΓMod [LHDecl]

type TypingCtx = [(Id, Image)]

instance Show Image where
  show (ΓVar w) = "local " ++ show w
  show (ΓFHOVar w) = "hoArg " ++ show w
  show (ΓDef w) = show w
  show (ΓRel argTps ret) = intercalate " -> " $ Prelude.map show $ argTps ++ [ret]
  show (ΓTC cs) = "<" ++ intercalate ", " (Prelude.map (\(c, w) -> show c ++ ": " ++ show w) cs) ++ ">"
  show (ΓMod decls) = intercalate "\n" (Prelude.map show decls)

showCtx :: TypingCtx -> String
showCtx γ = "[" ++ intercalate "\n" (Prelude.map show $ reverse γ) ++ "]"

empty = []

initial =
  [ ( boolTpName,
      ΓTC
        [ (tt, ArrType [] $ RefType "VV" boolTp ttTm),
          (ff, ArrType [] $ RefType "VV" boolTp ttTm)
        ]
    ),
    (unitTpName, ΓTC [(unit, ArrType [] $ RefType "VV" unitTp ttTm)])
  ]
  where
    Var tt = ttTm
    Var ff = ffTm
    Var unit = unitTm

toList :: TypingCtx -> [(Id, Image)]
toList = reverse

notMember :: Id -> TypingCtx -> Bool
notMember x γ = x `notElem` Prelude.map fst γ

map :: (Image -> Image) -> TypingCtx -> TypingCtx
map f = Prelude.map (second f)

{-
isFresh :: Id -> TypingCtx -> Bool
isFresh x γ = x `elem` Prelude.map fst γ
-}

{- insert :: (Id, Image) -> TypingCtx -> Either TransError TypingCtx
insert (x, img) γ =
  if not $ isFresh x γ
    then return $ (x, img) : γ
    else
      Left . WfErr $
        "The variable " ++ x ++ " is already in the context:\n" ++ showCtx γ -}

insert :: (Id, Image) -> TypingCtx -> Either TransError TypingCtx
insert (x, img) γ = return $ (x, img) : remove x γ

insertRefType :: (Id, RefType) -> TypingCtx -> Either TransError TypingCtx
insertRefType (x, tp) = insert (x, ΓVar $ ArrType [] tp)

-- need m b
-- have (a -> b -> m b), [a] and b

insertHOArgs :: ArrType -> TypingCtx -> Either TransError TypingCtx
insertHOArgs (ArrType argTps _) γ = foldM (flip insert) γ hoArgTps
  where
    hoArgTps :: [(Id, Image)]
    hoArgTps = concatMap (\case (x, rt@(RefType f Pi {} rf)) -> [(x, ΓFHOVar rt)]; _ -> []) argTps

-- TODO: maybe add the possibility of a data constructor like for RefType
insertArrType :: (Id, ArrType) -> TypingCtx -> Either TransError TypingCtx
insertArrType (x, arr) = insert (x, ΓDef arr)

insertRelType :: (Id, ArrType) -> TypingCtx -> Either TransError TypingCtx
insertRelType (f, ArrType argTps ret) = insert (relDefName f, ΓRel (Prelude.map (argTp . snd) argTps) (argTp ret))

insertTC :: (Id, [(Id, ArrType)]) -> TypingCtx -> Either TransError TypingCtx
insertTC (x, alts) = insert (x, ΓTC alts)

insertDecls :: (Id, [LHDecl]) -> TypingCtx -> Either TransError TypingCtx
insertDecls (x, decls) = insert (x, ΓMod decls)

lookupRefType :: Id -> TypingCtx -> Maybe RefType
lookupRefType x γ =
  case lookup x γ of
    Just (ΓVar (ArrType [] tp)) -> Just tp
    Just (ΓDef (ArrType [] tp)) -> Just tp
    Just (ΓVar tp) -> trace ("Found ArrType where RefType was expected for " ++ x) $ Just (ILH.arrToPi tp)
    Just (ΓDef tp) -> trace ("Found ArrType where RefType was expected for " ++ x) $ Just (ILH.arrToPi tp)
    _ -> case lookupDC x γ of
      Just (ArrType [] tp) -> Just tp
      _ -> Nothing

lookupArrType :: Id -> TypingCtx -> Maybe ArrType
lookupArrType x γ =
  case lookup x γ of
    Just (ΓDef arr) -> Just arr
    Just (ΓVar arr) -> Just arr
    _ -> Nothing

lookupTC :: Id -> TypingCtx -> Maybe [(Id, ArrType)]
lookupTC x γ =
  case lookup x γ of
    Just (ΓTC tpTC) -> Just tpTC
    _ -> Nothing

lookupDef :: Id -> TypingCtx -> Maybe ArrType
lookupDef x γ =
  case lookup x γ of
    Just (ΓDef w) -> Just w
    _ -> Nothing

lookupRel :: Id -> TypingCtx -> Maybe LHType
lookupRel x γ =
  case lookup x γ of
    Just (ΓRel _ ret) -> Just ret
    _ -> Nothing

lookupDC :: Id -> TypingCtx -> Maybe ArrType
lookupDC x γ =
  case foldr (findTypes . snd) [] γ of
    [arr] -> Just arr -- Data constructor identifiers must be unique across type constructors
    _ -> Nothing
  where
    findTypes :: Image -> [ArrType] -> [ArrType]
    findTypes (ΓTC alts) acc =
      case lookup x alts of
        Just arr -> arr : acc
        Nothing -> acc
    findTypes _ acc = acc

lookupDecls :: Id -> TypingCtx -> Maybe [LHDecl]
lookupDecls x γ =
  case lookup x γ of
    Just (ΓMod decls) -> Just decls
    _ -> Nothing

remove :: Id -> TypingCtx -> TypingCtx
remove x = filter ((/=) x . fst)

replace :: Id -> [(Id, RefType)] -> TypingCtx -> Either TransError TypingCtx
replace x binds γ = foldM (flip insertRefType) (remove x γ) binds
