{-@ LIQUID "--refcore" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}

module Benchmark.PLE.MonadMaybe where

{- HLInt ignore -}
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (Maybe, Just, Nothing)

-- | Monad Laws :
-- | Left identity:   retrn a >>= f  ≡ f a
-- | Right identity:   m >>= retrn    ≡ m

{-@ data MaybeInt where
        Nothing :: MaybeInt
        Just :: Int -> MaybeInt @-}
data MaybeInt where
  Nothing :: MaybeInt
  Just :: Int -> MaybeInt
  deriving (Eq)

{-@ reflect retrn @-}
{-@ retrn :: Int -> MaybeInt @-}
retrn :: Int -> MaybeInt
retrn x = Just x

{-@ reflect bind @-}
{-@ bind :: MaybeInt -> (Int -> MaybeInt) -> MaybeInt @-}
bind :: MaybeInt -> (Int -> MaybeInt) -> MaybeInt
bind Nothing _ = Nothing
bind (Just m) f = f m

{-bind m f
  | is_Just m  = f (from_Just m)
  | otherwise  = Nothing-}

-- | Left Identity

{-@ left_identity :: x:Int -> f:(Int -> MaybeInt) -> {v:Proof | bind (retrn x) f == f x } @-}
left_identity :: Int -> (Int -> MaybeInt) -> Proof
left_identity x f =
  trivial

-- | Right Identity

{-@ right_identity :: x:MaybeInt -> {v:Proof | bind x retrn == x } @-}
right_identity :: MaybeInt -> Proof
right_identity Nothing =
  trivial
right_identity (Just x) =
  trivial

{-{-@ reflect is_Just @-}
{-@ is_Just:: MaybeInt -> Bool @-}
is_Just :: MaybeInt -> Bool
is_Just (Just _) = True
is_Just _        = False

{-@ from_Just :: xs:{MaybeInt | is_Just xs } -> Int @-}
from_Just :: MaybeInt -> Int
from_Just (Just x) = x-}

