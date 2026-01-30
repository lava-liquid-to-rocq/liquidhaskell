{-@ LIQUID "--lava" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}

module Benchmark.PLE.MonadMaybe where

{- HLInt ignore -}
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (Just, Maybe, Nothing)

-- | Monad Laws :
-- | Left identity:   retrn a >>= f  ≡ f a
-- | Right identity:   m >>= retrn    ≡ m

{-@ data Maybe where
        Nothing :: Maybe
        Just :: Int -> Maybe @-}
data Maybe where
  Nothing :: Maybe
  Just :: Int -> Maybe
  deriving (Eq)

{-@ reflect retrn @-}
{-@ retrn :: Int -> Maybe @-}
retrn :: Int -> Maybe
retrn x = Just x

{-@ reflect bind @-}
{-@ bind :: Maybe -> (Int -> Maybe) -> Maybe @-}
bind :: Maybe -> (Int -> Maybe) -> Maybe
bind Nothing _ = Nothing
bind (Just m) f = f m

{-bind m f
  | is_Just m  = f (from_Just m)
  | otherwise  = Nothing-}

-- | Left Identity

{-@ left_identity :: x:Int -> f:(Int -> Maybe) -> {v:Proof | bind (retrn x) f == f x } @-}
left_identity :: Int -> (Int -> Maybe) -> Proof
left_identity x f =
  trivial

-- | Right Identity

{-@ right_identity :: x:Maybe -> {v:Proof | bind x retrn == x } @-}
right_identity :: Maybe -> Proof
right_identity Nothing =
  trivial
right_identity (Just x) =
  trivial

{-{-@ reflect is_Just @-}
{-@ is_Just:: Maybe -> Bool @-}
is_Just :: Maybe -> Bool
is_Just (Just _) = True
is_Just _        = False

{-@ from_Just :: xs:{Maybe | is_Just xs } -> Int @-}
from_Just :: Maybe -> Int
from_Just (Just x) = x-}

