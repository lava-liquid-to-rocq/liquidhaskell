{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--lava" @-}

module Benchmark.MonoidMaybe where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (Just, Maybe, Nothing, mappend, mempty)

-- | Monoid
-- | mempty-left ∀ x . mappend mempty  x ≡ x
-- | mempty-right ∀ x . mappend x  mempty ≡ x
-- | mappend-assoc ∀ x y z . mappend (mappend x  y) z ≡ mappend x (mappend y z)

{-@ data Maybe where
        Nothing :: Maybe
        Just :: Int -> Maybe @-}
data Maybe where
  Nothing :: Maybe
  Just :: Int -> Maybe
  deriving (Eq)

{-@ reflect mempty @-}
{-@ mempty :: Maybe @-}
mempty :: Maybe
mempty = Nothing

{-@ reflect mappend @-}
{-@ mappend :: Maybe -> Maybe -> Maybe @-}
mappend :: Maybe -> Maybe -> Maybe
mappend Nothing y =
  y
mappend (Just x) y =
  Just x

{-@ mempty_left :: x:Maybe -> { mappend mempty x == x }  @-}
mempty_left :: Maybe -> Proof
mempty_left _ = trivial

{-@ mempty_right :: x:Maybe -> { mappend x mempty == x }  @-}
mempty_right :: Maybe -> Proof
mempty_right Nothing =
  trivial
mempty_right (Just x) =
  trivial

{-@ mappend_assoc :: xs:Maybe -> ys:Maybe -> zs:Maybe
                  -> {mappend (mappend xs ys) zs == mappend xs (mappend ys zs) } @-}
mappend_assoc :: Maybe -> Maybe -> Maybe -> Proof
mappend_assoc (Just x) y z =
  trivial
mappend_assoc Nothing (Just y) z =
  trivial
mappend_assoc Nothing Nothing z =
  trivial
