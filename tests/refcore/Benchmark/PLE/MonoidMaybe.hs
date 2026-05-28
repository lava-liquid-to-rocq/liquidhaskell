{-@ LIQUID "--lava" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}

module Benchmark.PLE.MonoidMaybe where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (Just, Maybe, Nothing, mappend, mempty)

-- | Monoid
-- | mempty-left ∀ x . mappend mempty  x ≡ x
-- | mempty-right ∀ x . mappend x  mempty ≡ x
-- | mappend-assoc ∀ x y z . mappend (mappend x  y) z ≡ mappend x (mappend y z)

{-@ data MaybeInt where
        Nothing :: MaybeInt
        Just :: Int -> MaybeInt @-}
data MaybeInt where
  Nothing :: MaybeInt
  Just :: Int -> MaybeInt
  deriving (Eq)

{-@ reflect mempty @-}
{-@ mempty :: MaybeInt @-}
mempty :: MaybeInt
mempty = Nothing

{-@ reflect mappend @-}
{-@ mappend :: MaybeInt -> MaybeInt -> MaybeInt @-}
mappend :: MaybeInt -> MaybeInt -> MaybeInt
mappend Nothing y =
  y
mappend (Just x) y =
  Just x

{-@ mempty_left :: x:MaybeInt -> { mappend mempty x == x }  @-}
mempty_left :: MaybeInt -> Proof
mempty_left _ = trivial

{-@ mempty_right :: x:MaybeInt -> { mappend x mempty == x }  @-}
mempty_right :: MaybeInt -> Proof
mempty_right Nothing =
  trivial
mempty_right (Just x) =
  trivial

{-@ mappend_assoc :: xs:MaybeInt -> ys:MaybeInt -> zs:MaybeInt
                  -> {mappend (mappend xs ys) zs == mappend xs (mappend ys zs) } @-}
mappend_assoc :: MaybeInt -> MaybeInt -> MaybeInt -> Proof
mappend_assoc (Just x) y z =
  trivial
mappend_assoc Nothing (Just y) z =
  trivial
mappend_assoc Nothing Nothing z =
  trivial

