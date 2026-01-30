{-@ LIQUID "--lava" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}

module Benchmark.PLE.MonoidList where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (mappend, mempty)

-- | Monoid
-- | mempty-left ∀ x . mappend mempty  x ≡ x
-- | mempty-right ∀ x . mappend x  mempty ≡ x
-- | mappend-assoc ∀ x y z . mappend (mappend x  y) z ≡ mappend x (mappend y z)

{-@ data L where
        Emp :: L
        C :: Int -> L -> L @-}
data L where
  Emp :: L
  C :: Int -> L -> L
  deriving (Eq)

{-@ axiomatize mappend @-}
{-@ mappend :: L -> L -> L @-}
mappend :: L -> L -> L
mappend Emp ys = ys
mappend (C x xs) ys = C x (mappend xs ys)

{-@ axiomatize mempty @-}
{-@ mempty :: L @-}
mempty :: L
mempty = Emp

mempty_left :: L -> Proof
{-@ mempty_left :: x:L -> { mappend mempty x == x }  @-}
mempty_left xs =
  trivial

mempty_right :: L -> Proof
{-@ mempty_right :: x:L -> { mappend x mempty == x}  @-}
mempty_right Emp =
  trivial
mempty_right (C x xs) =
  mempty_right xs

{-@ mappend_assoc :: xs:L -> ys:L -> zs:L
               -> {mappend (mappend xs ys) zs == mappend xs (mappend ys zs) } @-}
mappend_assoc :: L -> L -> L -> Proof
mappend_assoc Emp ys zs =
  trivial
mappend_assoc (C x xs) ys zs =
  mappend_assoc xs ys zs

