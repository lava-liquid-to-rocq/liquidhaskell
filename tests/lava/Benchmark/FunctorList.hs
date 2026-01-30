{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE IncoherentInstances #-}

{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--lava" @-}

module Benchmark.FunctorList where

{- HLInt ignore -}
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (fmap, id)

-- | Functor Laws :
-- | fmap-id fmap id ≡ id
-- | fmap-distrib ∀ g h . fmap (g ◦ h) ≡ fmap g ◦ fmap h

{-@ data L where
        N :: L
        C :: Int -> L -> L @-}
data L where
  N :: L
  C :: Int -> L -> L
  deriving (Eq)

{-@ reflect fmap @-}
{-@ fmap :: (Int -> Int) -> L -> L @-}
fmap :: (Int -> Int) -> L -> L
fmap _ N = N
fmap f (C x xs) = C (f x) (fmap f xs)

{-@ reflect id @-}
{-@ id:: Int -> Int @-}
id :: Int -> Int
id x = x

{-@ reflect idL @-}
{-@ idL:: L -> L @-}
idL :: L -> L
idL x = x

{-@ reflect compose @-}
{-@ compose :: (Int -> Int) -> (Int -> Int) -> Int -> Int @-}
compose :: (Int -> Int) -> (Int -> Int) -> Int -> Int
compose f g x = f (g x)

{-@ reflect composeL @-}
{-@ composeL :: (L -> L) -> (L -> L) -> L -> L @-}
composeL :: (L -> L) -> (L -> L) -> L -> L
composeL f g x = f (g x)

{-@ fmap_id :: xs:L -> { fmap id xs == idL xs } @-}
fmap_id :: L -> Proof
fmap_id N =
  trivial
fmap_id (C x xs) =
  fmap_id (xs)

-- | Distribution

{-@ fmap_distrib :: f:(Int -> Int) -> g:(Int -> Int) -> xs:L
               -> {v:Proof | fmap  (compose f g) xs == (composeL (fmap f) (fmap g)) (xs) } @-}
fmap_distrib :: (Int -> Int) -> (Int -> Int) -> L -> Proof
fmap_distrib f g N =
  trivial
fmap_distrib f g (C x xs) =
  fmap_distrib f g xs
