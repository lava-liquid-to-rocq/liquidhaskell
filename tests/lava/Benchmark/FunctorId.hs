{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE IncoherentInstances #-}

{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--lava" @-}

module Benchmark.FunctorId where

{- HLInt ignore -}
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (fmap, id)

-- | Functor Laws :
-- | fmap-id fmap id ≡ id
-- | fmap-distrib ∀ g h . fmap (g ◦ h) ≡ fmap g ◦ fmap h

{-@ data Identity where
        Val :: n:Int -> Identity @-}
data Identity where
  Val :: Int -> Identity
  deriving (Eq)

{-@ reflect fmap @-}
{-@ fmap :: (Int -> Int) -> Identity -> Identity @-}
fmap :: (Int -> Int) -> Identity -> Identity
fmap f (Val x) = Val (f x)

{-@ reflect id @-}
{-@ id :: Int -> Int @-}
id :: Int -> Int
id x = x

{-@ reflect idI @-}
{-@ idI :: Identity -> Identity @-}
idI :: Identity -> Identity
idI x = x

{-@ reflect compose @-}
{-@ compose :: (Int -> Int) -> (Int -> Int) -> Int -> Int @-}
compose :: (Int -> Int) -> (Int -> Int) -> Int -> Int
compose f g x = f (g x)

{-@ reflect composeI @-}
{-@ composeI :: (Identity -> Identity) -> (Identity -> Identity) -> Identity -> Identity @-}
composeI :: (Identity -> Identity) -> (Identity -> Identity) -> Identity -> Identity
composeI f g x = f (g x)

{-@ fmap_id :: xs:Identity -> { fmap id xs == idI xs } @-}
fmap_id :: Identity -> Proof
fmap_id (Val x) =
  trivial

{-@ fmap_distrib :: f:(Int -> Int) -> g:(Int -> Int) -> xs:Identity
               -> { fmap  (compose f g) xs == (composeI (fmap f) (fmap g)) (xs) } @-}
fmap_distrib :: (Int -> Int) -> (Int -> Int) -> Identity -> Proof
fmap_distrib f g (Val x) =
  trivial
