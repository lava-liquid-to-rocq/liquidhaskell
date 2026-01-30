{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE IncoherentInstances #-}

{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--lava" @-}

module Benchmark.FunctorMaybe where

{- HLInt ignore -}
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (Just, Maybe, Nothing, fmap, id)

-- | Functor Laws :
-- | fmap-id fmap id ≡ id
-- | fmap-distrib ∀ g h . fmap (g ◦ h) ≡ fmap g ◦ fmap h

{-@ data Maybe where
        Nothing :: Maybe
        Just :: Int -> Maybe @-}
data Maybe where
  Nothing :: Maybe
  Just :: Int -> Maybe
  deriving (Eq)

{-@ reflect fmap @-}
{-@ fmap :: (Int -> Int) -> Maybe -> Maybe @-}
fmap :: (Int -> Int) -> Maybe -> Maybe
fmap _ Nothing = Nothing
fmap f (Just x) = Just (f x)

{-@ reflect id @-}
{-@ id:: Int -> Int @-}
id :: Int -> Int
id x = x

{-@ reflect idM @-}
{-@ idM:: Maybe -> Maybe @-}
idM :: Maybe -> Maybe
idM x = x

{-@ reflect compose @-}
{-@ compose :: (Int -> Int) -> (Int -> Int) -> Int -> Int @-}
compose :: (Int -> Int) -> (Int -> Int) -> Int -> Int
compose f g x = f (g x)

{-@ reflect composeM @-}
{-@ composeM :: (Maybe -> Maybe) -> (Maybe -> Maybe) -> Maybe -> Maybe @-}
composeM :: (Maybe -> Maybe) -> (Maybe -> Maybe) -> Maybe -> Maybe
composeM f g x = f (g x)

{-@ fmap_id :: xs:Maybe -> { fmap id xs == idM xs } @-}
fmap_id :: Maybe -> Proof
fmap_id Nothing = trivial
fmap_id (Just _) = trivial

-- | Distribution

{-@ fmap_distrib :: f:(Int -> Int) -> g:(Int -> Int) -> xs:Maybe
               -> {v:Proof | fmap  (compose f g) xs == (composeM (fmap f) (fmap g)) (xs) } @-}
fmap_distrib :: (Int -> Int) -> (Int -> Int) -> Maybe -> Proof
fmap_distrib _ _ Nothing = trivial
fmap_distrib f g (Just x) = trivial
