{-# LANGUAGE FlexibleContexts #-}
{-@ LIQUID "--refcore" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
{-# LANGUAGE IncoherentInstances #-}

module TranslationTests.FunctorMaybe where

{- HLInt ignore -}
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (Just, Maybe, Nothing, fmap, id)

-- | Functor Laws :
-- | fmap-id fmap id ≡ id
-- | fmap-distrib ∀ g h . fmap (g ◦ h) ≡ fmap g ◦ fmap h

{-@ data MaybeInt where
        Nothing :: MaybeInt
        Just :: Int -> MaybeInt @-}
data MaybeInt where
  Nothing :: MaybeInt
  Just :: Int -> MaybeInt
  deriving (Eq)

{-@ reflect fmap @-}
{-@ fmap :: (Int -> Int) -> MaybeInt -> MaybeInt @-}
fmap :: (Int -> Int) -> MaybeInt -> MaybeInt
fmap _ Nothing = Nothing
fmap f (Just x) = Just (f x)

{-@ reflect id @-}
{-@ id:: Int -> Int @-}
id :: Int -> Int
id x = x

{-@ reflect idM @-}
{-@ idM:: MaybeInt -> MaybeInt @-}
idM :: MaybeInt -> MaybeInt
idM x = x

{-@ reflect compose @-}
{-@ compose :: (Int -> Int) -> (Int -> Int) -> Int -> Int @-}
compose :: (Int -> Int) -> (Int -> Int) -> Int -> Int
compose f g x = f (g x)

{-@ reflect composeM @-}
{-@ composeM :: (MaybeInt -> MaybeInt) -> (MaybeInt -> MaybeInt) -> MaybeInt -> MaybeInt @-}
composeM :: (MaybeInt -> MaybeInt) -> (MaybeInt -> MaybeInt) -> MaybeInt -> MaybeInt
composeM f g x = f (g x)

{-@ fmap_id :: xs:MaybeInt -> { fmap id xs == idM xs } @-}
fmap_id :: MaybeInt -> Proof
fmap_id Nothing = trivial
fmap_id (Just _) = trivial

-- | Distribution

{-@ reflect distrib_left_hand @-}
{-@ distrib_left_hand:: f:(Int -> Int) -> g:(Int -> Int) -> xs:MaybeInt
               -> MaybeInt @-}
distrib_left_hand :: (Int->Int) -> (Int->Int) -> MaybeInt -> MaybeInt      
distrib_left_hand f g xs = fmap (compose f g) xs

{-@ reflect distrib_right_hand @-}
{-@ distrib_right_hand:: f:(Int -> Int) -> g:(Int -> Int) -> xs:MaybeInt
               -> MaybeInt @-}
distrib_right_hand :: (Int->Int) -> (Int->Int) -> MaybeInt -> MaybeInt
distrib_right_hand f g xs = (composeM (fmap f) (fmap g)) xs

{-@ fmap_distrib :: f:(Int -> Int) -> g:(Int -> Int) -> xs:MaybeInt
               -> {v:Proof | distrib_left_hand f g xs == distrib_right_hand f g xs } @-}
fmap_distrib :: (Int -> Int) -> (Int -> Int) -> MaybeInt -> Proof
fmap_distrib _ _ Nothing = trivial
fmap_distrib f g (Just x) = trivial

-- 47 SLOC

