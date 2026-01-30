{-@ LIQUID "--lava" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
{-# LANGUAGE FlexibleContexts #-}

module TranslationTests.ApplicativeMaybe where

{- HLInt ignore -}
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (Just, Maybe, Nothing, fmap, id, pure, seq)

-- | Applicative Laws :
-- | identity      pure id <*> v = v
-- | composition   pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
-- | homomorphism  pure f <*> pure x = pure (f x)
-- | interchange   u <*> pure y = pure ($ y) <*> u

{-@ data Maybe where
      Nothing :: Maybe
      Just :: Int -> Maybe @-}
data Maybe where
  Nothing :: Maybe
  Just :: Int -> Maybe
  deriving (Eq)

{-@ data MaybeF where
      NothingF :: MaybeF
      JustF :: n:(Int -> Int) -> MaybeF @-}
data MaybeF where
  NothingF :: MaybeF
  JustF :: (Int -> Int) -> MaybeF

{-@ data MaybeF1 where
      NothingF1::MaybeF1
      JustF1 :: n:((Int -> Int) -> Int) -> MaybeF1 @-}
data MaybeF1 where
  NothingF1 :: MaybeF1
  JustF1 :: ((Int -> Int) -> Int) -> MaybeF1

{-@ data MaybeF2 where
      NothingF2::MaybeF2
      JustF2 :: n:((Int -> Int) -> Int -> Int) -> MaybeF2 @-}
data MaybeF2 where
  NothingF2 :: MaybeF2
  JustF2 :: ((Int -> Int) -> Int -> Int) -> MaybeF2

{-@ data MaybeF3 where
      NothingF3::MaybeF3
      JustF3 :: n:((Int -> Int) -> (Int -> Int) -> Int -> Int) -> MaybeF3 @-}
data MaybeF3 where
  NothingF3 :: MaybeF3
  JustF3 :: ((Int -> Int) -> (Int -> Int) -> Int -> Int) -> MaybeF3

{-@ reflect pure @-}
{-@ pure :: Int -> Maybe @-}
pure :: Int -> Maybe
pure x = Just x

{-@ reflect pureF @-}
{-@ pureF :: (Int -> Int) -> MaybeF @-}
pureF :: (Int -> Int) -> MaybeF
pureF f = JustF f

{-@ reflect pureF1 @-}
{-@ pureF1 :: ((Int -> Int) -> Int) -> MaybeF1 @-}
pureF1 :: ((Int -> Int) -> Int) -> MaybeF1
pureF1 f = JustF1 f

{-@ reflect pureF3 @-}
{-@ pureF3 :: ((Int -> Int) -> (Int -> Int) -> Int -> Int) -> MaybeF3 @-}
pureF3 :: ((Int -> Int) -> (Int -> Int) -> Int -> Int) -> MaybeF3
pureF3 f = JustF3 f

{-@ reflect seq @-}
{-@ seq :: MaybeF -> Maybe -> Maybe @-}
seq :: MaybeF -> Maybe -> Maybe
seq (JustF f) (Just x) = Just (f x)
seq _ _ = Nothing

{-@ reflect seqF @-}
{-@ seqF :: MaybeF1 -> MaybeF -> Maybe @-}
seqF :: MaybeF1 -> MaybeF -> Maybe
seqF (JustF1 f) (JustF x) = Just (f x)
seqF _ _ = Nothing

{-@ reflect seqF1 @-}
{-@ seqF1 :: MaybeF2 -> MaybeF -> MaybeF @-}
seqF1 :: MaybeF2 -> MaybeF -> MaybeF
seqF1 (JustF2 f) (JustF x) = JustF (f x)
seqF1 _ _ = NothingF

{-@ reflect seqF2 @-}
{-@ seqF2 :: MaybeF3 -> MaybeF -> MaybeF2 @-}
seqF2 :: MaybeF3 -> MaybeF -> MaybeF2
seqF2 (JustF3 f) (JustF x) = JustF2 (f x)
seqF2 _ _ = NothingF2

{-@ reflect id @-}
{-@ id :: Int -> Int @-}
id :: Int -> Int
id x = x

{-@ reflect idollar @-}
{-@ idollar :: Int -> (Int -> Int) -> Int @-}
idollar :: Int -> (Int -> Int) -> Int
idollar x f = f x

{-@ reflect compose @-}
{-@ compose :: (Int -> Int) -> (Int -> Int) -> Int -> Int @-}
compose :: (Int -> Int) -> (Int -> Int) -> Int -> Int
compose f g x = f (g x)

-- | Maybe

{-@ identity :: x:Maybe -> { seq (pureF id) x == x } @-}
identity :: Maybe -> Proof
identity Nothing = trivial
identity (Just _) = trivial

-- | Composition

{-@ composition :: x:MaybeF
                -> y:MaybeF
                -> z:Maybe
                -> { (seq (seqF1 (seqF2 (pureF3 compose) x) y) z) == seq x (seq y z) } @-}
composition :: MaybeF -> MaybeF -> Maybe -> Proof
composition NothingF _ _ =
  trivial
composition _ NothingF _ =
  trivial
composition _ _ Nothing =
  trivial
composition (JustF x) (JustF y) (Just z) =
  trivial

-- | homomorphism  pure f <*> pure x = pure (f x)

{-@ homomorphism :: f:(Int -> Int) -> x:Int
                 -> { seq (pureF f) (pure x) == pure (f x) } @-}
homomorphism :: (Int -> Int) -> Int -> Proof
homomorphism f x =
  trivial

{-@ interchange :: u:(MaybeF) -> y:Int
     -> { seq u (pure y) == seqF (pureF1 (idollar y)) u }
  @-}
interchange :: MaybeF -> Int -> Proof
interchange NothingF _ =
  trivial
interchange (JustF f) x =
  trivial

-- 109 SLOC

