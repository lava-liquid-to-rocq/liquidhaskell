{-# LANGUAGE FlexibleContexts #-}
{-@ LIQUID "--refcore" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
{-# LANGUAGE IncoherentInstances #-}

module Todo.TranslationTests.ApplicativeId where

{- HLInt ignore -}
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (fmap, id, pure, seq)

-- | Applicative Laws :
-- | identity      pure id <*> v = v
-- | composition   pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
-- | homomorphism  pure f <*> pure x = pure (f x)
-- | interchange   u <*> pure y = pure ($ y) <*> u

{-@ data Identity where
        Val :: n:Int -> Identity @-}
data Identity where
  Val :: Int -> Identity
  deriving (Eq)

{-@ data IdentityF where
        ValF :: n:(Int -> Int) -> IdentityF @-}
data IdentityF where
  ValF :: (Int -> Int) -> IdentityF

{-@ data IdentityF1 where
        ValF1 :: n:((Int -> Int) -> Int) -> IdentityF1 @-}
data IdentityF1 where
  ValF1 :: ((Int -> Int) -> Int) -> IdentityF1

{-@ data IdentityF2 where
        ValF2 :: n:((Int -> Int) -> Int -> Int) -> IdentityF2 @-}
data IdentityF2 where
  ValF2 :: ((Int -> Int) -> Int -> Int) -> IdentityF2

{-@ data IdentityF3 where
        ValF3 :: n:((Int -> Int) -> (Int -> Int) -> Int -> Int) -> IdentityF3 @-}
data IdentityF3 where
  ValF3 :: ((Int -> Int) -> (Int -> Int) -> Int -> Int) -> IdentityF3

{-@ reflect pure @-}
{-@ pure :: Int -> Identity @-}
pure :: Int -> Identity
pure x = Val x

{-@ reflect pureF @-}
{-@ pureF :: (Int -> Int) -> IdentityF @-}
pureF :: (Int -> Int) -> IdentityF
pureF f = ValF f

{-@ reflect pureF1 @-}
{-@ pureF1 :: ((Int -> Int) -> Int) -> IdentityF1 @-}
pureF1 :: ((Int -> Int) -> Int) -> IdentityF1
pureF1 f = ValF1 f

{-@ reflect pureF3 @-}
{-@ pureF3 :: ((Int -> Int) -> (Int -> Int) -> Int -> Int) -> IdentityF3 @-}
pureF3 :: ((Int -> Int) -> (Int -> Int) -> Int -> Int) -> IdentityF3
pureF3 f = ValF3 f

{-@ reflect seq @-}
{-@ seq :: IdentityF -> Identity -> Identity @-}
seq :: IdentityF -> Identity -> Identity
seq (ValF f) (Val x) = Val (f x)

{-@ reflect seqF @-}
{-@ seqF :: IdentityF1 -> IdentityF -> Identity @-}
seqF :: IdentityF1 -> IdentityF -> Identity
seqF (ValF1 f) (ValF x) = Val (f x)

{-@ reflect seqF1 @-}
{-@ seqF1 :: IdentityF2 -> IdentityF -> IdentityF @-}
seqF1 :: IdentityF2 -> IdentityF -> IdentityF
seqF1 (ValF2 f) (ValF x) = ValF (f x)

{-@ reflect seqF2 @-}
{-@ seqF2 :: IdentityF3 -> IdentityF -> IdentityF2 @-}
seqF2 :: IdentityF3 -> IdentityF -> IdentityF2
seqF2 (ValF3 f) (ValF x) = ValF2 (f x)

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

-- | Identity

{-@ identity :: x:Identity -> { seq (pureF id) x == x } @-}
identity :: Identity -> Proof
identity (Val x) =
  trivial

-- | Composition

{-@ composition :: x:IdentityF
                -> y:IdentityF
                -> z:Identity
                -> { (seq (seqF1 (seqF2 (pureF3 compose) x) y) z) == seq x (seq y z) } @-}
composition :: IdentityF -> IdentityF -> Identity -> Proof
composition (ValF x) (ValF y) (Val z) =
  trivial

-- | homomorphism  pure f <*> pure x = pure (f x)

{-@ homomorphism :: f:(Int -> Int) -> x:Int
                 -> { seq (pureF f) (pure x) == pure (f x) } @-}
homomorphism :: (Int -> Int) -> Int -> Proof
homomorphism f x =
  trivial

interchange :: IdentityF -> Int -> Proof
{-@ interchange :: u:(IdentityF) -> y:Int
     -> { seq u (pure y) == seqF (pureF1 (idollar y)) u }
  @-}
interchange (ValF f) x =
  trivial

-- 87 SLOC

