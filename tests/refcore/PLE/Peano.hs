{-@ LIQUID "--refcore" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module PLE.Peano where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (plus)

{-@ data Peano where
	Zero :: Peano
	S :: Peano -> Peano @-}
data Peano = Zero | S Peano

-- Why do we need these?
zeroR :: Peano -> Proof
zeroL :: Peano -> Proof
plusAssoc :: Peano -> Peano -> Peano -> Proof
plusComm :: Peano -> Peano -> Proof
plusSuccR :: Peano -> Peano -> Proof
{-@ type Nat = {v:Int | v >= 0} @-}

{-@ measure toInt @-}
toInt :: Peano -> Int
{-@ toInt :: Peano -> Nat @-}
toInt Zero = 0
toInt (S n) = 1 + toInt n

{-@ axiomatize plus @-}
{-@ plus :: Peano -> Peano -> Peano @-}
plus :: Peano -> Peano -> Peano
plus Zero m = m
plus (S n) m = S (plus n m)

{-@ zeroL :: n:Peano -> { plus Zero n == n }  @-}
zeroL n = trivial

{-@ zeroR :: n:Peano -> { plus n Zero == n }  @-}
zeroR Zero = trivial
zeroR (S n) = zeroR n

{-@ plusSuccR :: n:Peano -> m:Peano -> { plus n (S m) = S (plus n m) } @-}
plusSuccR Zero _ = trivial
plusSuccR (S n) m = plusSuccR n m

{-@ plusComm :: a:_ -> b:_  -> {plus a b == plus b a} @-}
plusComm Zero b = zeroR b
plusComm (S a) b = plusComm a b &&& plusSuccR b a

{-@ plusAssoc :: a:_ -> b:_ -> c:_ -> {plus (plus a b) c == plus a (plus b c) } @-}
plusAssoc Zero _ _ = trivial
plusAssoc (S a) b c = plusAssoc a b c
