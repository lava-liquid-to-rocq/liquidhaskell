{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-# OPTIONS_GHC -fplugin=Lava #-}

module PLE.Peano where

import GHC.Exts
{-@ embed GHC.Exts.Int as Int @-}
{-@ embed GHC.Exts.Bool as bool @-}
{-@ embed GHC.Exts.Int# as Int @-}
{-@ assume GHC.Exts.I# :: x:Int# -> {v: Int | v = (x :: int) } @-}
{-@ embed GHC.Exts.Addr# as Str @-}
{-@ embed GHC.Exts.Word64# as Int @-}
{-@ assume (+)  :: x:_ -> y:_ -> {v:_ | x + y  = v} @-}
{-@ assume (-)  :: x:_ -> y:_ -> {v:_ | x - y  = v} @-}
{-@ assume (<)  :: x:_ -> y:_ -> {v:_ | x < y  = v} @-}
{-@ assume (==)  :: x:_ -> y:_ -> {v:_ | (x = y)  = v} @-}

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (plus)

-- Why do we need these?
zeroR :: Peano -> Proof
zeroL :: Peano -> Proof
plusAssoc :: Peano -> Peano -> Peano -> Proof
plusComm :: Peano -> Peano -> Proof
plusSuccR :: Peano -> Peano -> Proof

{-@ type Nat = {v:Int | v >= 0} @-}

{-@ data Peano = Z | S Peano @-}
data Peano = Z | S Peano

{-@ measure toInt @-}
toInt :: Peano -> Int
{-@ toInt :: Peano -> Nat @-}
toInt Z = 0
toInt (S n) = 1 + toInt n

{-@ axiomatize plus @-}
{-@ plus :: Peano -> Peano -> Peano @-}
plus :: Peano -> Peano -> Peano
plus Z m = m
plus (S n) m = S (plus n m)

{-@ zeroL :: n:Peano -> { plus Z n == n }  @-}
zeroL n = trivial

{-@ zeroR :: n:Peano -> { plus n Z == n }  @-}
zeroR Z = trivial
zeroR (S n) = zeroR n

{-@ plusSuccR :: n:Peano -> m:Peano -> { plus n (S m) = S (plus n m) } @-}
plusSuccR Z _ = trivial
plusSuccR (S n) m = plusSuccR n m

{-@ plusComm :: a:_ -> b:_  -> {plus a b == plus b a} @-}
plusComm Z b = zeroR b
plusComm (S a) b = plusComm a b &&& plusSuccR b a

{-@ plusAssoc :: a:_ -> b:_ -> c:_ -> {plus (plus a b) c == plus a (plus b c) } @-}
plusAssoc Z _ _ = trivial
plusAssoc (S a) b c = plusAssoc a b c
