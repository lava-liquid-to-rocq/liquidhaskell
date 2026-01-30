{-# OPTIONS_GHC -fplugin=Lava #-}

module PLE.NatInduction where

import GHC.Exts
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (range, sum)

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

{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--exactdc" @-}

{-@ type Nat = {v:Int | v >= 0} @-}
type Nat = Int

{-@ natinduction :: p:(Nat-> Bool) -> PAnd -> n:Nat -> {v:Proof | p n}  @-}
natinduction :: (Int -> Bool) -> PAnd -> Int -> Proof
natinduction p (PAnd p0 pi) n
  | n == 0 = p0
  | otherwise = pi n (natinduction p (PAnd p0 pi) (n - 1))

-- Example of proving with natinduction

{-@ prop :: n:Nat -> {godelProp n} @-}
prop :: Int -> Proof
prop n = natinduction godelProp (PAnd baseCase indCase) n

{-@ assume indCase :: n:Nat -> {v:Proof | godelProp (n-1)} -> {v:Proof | godelProp n} @-}
indCase :: Int -> Proof -> Proof
indCase _ _ = ()

{-@ assume baseCase :: {godelProp 0} @-}
baseCase :: Proof
baseCase = ()

{-@ reflect godelProp@-}
godelProp :: Int -> Bool
godelProp n = n == n

{-@ data PAnd where
     PAnd :: v:{v:Proof | p 0} -> (n:Nat -> {v:Proof | p (n-1)} -> {v:Proof | p n}) -> PAnd @-}
data PAnd where
  PAnd :: Proof -> (Int -> Proof -> Proof) -> PAnd

{- main :: IO ()
main = pure () -}
