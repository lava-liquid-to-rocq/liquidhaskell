{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-# OPTIONS_GHC -fplugin=Lava #-}

module PLE.Euclide where

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
import Prelude hiding (gcd, mod)

{-@ type Nat = {v:Int | v >= 0} @-}
type Nat = Int

{-@ reflect gcd @-}
{-@ gcd :: a:Nat -> b:{Nat | b < a } -> Int @-}
gcd :: Int -> Int -> Int
gcd a b
  | b == 0 || a == 0 =
      a
  | otherwise =
      gcd b (a `modr` b)

{-@ reflect modr @-}
{-@ modr :: a:Nat -> b:{Int | 0 < b} -> {v:Nat | v < b } @-}
modr :: Int -> Int -> Int
modr a b
  | a < b = a
  | otherwise =
      modr (a - b) b
