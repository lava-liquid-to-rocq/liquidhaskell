{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-# OPTIONS_GHC -fplugin=Lava #-}

module PLE.Compose where

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
import Prelude hiding (map)

{-@ reflect compose @-}
{-@ compose :: (Int -> Int) -> (Int -> Int) -> Int -> Int @-}
compose :: (Int -> Int) -> (Int -> Int) -> Int -> Int
compose f g x = f (g x)

{-@ prop1 :: f:(Int -> Int) -> g:(Int -> Int) -> x:Int
          -> {v: Proof | f (g x) == compose f g x } @-}
prop1 :: (Int -> Int) -> (Int -> Int) -> Int -> Proof
prop1 f g x = trivial

{-@ prop2 :: f:(Int -> Int) -> g:(Int -> Int) -> x:Int
          -> {v: Proof | compose f g x == compose f g x } @-}
prop2 :: (Int -> Int) -> (Int -> Int) -> Int -> Proof
prop2 f g x = trivial
