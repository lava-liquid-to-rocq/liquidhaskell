{-# LANGUAGE FlexibleContexts #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-# LANGUAGE IncoherentInstances #-}
{-# OPTIONS_GHC -fplugin=Lava #-}

module PLE.MapFusion where

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
compose :: (Int -> Int) -> (Int -> Int) -> Int -> Int
compose f g x = f (g x)

{-@ reflect map @-}
map :: (Int -> Int) -> L -> L
map f N = N
map f (C x xs) = f x `C` map f xs

{-@ map_fusion :: f:(Int -> Int) -> g:(Int -> Int) -> xs:L
      -> {map (compose f g) xs == compose (map f) (map g) xs } @-}
map_fusion :: (Int -> Int) -> (Int -> Int) -> L -> Proof
map_fusion _ _ N = trivial
map_fusion f g (C x xs) = map_fusion f g xs

{-@ data L = N | C {headlist :: Int, taillist :: L }@-}
data L = N | C Int L

{-@ reflect llen @-}
llen :: L -> Int
{-@ llen :: L -> {v:Int | v >= 0} @-}
llen N = 0
llen (C _ xs) = 1 + llen xs
