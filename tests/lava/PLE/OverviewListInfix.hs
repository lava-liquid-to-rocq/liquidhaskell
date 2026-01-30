{-# LANGUAGE FlexibleContexts #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-# LANGUAGE IncoherentInstances #-}
{-# OPTIONS_GHC -fplugin=Lava #-}

module PLE.OverviewListInfix where

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
import Prelude hiding (map, (++), (.))

{-@ type Nat = {v:Int | v >= 0} @-}

{-@ reflect append @-}
{-@ append :: L -> L -> L @-}
append :: L -> L -> L
append N ys = ys
append (C x xs) ys = C x (append xs ys)

{-@ associative :: xs:L -> ys:L -> zs:L
                -> {append (append xs ys) zs == append xs (append ys zs)} @-}
associative :: L -> L -> L -> Proof
associative N ys zs =
  trivial
associative (C x xs) ys zs =
  associative xs ys zs

{-@ data L = N | C {headlist :: Int, taillist :: L }@-}
data L = N | C Int L

{-@ measure llen @-}
llen :: L -> Int
{-@ llen :: L -> Nat @-}
llen N = 0
llen (C _ xs) = 1 + llen xs
