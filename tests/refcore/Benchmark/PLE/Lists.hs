{-@ LIQUID "--refcore" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Benchmark.PLE.Lists where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (length, (++))

{-@ type Nat = {v:Int | v >= 0} @-}
type Nat = Int

{-@ propConst1 :: () -> { (append (append (C 1 Emp) Emp) Emp) == (C 1 Emp) } @-}
propConst1 :: () -> Proof
propConst1 _ = trivial

{-@ automatic-instances propConst2 @-}
{-@ propConst2 :: () -> { (append (append (C 1 (C 2 Emp)) Emp) Emp) == (C 1 (C 2 Emp)) } @-}
propConst2 :: () -> Proof
propConst2 _ = trivial

{-@ automatic-instances propConst3 @-}
{-@ propConst3 :: () -> { (append (append (C 1 (C 2 (C 3 Emp))) Emp) Emp) == (C 1 (C 2 (C 3 Emp))) } @-}
propConst3 :: () -> Proof
propConst3 _ = trivial

prop :: Int -> L -> L -> L -> Proof
{-@ prop :: x:Int -> xs:L -> ys:L -> zs:L
         -> {append (append (C x xs) ys) zs == C x (append (append xs ys) zs) } @-}
prop x xs ys zs = trivial

{-@ data L [length] Int = Emp | C {x::Int, xs :: L } @-}
data L = Emp | C Int (L)

{-@ reflect length @-}
length :: L -> Int
{-@ length :: L -> Nat @-}
length Emp = 0
length (C _ xs) = 1 + length xs

{-@ reflect append @-}
{-@ append :: L -> L -> L @-}
append :: L -> L -> L
append Emp ys = ys
append (C x xs) ys = C x (append xs ys)
