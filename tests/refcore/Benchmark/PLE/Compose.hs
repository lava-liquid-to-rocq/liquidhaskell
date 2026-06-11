{-@ LIQUID "--refcore" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Benchmark.PLE.Compose where

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

-- 12 SLOC
