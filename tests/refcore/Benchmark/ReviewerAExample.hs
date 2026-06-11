{-@ LIQUID "--refcore" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}

module Benchmark.ReviewerAExample where

import Language.Haskell.Liquid.ProofCombinators

-- import Prelude_LHAssumptions

{-@ data IList where
        Nil :: IList
        Cons :: n:{v:Int | 5 < v} -> l:IList -> IList @-}
data IList where
  Cons :: Int -> IList -> IList
  Nil :: IList
  deriving (Eq)

-- | length of an IList

{-@ reflect llen @-}
{-@ llen :: l:IList -> {v:Int | v >= 0} @-}
llen :: IList -> Int
llen (Cons _ l') = llen l' + 1
llen Nil = 0

-- | Greater than for natural numbers

{-@ reflect get @-}
{-@ get :: xs:IList -> i:{i:Int | 0 <= i && i < (llen xs) } -> {v:Int | 5 < v } @-}
get :: IList -> Int -> Int
get (Cons x xs') i' = if i' == 0 then x else get xs' (i' - 1)


-- | Reviewer A example
{-@ surprise :: x:Int -> l:IList -> {u: () | get Nil 4 = 10 } @-}
surprise :: Int -> IList -> ()
surprise _ _ = ()