{-@ LIQUID "--refcore" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}

module Benchmark.Overview where

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

-- Theorem

{-@ thm1 :: xs:IList -> x:{v:Int | 5 < v} -> i:{i:Int | 0 <= i && i < (llen xs) }
         -> {get xs i == get (Cons x xs) (i+1)} @-}
thm1 :: IList -> Int -> Int -> Proof
thm1 _ x _ = trivial

-- thm1 _ x 0 = trivial
-- thm1 (Cons x xs) y i = trivial -- thm1 xs y (i-1)

{-@ reflect append @-}
{-@ append :: xs:IList -> ys:IList -> {v:IList | llen v == llen xs + llen ys  } @-}
append :: IList -> IList -> IList
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

{-@ thm2 :: xs:IList -> ys:IList -> i:{i:Int | 0 <= i && i < (llen xs) }
         -> {get xs i == get (append ys xs) (i+llen ys)} @-}
thm2 :: IList -> IList -> Int -> Proof
thm2 _ Nil _ = trivial
thm2 xs (Cons y ys) i =
  thm2 xs ys i
    -- ? (atIndex (append ys xs) (i + llen ys) == atIndex (Cons y (append ys xs)) ((i + llen ys)+1))
    ? thm1 (append ys xs) y (i + llen ys)

-- works but totally screws up performance
{-@ reflect applyToFirst @-}
{-@ applyToFirst :: f:(Int -> {y:Int | 5 < y}) -> {xs:IList | llen xs /= 0} -> {v:Int | v = f (get xs 0)} @-}
applyToFirst :: (Int -> Int) -> IList -> Int
applyToFirst f (Cons x l') = f x

{- {-@ reflect imap @-}
{-@ imap :: f:(Int -> {v':Int | 5 < v'}) -> xs:IList -> {v:IList | llen v = llen xs} @-}
imap :: (Int -> Int) -> IList -> IList
imap f (Cons x l') = Cons (f x) (imap f l')
imap _ Nil = Nil -}

-- so far 32 real (non-comment or whitespace) LH LoC
