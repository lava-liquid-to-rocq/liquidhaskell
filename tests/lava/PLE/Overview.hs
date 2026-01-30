{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-# OPTIONS_GHC -fplugin=Lava #-}

module PLE.Overview where

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

-- import Helper
import Language.Haskell.Liquid.ProofCombinators

{-@ type Nat = {v:Int | v >= 0} @-}

{-@ reflect fib @-}
{-@ fib :: n:Nat -> Nat @-}
fib :: Int -> Int
fib n
  | n == 0 = 0
  | n == 1 = 1
  | otherwise = fib (n - 1) + fib (n - 2)

-- | How do I teach the logic the implementation of fib?
-- | Two trents:
-- | Dafny, F*, HALO: create an SMT axiom
-- | forall n. fib n == if n == 0 then 0 else if n == 1 == 1 else fib (n-1) + fin (n-2)

-- | Problem: When does this axiom trigger?
-- | undefined: unpredicted behaviours + the butterfly effect

-- | LiquidHaskell: logic does not know about fib:
-- | reffering to fib in the logic will lead to un sorted refinements

{- unsafe :: _ -> { fib 2 == 1 } @-}
-- unsafe () = ()

{-@ safe :: () -> { fib 2 == 1 } @-}
safe :: () -> Proof
safe () = trivial

-- | fib 2 == fib 1 + fib 0

-- | Adding some structure to proofs
-- | ==. :: x:a -> y:{a | x == y} -> {v:a | v == x && x == y}
-- | proofs are unit
-- | toProof :: a -> Proof
-- | type Proof = ()

{-@ automatic-instances safe' @-}

{-@ safe' :: () ->  { fib 3 == 2 } @-}
safe' () = trivial

{-@ safe'' :: () ->  { fib 3 == 2 } @-}
safe'' () = safe ()

-- From Helper

{-@ type Greater N = {v:Int | N < v } @-}

gen_incr :: (Int -> Int) -> (Int -> Proof) -> (Int -> Int -> Proof)
{-@ gen_incr :: f:(Nat -> Int)
                   -> (z:Nat -> {f z <= f (z+1)})
                   ->  x:Nat -> y:Greater x -> {f x <= f y} / [y] @-}
gen_incr f thm x y
  | x + 1 == y =
      f x
        ? thm x
        =<= f (x + 1)
        =<= f y
        *** QED
  | x + 1 < y =
      f x
        ? gen_incr f thm x (y - 1)
        =<= f (y - 1)
        ? thm (y - 1)
        =<= f y
        *** QED

fib_incr_gen :: Int -> Int -> Proof
{-@ fib_incr_gen :: n:Nat -> m:Greater n -> {fib n <= fib m}
  @-}
fib_incr_gen =
  gen_incr fib fib_incr

fib_incr :: Int -> Proof
{-@ fib_incr :: n:Nat -> {fib n <= fib (n+1)} @-}
fib_incr n
  | n == 0 =
      [fib 1] *** QED
  | n == 1 =
      [fib 2] *** QED
  | otherwise =
      (fib_incr (n - 1) &&& fib_incr (n - 2))
