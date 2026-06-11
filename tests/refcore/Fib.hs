{-@ LIQUID "--refcore" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}

module Benchmark.Fib where

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
import Prelude hiding (pred)

------------------------------------------------------------------------------------------
-- OUTLINE OF THE TUTORIAL
------------------------------------------------------------------------------------------

-- | Let's define the Fibonacci function and prove some properties about it.
-- | 0. Define fibonacci and prove it terminates.
-- | 1. Light Verification
-- | 2. Deep Verification
-- | 3. Reachability

------------------------------------------------------------------------------------------

------------------------------------------------------------------------------------------

-- | 0. Definition and Termination

------------------------------------------------------------------------------------------

{-@ fib :: i:{Int | 0 <= i} -> {v:Int | 0 <= v && i <= v} @-}
fib :: Int -> Int
fib i
  | i == 0 = 1
  | i == 1 = 1
  | otherwise = fib (i - 1) + fib (i - 2)

{-}
------------------------------------------------------------------------------------------
-- | 1   Light Verification
------------------------------------------------------------------------------------------
-- | 1.1 The result is always >= the input
-- {-@ fib :: i:Nat -> {v:Nat | i <= v }  @-}

-- | 1.2 The parity of the result follows a pattern based on i mod 3
-- {-@ fib :: i:Nat -> {v:Nat | fibMod3 i v }  @-}
------------------------------------------------------------------------------------------

{-@ inline fibMod3 @-}
fibMod3 :: Int -> Int -> Bool
fibMod3 i v = if i `mod` 3 == 0 || i `mod` 3 == 1 then v `mod` 2 == 1 else v `mod` 2 == 0

------------------------------------------------------------------------------------------
-- | 2   Deep Verification
-- | 2.1 What is fib 0, 1, 3, and 16?
-- | 2.2 Fibonacci is increasing
-- | 2.3 Fibonacci is monotonic
------------------------------------------------------------------------------------------

------------------------------------------------------------------------------------------
-- | 2.1 What is fib 0, 1, 3, and 16?
------------------------------------------------------------------------------------------

-- | To express properties about fib, **extrinsically**, ie outside of its type signature,
-- | we simply use the unit type `()` refined with the property we want to prove.

{-@ fib0 :: () -> {v:() |  fib 0 == 1 } @-}
fib0 :: () -> ()
fib0 _ = undefined

-- | But, the Haskell functions, like fib, are not allows by default in the refinement logic.

-- | The reflection flag allows us to use fib in specifications.
-- | After reflection, each call of fib is unfolded exactly once in the SMT solver.
-- | This is sufficient to prove fib facts up to fib 2 automatically.

{-@ reflect fib @-}

{-@ fib1 :: () -> { fib 1 == 1 } @-}
fib1 :: () -> ()
fib1 _ = fib 1 === 1 *** QED

{-@ fib3 :: () -> { fib 3 == 3 } @-}
fib3 :: () -> ()
fib3 _ = ()

-- | To automate such kind of standard evaluation steps, we can use the PLE flag.

{-@ LIQUID "--ple" @-}

fib3ple :: () -> ()
{-@ fib3ple :: () -> { fib 3 == 3 } @-}
fib3ple _ = ()

{-@ fib16 :: () -> { fib 16 == 1597 } @-}
fib16 :: () -> ()
fib16 _ = ()

------------------------------------------------------------------------------------------
-- | 2.2 Fibonacci is increasing
------------------------------------------------------------------------------------------
-- | To prove that fib is increasing, we need to prove a lemma first:
-- | fib i <= fib (i+1)

{-@ fibIncr :: i:Nat -> { fib i <= fib (i+1) } @-}
fibIncr :: Int -> ()
fibIncr 0 = ()
fibIncr 1 = ()
fibIncr i =  fib i
          === fib (i-1) + fib (i-2) ? fibIncr (i-2) ? fibIncr (i-1)
          =<= fib  i    + fib (i-1)
          === fib (i+1)
          *** QED

-- | Note that Liquid Haskell checks that the proof is terminating and that all cases are covered.
-- | It is a _mathematical_ proof!

------------------------------------------------------------------------------------------
-- | 2.3 Fibonacci is monotonic
------------------------------------------------------------------------------------------

{-@ fibMono :: i:Nat -> j:{Nat | i < j} -> { fib i <= fib j } / [j - i] @-}
fibMono :: Int -> Int -> ()
fibMono i j  | j == i + 1
  = fibIncr i
fibMono i j  | j > i + 1
  = fib i       ? fibMono i (j-1)
  =<= fib (j-1) ? fibIncr (j-1)
  =<= fib j
  *** QED

-- Interestingly, the proof requires the `fibIncr` lemma, but not the definition of `fib` itself!
-- So, we can abstract away the definition of `fib` and state that
-- each increasing function is monotonic!

{-@ fMono :: i:Nat -> j:{Nat | i < j}
          -> f:(Nat -> Nat) -> fIncr:(x:Nat -> { f x <= f (x+1) })
          -> { f i <= f j } / [j - i] @-}
fMono :: Int -> Int -> (Int -> Int) -> (Int -> ()) -> ()
fMono i j f fIncr | j == i + 1
  = fIncr i
fMono i j f fIncr | j > i + 1
  = f i       ? fMono i (j-1) f fIncr
  =<= f (j-1) ? fIncr (j-1)
  =<= f j
  *** QED

-- | With that, monotonicity of Fibonacci can be proved as:

{-@ fibMono' :: i:Nat -> j:{Nat | i < j} -> { fib i <= fib j } @-}
fibMono' :: Int -> Int -> ()
fibMono' i j = fMono i j fib fibIncr

------------------------------------------------------------------------------------------
-- | 3   Reachability
------------------------------------------------------------------------------------------

-- As a final exercise, and to state on topic, let's use Liquid Haskell to
-- determine which values can fib reach.

-- n can be reached by fib iff
-- there exists an x such that fib x = n
-- equivalently
-- (x:Nat, {fib x = n})

{-
   As a final exercise, and to state on topic, let's use Liquid Haskell to
   determine which values can fib reach.

  n can be reached by fib iff
    there exists an x such that fib x = n
      _equivalently_
    (x:Nat, {fib x = n})

  _ie,_ existentials are encoded as dependent pairs
        with the first component being the witness.
-}

------------------------------------------------------------------------------------------
-- | 3.1 Is 8 reachable by fib?
------------------------------------------------------------------------------------------

{-@ reachable8 :: () -> (x::Nat, { v:() | fib x == 8}) @-}
reachable8 :: () -> (Int, ())
reachable8 _ = (5, liquidAssert (fib 5 == 8) ())

------------------------------------------------------------------------------------------
-- | 3.2 Is 7 reachable by fib?
------------------------------------------------------------------------------------------

{-
To show non reachability, we need to negate the existential.
      not (exists x. fib x = 7)
     equivalently
      (exists x. fib x = 7) -> False

      _ie_, negation is encoded as an implication to False.
-}

{-@ unreachable7 :: () -> ((x::Nat, { v:() | fib x == 7}) -> ({v:() |  False})) @-}
unreachable7 :: () -> ((Int, ()) -> ())
unreachable7 _ (x, _) | x > 7
  = liquidAssert (fib x == 7) ()
unreachable7 _ (x, _) | x < 0
  = liquidAssert (fib x == 7) ()
unreachable7 _ (0, _)
  = liquidAssert (fib 0 /= 7) ()
unreachable7 _ (1, _)
  = liquidAssert (fib 1 /= 7) ()
unreachable7 _ (2, _)
  = liquidAssert (fib 2 /= 7) ()
unreachable7 _ (3, _)
  = liquidAssert (fib 3 /= 7) ()
unreachable7 _ (4, _)
  = liquidAssert (fib 4 /= 7) ()
unreachable7 _ (5, _)
  = liquidAssert (fib 5 /= 7) ()
unreachable7 _ (6, _)
  = liquidAssert (fib 6 /= 7) ()
unreachable7 _ (7, _)
  = liquidAssert (fib 7 /= 7) ()
-}

