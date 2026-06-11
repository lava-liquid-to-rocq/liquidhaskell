{-@ LIQUID "--refcore" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}

module Benchmark.PeanoNats where

{- HLInt ignore -}
import Language.Haskell.Liquid.ProofCombinators

{-@ data Nats where
        Zero :: Nats
        Suc :: n:Nats -> Nats @-}
data Nats where
  Zero :: Nats
  Suc :: Nats -> Nats
  deriving (Eq)

-- | Addition of natural numbers

{-@ reflect add @-}
{-@ add :: m:Nats -> n:Nats -> Nats @-}
add :: Nats -> Nats -> Nats
add Zero n = n
add (Suc m) n = Suc (add m n)

-- Addition definition lemmas:
{-@ add_zero_l :: n:Nats -> {add Zero n = n} @-}
add_zero_l :: Nats -> Proof
add_zero_l Zero = ()
add_zero_l (Suc n) = add_zero_l n

{-@ add_zero_l_test :: {add Zero (Suc (Suc Zero)) = Suc (Suc Zero)} @-}
add_zero_l_test :: Proof
add_zero_l_test = add_zero_l (Suc (Suc Zero))

-- Putting different refinements on add for testing purposes
{-@ add'' :: m:Nats -> n:Nats -> {v:Nats| add m n== v } @-}
add'' m n = add m n

{-@ add' :: m:Nats -> n:Nats -> {v:Nats| add (add m n) Zero == v } @-}
add' m n = add (add m n) Zero

-- | Addition is associative

{-@ add_assoc :: m:Nats -> n:Nats -> o:Nats -> {add m (add n o) == add (add m n) o} @-}
add_assoc :: Nats -> Nats -> Nats -> Proof
add_assoc Zero _ _ = trivial
add_assoc (Suc m) n o = add_assoc m n o

{-@ reflect one @-}
{-@ one :: Nats @-}
one = Suc Zero

-- 30 LOC

{-@ reflect two @-}
{-@ two :: Nats @-}
two = Suc one

-- | Multiplication of natural numbers

{-@ reflect mult @-}
{-@ mult :: m:Nats -> n:Nats -> Nats @-}
mult :: Nats -> Nats -> Nats
mult Zero _ = Zero
mult (Suc m) n = n `add` (mult m n)

-- Some lemmas required to prove add_sub eventually:

-- | Addition with right zero

{-@ add_zero_r :: n:Nats -> {add n Zero = n} @-}
add_zero_r :: Nats -> Proof
add_zero_r Zero = trivial
add_zero_r (Suc n) = add_zero_r n

-- | Addition with right successor.

{-@ add_suc_r :: m:Nats -> n:Nats -> {Suc (add m n) = add m (Suc n)} @-}
add_suc_r :: Nats -> Nats -> Proof
add_suc_r Zero _ = trivial
add_suc_r (Suc m) n = add_suc_r m n

-- | Addition distributes over right multiplication

{-@ add_dist_rmult:: m: Nats -> n: Nats -> o: Nats -> {mult (add m n) o == add (mult m o) (mult n o) } @-}
add_dist_rmult :: Nats -> Nats -> Nats -> Proof
add_dist_rmult Zero _ _ = trivial
add_dist_rmult (Suc m) n o = add_dist_rmult m n o ? add_assoc o (mult m o) (mult n o)

-- 50 LoC

-- An example to test nested inductive definitions

-- | Greater than or equals for natural numbers

{-@ reflect geqN @-}
{-@ geqN :: m: Nats -> n:Nats -> Bool @-}
geqN :: Nats -> Nats -> Bool
geqN _ Zero = True
geqN Zero (Suc _) = False
geqN (Suc m) (Suc n) = geqN m n

-- An example to test nested induction and non-trivial refinements

-- | Equality of natural numbers

{-@ reflect eqN @-}
{-@ eqN :: m:Nats -> n:Nats -> r:Bool @-}
{- eqN :: m:Nats -> n:Nats -> {r:Bool | r = (m == n) }@-}
eqN :: Nats -> Nats -> Bool
eqN Zero Zero = True
eqN (Suc m) (Suc n) = eqN m n
eqN _ _ = False

test_eqN :: Bool
{-@ test_eqN :: {r:Bool | r} @-}
test_eqN = eqN (Suc (Suc (Suc Zero))) (Suc (Suc (Suc Zero)))

test_eqN' :: Bool
{-@ test_eqN' :: {r:Bool | not r} @-}
test_eqN' = eqN (Suc (Suc Zero)) (Suc Zero)

-- Subtraction of nats, an example of a function with a non-trivial refinement in its domain

-- | subraction of natural numbers, only works if subracting from a number greater or equal to the number we subract from it

{-@ reflect sub @-}
{-@ sub :: m:Nats -> {n:Nats | geqN m n} -> {o:Nats | o != Zero <=> m != n} @-}
sub :: Nats -> Nats -> Nats
sub Zero Zero = Zero
sub (Suc m) Zero = Suc m
sub (Suc m) (Suc n) = sub m n

-- | subracting a number from itself yields Z

{-@ sub_self :: m: Nats -> n: Nats -> {eqN m n ==> sub m n = Zero} @-}
sub_self :: Nats -> Nats -> Proof
sub_self (Suc m) (Suc n) = sub_self m n
sub_self _ _ = trivial

-- Finally a more complicated example theorem by nested induction using two lemmas

-- | adding and then subracting a number is identity

{-@ add_sub :: m:Nats -> n:Nats -> {sub (add m n) n = m } @-}
add_sub :: Nats -> Nats -> Proof
add_sub Zero Zero = trivial
add_sub (Suc m) Zero = add_zero_r m
add_sub m (Suc n) = add_suc_r m n ? add_sub m n

-- A function for which we need two inductions
-- (and two generalizations of the arguments for the IH)
-- {-@ nested :: m:Nats -> n:Nats -> p:Nats -> Nats @-}
-- nested :: Nats -> Nats -> Nats -> Nats
-- nested (Suc m) n p = nested m n Zero
-- nested Zero (Suc n) p = nested Zero n Zero
-- nested Zero Zero p = p

-- 88 LoC
