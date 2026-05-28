{-@ LIQUID "--lava" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}

module Import.SoftwareFoundationsInduction where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (pred)

import Import.SoftwareFoundationsBasics


{-@ add_0_r:: n:MyNat -> {plus n O = n} @-}
add_0_r O = trivial
add_0_r (S n') = add_0_r n'

{-@ minus_n_n:: n:MyNat -> {minus n n = O} @-}
minus_n_n O = trivial
minus_n_n (S n') = minus_n_n n'

{-@ mul_0_r:: n:MyNat -> {mult n O = O} @-}
mul_0_r O = trivial
mul_0_r (S n') = mul_0_r n'

{-@ plus_n_Sm:: n:MyNat -> m:MyNat -> {S (plus n m) = plus n (S m)} @-}
plus_n_Sm :: MyNat -> MyNat -> Proof
plus_n_Sm O m = trivial
plus_n_Sm (S n') m = plus_n_Sm n' m

{-@ add_comm:: n:MyNat -> m:MyNat -> {plus n m = plus m n} @-}
add_comm O m = add_0_r m
add_comm (S n') m = plus_n_Sm m n' ? add_comm n' m

-- + 16 SLoc
-- 414 SLoc

