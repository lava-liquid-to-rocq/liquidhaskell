{-@ LIQUID "--refcore" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}

module Import.SoftwareFoundationsLists where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (pred)

import Import.SoftwareFoundationsBasics
import Import.SoftwareFoundationsInduction

{-@ data Natprod where
        Pair :: n1:MyNat -> n2:MyNat -> Natprod @-}
data Natprod where
  Pair :: MyNat -> MyNat -> Natprod
  deriving (Eq)

{-@ reflect fstSF @-}
{-@ fstSF:: p:Natprod -> MyNat @-}
fstSF :: Natprod -> MyNat
fstSF (Pair n1 n2) = n1

{-@ reflect sndSF @-}
{-@ sndSF:: p:Natprod -> MyNat @-}
sndSF :: Natprod -> MyNat
sndSF (Pair n1 n2) = n2

{-@ reflect swap_pair @-}
{-@ swap_pair:: p:Natprod ->Natprod @-}
swap_pair :: Natprod -> Natprod
swap_pair (Pair x y) = Pair y x

{-@ surjective_pairing':: n:MyNat -> m:MyNat -> {Pair n m = Pair (fstSF (Pair n m)) (sndSF (Pair n m))} @-}
surjective_pairing' :: MyNat -> MyNat -> Proof
surjective_pairing' n m = trivial

{-@ surjective_pairing:: p:Natprod -> {p = Pair (fstSF p) (sndSF p)} @-}
surjective_pairing :: Natprod -> Proof
surjective_pairing (Pair n m) = trivial

-- 23 SLoc

