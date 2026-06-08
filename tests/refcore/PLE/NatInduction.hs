{-@ LIQUID "--refcore" @-}

module PLE.NatInduction where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (range, sum)

{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--exactdc" @-}

{-@ type Nat = {v:Int | v >= 0} @-}
type Nat = Int

{-@ natinduction :: p:(Nat-> Bool) -> PAnd -> n:Nat -> {v:Proof | p n}  @-}
natinduction :: (Int -> Bool) -> PAnd -> Int -> Proof
natinduction p (PAnd p0 pi) n
  | n == 0 = p0
  | otherwise = pi n (natinduction p (PAnd p0 pi) (n - 1))

-- Example of proving with natinduction

{-@ prop :: n:Nat -> {godelProp n} @-}
prop :: Int -> Proof
prop n = natinduction godelProp (PAnd baseCase indCase) n

{-@ assume indCase :: n:Nat -> {v:Proof | godelProp (n-1)} -> {v:Proof | godelProp n} @-}
indCase :: Int -> Proof -> Proof
indCase _ _ = ()

{-@ assume baseCase :: {godelProp 0} @-}
baseCase :: Proof
baseCase = ()

{-@ reflect godelProp@-}
godelProp :: Int -> Bool
godelProp n = n == n

-- clearly ill-defined since p not in scope
{-@ data PAnd where
     PAnd :: v:{v:Proof | p 0} -> (n:Nat -> {v:Proof | p (n-1)} -> {v:Proof | p n}) -> PAnd @-}
data PAnd where
  PAnd :: Proof -> (Int -> Proof -> Proof) -> PAnd

{- main :: IO ()
main = pure () -}
