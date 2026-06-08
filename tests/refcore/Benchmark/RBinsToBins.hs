{-@ LIQUID "--refcore" @-}
{-@ LIQUID "--ple" @-}

module Benchmark.RBinsToBins where

{- HLInt ignore -}
import Language.Haskell.Liquid.ProofCombinators

{-@ data RBin where
        RB0 :: n:{x: RBin | x != RZ} -> {x: RBin | True}
        RZ :: {x: RBin | True}
        RB1 :: n:RBin ->  {x: RBin | True} @-}
data RBin where
  RB0 :: RBin -> RBin
  RZ :: RBin
  RB1 :: RBin -> RBin
  deriving (Eq)

{-@ data Bin where
        Z :: Bin
        B0 :: n:Bin -> Bin
        B1 :: n:Bin ->  Bin @-}
data Bin where
  Z :: Bin
  B0 :: Bin -> Bin
  B1 :: Bin -> Bin
  deriving (Eq)

{-@ rbinToBin :: b:RBin -> Bin @-}
rbinToBin :: RBin -> Bin
rbinToBin RZ = Z
rbinToBin (RB0 n) = B0 (rbinToBin n)
rbinToBin (RB1 n) = B1 (rbinToBin n)

-- 23 real LH LoC
