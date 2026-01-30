{-@ LIQUID "--lava" @-}
{-@ LIQUID "--ple" @-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PackageImports #-}

module Todo.RBinsToBins where

{- HLInt ignore -}
import Language.Haskell.Liquid.ProofCombinators
import Todo.RBins

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
