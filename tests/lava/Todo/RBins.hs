{-@ LIQUID "--lava" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PackageImports #-}

module Todo.RBins where

{- HLint ignore -}
import Language.Haskell.Liquid.ProofCombinators

{-@ data RBin where
        RZ :: RBin
        RB0 :: n:{x: RBin | x != RZ} -> {x: RBin | x != RZ}
        RB1 :: n:RBin ->  {x: RBin | x != RZ} @-}
data RBin where
  RZ :: RBin
  RB0 :: RBin -> RBin
  RB1 :: RBin -> RBin
  deriving (Eq)

{-@ reflect incRBin @-}
{-@ incRBin :: RBin -> {x: RBin | x != RZ} @-}
incRBin :: RBin -> RBin
incRBin RZ = RB1 RZ
incRBin (RB0 n) = RB1 n
incRBin (RB1 n) = RB0 (incRBin n)
