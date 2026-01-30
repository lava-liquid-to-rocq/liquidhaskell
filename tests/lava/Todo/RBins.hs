{-@ LIQUID "--lava" @-}
{-@ LIQUID "--ple" @-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PackageImports #-}

module Todo.RBins where

{- HLInt ignore -}
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
