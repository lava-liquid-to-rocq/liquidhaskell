{-@ LIQUID "--ple" @-}
-- {-@ LIQUID "--diff" @-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PackageImports #-}
{- OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-# OPTIONS_GHC -fplugin=Lava #-}

module Todo.RBins where

{-@ embed GHC.Types.Int as Int @-}
{-@ embed GHC.Integer.Type.Integer as Integer @-}
{-@ embed GHC.Types.Bool as bool @-}

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
