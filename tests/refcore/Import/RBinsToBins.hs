{-@ LIQUID "--refcore" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PackageImports #-}

module Import.RBinsToBins where

{- HLInt ignore -}
import Language.Haskell.Liquid.ProofCombinators
import Import.RBins

{-@ data Bin where
        Z :: Bin
        B0 :: n:Bin -> Bin
        B1 :: n:Bin ->  Bin @-}
data Bin where
  Z :: Bin
  B0 :: Bin -> Bin
  B1 :: Bin -> Bin
  deriving (Eq)

{-@ reflect rbinToBin @-}
{-@ rbinToBin :: b:RBin -> Bin @-}
rbinToBin :: RBin -> Bin
rbinToBin RZ = Z
rbinToBin (RB0 n) = B0 (rbinToBin n)
rbinToBin (RB1 n) = B1 (rbinToBin n)

{-@ reflect incAndConvert @-}
{-@ incAndConvert :: b:RBin -> Bin @-}
incAndConvert :: RBin -> Bin
incAndConvert b = rbinToBin (incRBin b)

{-@ incRBinNotZ :: b:RBin -> { incRBin b != RZ } @-}
incRBinNotZ :: RBin -> Proof
incRBinNotZ RZ = trivial
incRBinNotZ (RB0 _) = trivial
incRBinNotZ (RB1 _) = trivial

{-@ incAndConvertZ :: { incAndConvert RZ == B1 Z } @-}
incAndConvertZ :: Proof
incAndConvertZ = trivial

{-@ doubleIncAndConvertZ :: { rbinToBin (doubleIncRBin RZ) == B0 (B1 Z) } @-}
doubleIncAndConvertZ :: Proof
doubleIncAndConvertZ = trivial
