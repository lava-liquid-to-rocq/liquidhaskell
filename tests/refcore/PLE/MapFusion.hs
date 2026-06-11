{-# LANGUAGE FlexibleContexts #-}
{-@ LIQUID "--refcore" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-# LANGUAGE IncoherentInstances #-}

module PLE.MapFusion where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (map)

{-@ reflect compose @-}
{-@ compose :: (Int -> Int) -> (Int -> Int) -> Int -> Int @-}
compose :: (Int -> Int) -> (Int -> Int) -> Int -> Int
compose f g x = f (g x)

{-@ reflect map @-}
{-@ map :: (Int -> Int) -> L -> L @-}
map :: (Int -> Int) -> L -> L
map f N = N
map f (C x xs) = f x `C` map f xs

{-@ map_fusion :: f:(Int -> Int) -> g:(Int -> Int) -> xs:L
      -> {map (compose f g) xs == compose (map f) (map g) xs } @-}
map_fusion :: (Int -> Int) -> (Int -> Int) -> L -> Proof
map_fusion _ _ N = trivial
map_fusion f g (C x xs) = map_fusion f g xs

{-@ data L where
	N :: L
	C :: head:Int -> tail:L -> L @-}
data L where
  N :: L
  C :: Int -> L -> L

{-@ reflect llen @-}
{-@ llen :: L -> {v:Int | v >= 0} @-}
llen :: L -> Int
llen N = 0
llen (C _ xs) = 1 + llen xs
