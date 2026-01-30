{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
{-# OPTIONS_GHC -fplugin=Lava #-}

module Todo.Lambdas where

import GHC.Exts

{-@ embed GHC.Exts.Int as Int @-}
{-@ embed GHC.Exts.Bool as bool @-}
{-@ embed GHC.Exts.Int# as Int @-}
{-@ assume GHC.Exts.I# :: x:Int# -> {v: Int | v = (x :: int) } @-}
{-@ embed GHC.Exts.Addr# as Str @-}
{-@ embed GHC.Exts.Word64# as Int @-}
{-@ assume (+)  :: x:_ -> y:_ -> {v:_ | x + y  = v} @-}
{-@ assume (-)  :: x:_ -> y:_ -> {v:_ | x - y  = v} @-}
{-@ assume (<)  :: x:_ -> y:_ -> {v:_ | x < y  = v} @-}
{-@ assume (==)  :: x:_ -> y:_ -> {v:_ | (x = y)  = v} @-}

-- import Language.Haskell.Liquid.ProofCombinators

-- {-@ reflect appId @-}
{-@ appId :: x:Int -> Int @-}
appId :: Int -> Int
appId x =
  let f :: Int -> Int
      f y = y
   in f x

{-@ fvInLambda :: x:Int -> Int @-}
fvInLambda :: Int -> Int
fvInLambda x = let f y = x + y in f x
