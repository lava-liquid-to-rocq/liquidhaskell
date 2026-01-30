{-@ LIQUID "--lava" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}

module Todo.Lambdas where

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
