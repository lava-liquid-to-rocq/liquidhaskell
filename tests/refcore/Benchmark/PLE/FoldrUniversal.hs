{-@ LIQUID "--lava" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}

-- | Universal property of foldr a la Zombie
-- | cite : http://www.seas.upenn.edu/~sweirich/papers/congruence-extended.pdf
module Benchmark.PLE.FoldrUniversal where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (foldr)

{-@ data L where
        Emp :: L
        C :: Int -> L -> L @-}
data L where
  Emp :: L
  C :: Int -> L -> L
  deriving (Eq)

-- | foldrUniversal

{-@ axiomatize foldr @-}
{-@ foldr:: (Int -> Int -> Int) -> Int -> L -> Int @-}
foldr :: (Int -> Int -> Int) -> Int -> L -> Int
foldr f b (C x xs) = f x (foldr f b xs)
foldr f b Emp = b

{-@ axiomatize compose @-}
{-@ compose :: (Int -> Int) -> (L -> Int) -> L -> Int @-}
compose :: (Int -> Int) -> (L -> Int) -> L -> Int
compose f g x = f (g x)

{-@ foldrUniversal
      :: f:(Int -> Int -> Int)
      -> h:(L -> Int)
      -> e:Int
      -> ys:L
      -> base:{h Emp == e }
      -> step: (x:Int -> xs:L -> {h (C x xs) == f x (h xs)})
      -> { h ys == foldr f e ys }
  @-}
foldrUniversal ::
  (Int -> Int -> Int) ->
  (L -> Int) ->
  Int ->
  L ->
  Proof ->
  (Int -> L -> Proof) ->
  Proof
foldrUniversal f h e Emp base step =
  trivial
foldrUniversal f h e (C x xs) base step =
  step x xs ? foldrUniversal f h e xs base step

-- 37 SLOC

{- 
-- this needs type annotations
-- | foldrFunsion

-- This will fail as the function foldr is not fully applied
{-@ foldrFusion :: h:(Int -> Int) -> f:(Int -> Int -> Int) -> g:(Int -> Int -> Int) -> e:Int -> ys:L
            -> fuse:(x:Int -> y:Int -> {h (f x y) == g x (h y)})
            -> { h (foldr f e ys) == foldr g (h e) ys }
  @-}
foldrFusion :: (Int -> Int) -> (Int -> Int -> Int) -> (Int -> Int -> Int) -> Int -> L
             -> (Int -> Int -> Proof)
             -> Proof
foldrFusion h f g e ys fuse
  = foldrUniversal g (compose h (foldr f e)) (h e) ys
       (fuse_base h f e)
       (fuse_step h f e g fuse)

-- This will fail as the function foldr is not fully applied
fuse_step :: (Int -> Int) -> (Int -> Int -> Int) -> Int -> (Int -> Int -> Int)
         -> (Int -> Int -> Proof)
         -> Int -> L -> Proof
{-@ fuse_step :: h:(Int -> Int) -> f:(Int -> Int -> Int) -> e:Int -> g:(Int -> Int -> Int)
         -> thm:(x:Int -> y:Int -> { h (f x y) == g x (h y)})
         -> x:Int -> xs:L
         -> {h ((foldr f e) (C x xs)) == g x ((compose h (foldr f e)) (xs))}
  @-}
fuse_step h f e g thm x Emp
  = thm x e

fuse_step h f e g thm x (C y ys)
  = thm x (f y (foldr f e ys))

-- This will fail as the function foldr is not fully applied
fuse_base :: (Int->Int) -> (Int -> Int -> Int) -> Int -> Proof
{-@ fuse_base :: h:(Int->Int) -> f:(Int -> Int -> Int) -> e:Int
              -> { h (foldr f e Emp) == h e } @-}
fuse_base h f e
  = trivial

-- 61 SLOC
-}