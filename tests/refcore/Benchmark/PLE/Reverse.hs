{-@ LIQUID "--refcore" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-# LANGUAGE FlexibleContexts #-}

module Benchmark.PLE.Reverse where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (concat, reverse)

{-@ data L where
        Emp :: L
        App :: Int -> L -> L @-}
data L where
  Emp :: L
  App :: Int -> L -> L
  deriving (Eq)

{-@ reflect concat @-}
{-@ concat:: l:L -> m:L -> L @-}
concat :: L -> L -> L
concat Emp m = m
concat (App x xs) m = App x (concat xs m)

{-@ app_inj:: x:Int -> y:Int -> xs: L -> ys:L -> p:{App x xs=App y ys} -> {x = y && xs = ys} @-}
app_inj :: Int -> Int -> L -> L -> Proof -> Proof
app_inj x y xs ys p = trivial

{-@ concat_nonempty_ys:: xs: L -> ys:L -> p:{concat xs ys = Emp} -> {ys = Emp} @-}
concat_nonempty_ys :: L -> L -> Proof -> Proof
concat_nonempty_ys Emp Emp _ = trivial
concat_nonempty_ys _ _ p = p

{-@ concat_nonempty_xs:: xs: L -> ys:L -> p:{concat xs ys = Emp} -> {xs = Emp} @-}
concat_nonempty_xs :: L -> L -> Proof -> Proof
concat_nonempty_xs Emp Emp _ = trivial
concat_nonempty_xs _ _ p = p

{-@ concat_inj_y:: xs:L -> xs':L -> y:Int -> y':Int -> p:{concat xs (App y Emp) = concat xs' (App y' Emp)} -> {y = y' && xs = xs'} @-}
concat_inj_y :: L -> L -> Int -> Int -> Proof -> Proof
concat_inj_y Emp Emp y y' p = trivial
concat_inj_y (App x xs) Emp y y' p = app_inj x y' (concat xs (App y Emp)) Emp p
concat_inj_y Emp (App x xs) y y' p = app_inj y x Emp (concat xs (App y' Emp)) p
concat_inj_y (App x xs) (App x' xs') y y' p = concat_inj_y xs xs' y y' p

{-@ concat_inj_y1:: xs:L -> xs':L -> y:Int -> y':Int -> p:{concat xs (App y Emp) = concat xs' (App y' Emp)} -> {y = y'} @-}
concat_inj_y1 :: L -> L -> Int -> Int -> Proof -> Proof
concat_inj_y1 xs xs' y y' p = concat_inj_y xs xs' y y' p

{-@ concat_inj_y2:: xs:L -> xs':L -> y:Int -> y':Int -> p:{concat xs (App y Emp) = concat xs' (App y' Emp)} -> {xs = xs'} @-}
concat_inj_y2 :: L -> L -> Int -> Int -> Proof -> Proof
concat_inj_y2 xs xs' y y' p = concat_inj_y xs xs' y y' p

{-@ reflect reverse @-}
{-@ reverse :: l:L -> L @-}
reverse :: L -> L
reverse Emp = Emp
reverse (App x xs) = concat (reverse xs) (App x Emp)

{-@ reverse_nonempty:: l:L -> p:{reverse l = Emp} -> {l = Emp}@-}
reverse_nonempty :: L -> Proof -> Proof
reverse_nonempty Emp _ = trivial
reverse_nonempty (App x xs) p = concat_nonempty_ys (reverse xs) (App x Emp) p

{-@ reverse_injective:: l:L -> m:L -> p:{reverse l = reverse m} -> {l = m} @-}
reverse_injective :: L -> L -> Proof -> Proof
reverse_injective Emp Emp p = trivial
reverse_injective Emp (App y ys) p = reverse_nonempty (App y ys) p
reverse_injective (App x xs) Emp p = reverse_nonempty (App x xs) p
reverse_injective (App x xs) (App y ys) p = concat_inj_y1 (reverse xs) (reverse ys) x y p ? reverse_injective xs ys (concat_inj_y2 (reverse xs) (reverse ys) x y p)

-- 60 LoC (combined with Append)

