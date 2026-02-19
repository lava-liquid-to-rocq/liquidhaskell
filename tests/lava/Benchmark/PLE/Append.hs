{-@ LIQUID "--lava" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-# LANGUAGE FlexibleContexts #-}

module Benchmark.PLE.Append where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (concatMap, map, reverse, zip, length, flip, zipWith, unzip, take)

{-@ data L where
        Emp :: L
        App :: Int -> L -> L @-}
data L where
  Emp :: L
  App :: Int -> L -> L
  deriving (Eq)

{-@ reflect append @-}
{-@ append :: L -> L -> L @-}
append :: L -> L -> L
append Emp ys = ys
append (App x xs) ys = App x (append xs ys)

{-@ reflect map @-}
{-@ map :: (Int -> Int) -> L -> L @-}
map :: (Int -> Int) -> L -> L
map f Emp = Emp
map f (App x xs) = App (f x) (map f xs)

{-@ reflect concatMap @-}
{-@ concatMap :: (Int -> L) -> L -> L @-}
concatMap :: (Int -> L) -> L -> L
concatMap f Emp = Emp
concatMap f (App x xs) = append (f x) (concatMap f xs)

{-@ app_inj:: x:Int -> y:Int -> xs: L -> ys:L -> p:{App x xs=App y ys} -> {x = y && xs = ys} @-}
app_inj :: Int -> Int -> L -> L -> Proof -> Proof
app_inj x y xs ys p = trivial

{-@ reflect reverse @-}
{-@ reverse :: l:L -> L @-}
reverse:: L -> L
reverse Emp = Emp
reverse (App x xs) = append (reverse xs) (App x Emp)

{-@ append_nonempty_ys:: xs: L -> ys:L -> p:{append xs ys = Emp} -> {ys = Emp} @-}
append_nonempty_ys:: L -> L -> Proof -> Proof
append_nonempty_ys Emp Emp _ = trivial
append_nonempty_ys _ _ p = p

{-@ append_nonempty_xs:: xs: L -> ys:L -> p:{append xs ys = Emp} -> {xs = Emp} @-}
append_nonempty_xs:: L -> L -> Proof -> Proof
append_nonempty_xs Emp Emp _ = trivial
append_nonempty_xs _ _ p = p

{-@ reverse_nonempty:: l:L -> p:{reverse l = Emp} -> {l = Emp}@-}
reverse_nonempty:: L -> Proof -> Proof
reverse_nonempty Emp _ = trivial
reverse_nonempty (App x xs) p = append_nonempty_ys (reverse xs) (App x Emp) p

-- 42 LoC

{-@ data Pair where
        MkPair :: Int -> Int -> Pair @-}
data Pair where
  MkPair :: Int -> Int -> Pair
  deriving (Eq)

{-@ data L2 where
        Emp2 :: L2
        App2 :: Pair -> L2 -> L2 @-}
data L2 where
  Emp2 :: L2
  App2 :: Pair -> L2 -> L2
  deriving (Eq)

{-@ reflect zip @-}
{-@ zip:: L -> L -> L2 @-}
zip::L -> L -> L2
zip Emp _ = Emp2
zip _ Emp = Emp2
zip (App x xs) (App y ys) = App2 (MkPair x y) (zip xs ys)

{-@ reflect zipWith @-}
{-@ zipWith:: f:(Int->Int->Int) -> l:L -> m:L -> L @-}
zipWith:: (Int->Int->Int) -> L -> L -> L
zipWith f Emp _ = Emp
zipWith f _ Emp = Emp
zipWith f (App x xs) (App y ys) = App (f x y) (zipWith f xs ys)

{-@ reflect flip @-}
{-@ flip:: f:(Int->Int->Int) -> x:Int -> y:Int -> Int @-}
flip:: (Int->Int->Int)->Int->Int->Int
flip f x y = f y x

-- 70 LoC

{-@ data PairL where
        MkPairL:: L -> L -> PairL @-}
data PairL where
  MkPairL:: L -> L -> PairL
  deriving (Eq)

{-@ unzip::l:L2 -> PairL @-}
unzip::L2->PairL
unzip Emp2 = MkPairL Emp Emp
unzip (App2 (MkPair x y) l) = 
  let tl = unzip l in
  case tl of
    MkPairL xs ys -> MkPairL (App x xs) (App y ys)

-- 83 Loc

{-@ data Nats where
        Zero :: Nats
        Suc :: n:Nats -> Nats @-}
data Nats where
  Zero :: Nats
  Suc :: Nats -> Nats
  deriving (Eq)

{-@ reflect length @-}
{-@ length:: l:L -> Nats @-}
length::L->Nats
length Emp = Zero
length (App _ xs) = Suc (length xs)

{-@ reflect length2 @-}
{-@ length2:: l:L2 -> Nats @-}
length2::L2->Nats
length2 Emp2 = Zero
length2 (App2 _ xs) = Suc (length2 xs)

-- 99 LoC

{-@ length_map:: f:(Int -> Int) -> l:L -> {length (map f l) = length l} @-}
length_map :: (Int -> Int) -> L -> Proof
length_map f Emp = trivial
length_map f (App x xs) = length_map f xs -- length (App (f x) (map f xs)) = Suc (length (map f xs)), length (App x xs) = Suc (length xs)

{-@ length_zip:: n:Nats -> l:{l:L | length l = n} -> m:{m:L | length m = n} -> {length2 (zip l m) = n} @-}
length_zip:: Nats -> L -> L -> Proof
length_zip Zero Emp Emp = trivial
length_zip (Suc n) (App x xs) (App y ys) = length_zip n xs ys

{-@ length_zipWith:: n:Nats -> f:(Int->Int->Int) -> l:{l:L | length l = n} -> m:{m:L | length m = n} -> {length2 (zip l m) = n} @-}
length_zipWith:: Nats -> (Int->Int->Int) -> L -> L -> Proof
length_zipWith Zero f Emp Emp = trivial
length_zipWith (Suc n) f (App x xs) (App y ys) = length_zipWith n f xs ys

{-@ reflect l2_pr1 @-}
{-@ l2_pr1:: l:L2 -> L @-}
l2_pr1::L2->L
l2_pr1 Emp2 = Emp
l2_pr1 (App2 (MkPair x _) l) = App x (l2_pr1 l)

{-@ reflect l2_pr2 @-}
{-@ l2_pr2:: l:L2 -> L @-}
l2_pr2::L2->L
l2_pr2 Emp2 = Emp
l2_pr2 (App2 (MkPair _ y) l) = App y (l2_pr2 l)

{-@ length_unzip_1:: l:L2 -> {length2 l = length (l2_pr1 l)} @-}
length_unzip_1:: L2 -> Proof
length_unzip_1 Emp2 = trivial
length_unzip_1 (App2 _ l) = length_unzip_1 l

{-@ length_unzip_2:: l:L2 -> {length2 l = length (l2_pr2 l)} @-}
length_unzip_2:: L2 -> Proof
length_unzip_2 Emp2 = trivial
length_unzip_2 (App2 _ l) = length_unzip_2 l

-- 127 LoC

{-@ reflect take @-}
{-@ take:: n:Nats -> l:L -> L @-}
take:: Nats -> L -> L
take Zero _ = Emp
take _ Emp = Emp
take (Suc n) (App x xs) = App x (take n xs)

{-@ reflect geqN @-}
{-@ geqN :: m: Nats -> n:Nats -> Bool @-}
geqN :: Nats -> Nats -> Bool
geqN _ Zero = True
geqN Zero (Suc _) = False
geqN (Suc m) (Suc n) = geqN m n

{-@ take_all:: n:Nats -> l:{l:L | geqN n (length l)} -> {take n l = l} @-}
take_all:: Nats -> L -> Proof
take_all Zero Emp = trivial
take_all (Suc n) Emp = trivial
take_all (Suc n) (App x xs) = take_all n xs

{-@ zip_take:: l:L -> m:L -> {zip l m = zip (take (length m) l) (take (length l) m)} @-}
zip_take:: L -> L -> Proof
zip_take Emp _ = trivial
zip_take _ Emp = trivial
zip_take (App x xs) (App y ys) = zip_take xs ys

-- 149 LoC


{-
{-@ take_length:: n:Nats -> l:{l:L | length l = n} -> {take n l = l} @-}
take_length:: Nats -> L -> Proof
take_length Zero Emp = trivial
take_length (Suc n) (App x xs) = take_length n xs

{-@ append_inj_y:: xs:L -> xs':L -> y:Int -> y':Int -> p:{append xs (App y Emp) = append xs' (App y' Emp)} -> {y = y' && xs = xs'} @-}
append_inj_y:: L -> L -> Int -> Int -> Proof -> Proof
append_inj_y Emp Emp x y p = trivial
append_inj_y (App x xs) Emp y y' p = app_inj x y' (append xs (App y Emp)) Emp p
append_inj_y Emp (App x xs) y y' p = app_inj y x Emp (append xs (App y' Emp)) p
append_inj_y (App x xs) (App x' xs') y y' p = append_inj_y xs xs' y y' p

{-@ append_inj_y1:: xs:L -> xs':L -> y:Int -> y':Int -> p:{append xs (App y Emp) = append xs' (App y' Emp)} -> {y = y'} @-}
append_inj_y1:: L -> L -> Int -> Int -> Proof -> Proof
append_inj_y1 xs xs' y y' p = append_inj_y xs xs' y y' p

{-@ append_inj_y2:: xs:L -> xs':L -> y:Int -> y':Int -> p:{append xs (App y Emp) = append xs' (App y' Emp)} -> {xs = xs'} @-}
append_inj_y2:: L -> L -> Int -> Int -> Proof -> Proof
append_inj_y2 xs xs' y y' p = append_inj_y xs xs' y y' p-}

{-{-@ reverse_injective:: l:L -> m:L -> p:{reverse l = reverse m} -> {l = m} @-}
reverse_injective:: L -> L -> Proof -> Proof
reverse_injective Emp Emp p = trivial
reverse_injective Emp (App y ys) p = reverse_nonempty (App y ys) p
reverse_injective (App x xs) Emp p = reverse_nonempty (App x xs) p
reverse_injective (App x xs) (App y ys) p = append_inj_y1 (reverse xs) (reverse ys) x y p ? reverse_injective xs ys (append_inj_y2 (reverse xs) (reverse ys) x y p)-}