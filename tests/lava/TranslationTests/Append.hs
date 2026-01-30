{-@ LIQUID "--lava" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-# LANGUAGE FlexibleContexts #-}

module TranslationTests.Append where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (concatMap, map)

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

{- {-@ reflect concatt @-}
concatt :: L (L) -> L
concatt Emp = Emp
concatt (App x xs) = append x (concatt xs) -}

prop_append_neutral :: L -> Proof
{-@ prop_append_neutral :: xs:L -> {append xs Emp == xs}  @-}
prop_append_neutral Emp = trivial
prop_append_neutral (App _ xs) = prop_append_neutral xs

{-@ prop_assoc :: xs:L -> ys:L -> zs:L
               -> {append (append xs ys) zs == append xs (append ys zs) } @-}
prop_assoc :: L -> L -> L -> Proof
prop_assoc Emp _ _ = trivial
prop_assoc (App x xs) ys zs = prop_assoc xs ys zs

{-@ prop_map_append ::  f:(Int -> Int) -> xs:L -> ys:L
                    -> {map f (append xs ys) == append (map f xs) (map f ys) }
  @-}
prop_map_append :: (Int -> Int) -> L -> L -> Proof
prop_map_append f Emp ys = trivial
prop_map_append f (App _ xs) ys = prop_map_append f xs ys

{- {-@ prop_concatMap :: f:(Int -> L (L)) -> xs:L
                   -> { concatt (map f xs) == concatMap f xs }
  @-}

prop_concatMap :: (Int -> L (L)) -> L -> Proof
prop_concatMap _ Emp = trivial
prop_concatMap f (App x xs) = prop_concatMap f xs -}

{-@ data L where
        Emp :: L
        App :: Int -> L -> L @-}
data L where
  Emp :: L
  App :: Int -> L -> L
  deriving (Eq)

-- 37 SLOC

