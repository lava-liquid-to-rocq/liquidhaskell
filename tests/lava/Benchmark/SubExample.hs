{-@ LIQUID "--lava" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}

module Benchmark.SubExample where

{- HLInt ignore -}
import Language.Haskell.Liquid.ProofCombinators

{-@ data Nats where
        Zero :: Nats
        Suc :: n:Nats -> Nats @-}
data Nats where
  Zero :: Nats
  Suc :: Nats -> Nats
  deriving (Eq)

{-@ reflect one @-}
{-@ one :: Nats @-}
one = Suc Zero

{-@ reflect two @-}
{-@ two :: Nats @-}
two = Suc one

{-@ reflect geqN @-}
{-@ geqN :: m: Nats -> n:Nats -> Bool @-}
geqN :: Nats -> Nats -> Bool
geqN _ Zero = True
geqN Zero (Suc _) = False
geqN (Suc m) (Suc n) = geqN m n

{-@ reflect sub @-}
{-@ sub :: m:Nats -> {n:Nats | geqN m n} -> {o:Nats | o != Zero <=> m != n} @-}
sub :: Nats -> Nats -> Nats
sub Zero Zero = Zero
sub (Suc m) Zero = Suc m
sub (Suc m) (Suc n) = sub m n

{-@ surprise:: {sub (Suc Zero) (Suc (Suc Zero)) = Zero} @-}
surprise :: Proof
surprise = trivial
