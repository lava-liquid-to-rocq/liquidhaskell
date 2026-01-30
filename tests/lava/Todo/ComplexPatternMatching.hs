{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
{-# OPTIONS_GHC -fplugin=Lava #-}

module Todo.ComplexPatternMatching where

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

import Language.Haskell.Liquid.ProofCombinators

{-@ data Nats where
      Zero :: Nats
      Suc :: n:Nats -> Nats @-}
data Nats where
  Zero :: Nats
  Suc :: Nats -> Nats
  deriving (Eq)

{-@ reflect idNat @-}
{-@ idNat :: x:Nats -> Nats @-}
idNat :: Nats -> Nats
idNat x = x

{-@ reflect h0 @-}
{-@ h0 :: x:Nats -> Nats @-}
h0 :: Nats -> Nats
h0 x = case x of
  Zero -> case idNat x of
    Zero -> Zero
    Suc z -> x
  Suc y -> case idNat x of
    Zero -> Suc x
    Suc z -> x

{- This version of the function h should be handled correctly by the tactics.
 - We can build the relation graph.
 - However, the functionality lemma currently fails, while it works well with
 - the version h0, apparently because we need a better induction hypothesis.
 - Also, we can't write this version of the function using Equations. -}

{-@ reflect h @-}
{-@ h :: x:Nats -> Nats @-}
h :: Nats -> Nats
h x = case idNat x of
  Zero -> case x of
    Zero -> Zero
    Suc y -> Suc x
  Suc z -> x

{-- Pattern matchings that involves a bound variable, and thus cannot be part
 - of the “with” patterns.
 - We should be able to translate it if the pattern matching is complete. -}

{- Currently, try to reduce lets, so this will just be a match on Suc x -}
{-@ reflect boundVar @-}
{-@ boundVar :: x:Nats -> Nats @-}
boundVar :: Nats -> Nats
boundVar x =
  let y = Suc x
   in case y of
        Zero -> Zero
        Suc x' -> x'

{-@ reflect apply @-}
{-@ apply :: f:(m:Nats -> Nats) -> n:Nats -> {v:Nats | v = f n} @-}
apply :: (Nats -> Nats) -> Nats -> Nats
apply f n = f n

-- Cannot be reflected because of idN being bound and used in an application
{-@ boundExp :: n:Nats -> Nats @-}
boundExp :: Nats -> Nats
boundExp n =
  let idN :: Nats -> Nats
      idN = \p -> p
   in case apply idN n of
        Zero -> Zero
        Suc n' -> Suc n'
