{-@ LIQUID "--refcore" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}

module Benchmark.PLE.MonadId where

{- HLInt ignore -}
import Language.Haskell.Liquid.ProofCombinators
import Prelude

-- | Monad Laws :
-- | Left identity:   return a >>= f  ≡ f a
-- | Right identity:   m >>= return    ≡ m

{-@ data Identity where
        Val :: n:Int -> Identity @-}
data Identity where
  Val :: Int -> Identity
  deriving (Eq)

{-@ reflect retrn @-}
{-@ retrn:: v:Int -> Identity @-}
retrn :: Int -> Identity
retrn v = Val v

-- compose corresponds to the >>= infix in Haskell's Monads
-- forall a b. m a -> (a -> m b) -> m b
{-@ reflect compose @-}
{-@ compose:: vx:Identity -> f:(x:Int -> Identity) -> Identity @-}
compose :: Identity -> (Int -> Identity) -> Identity
compose (Val x) f = f x

{-@ rightIdentity :: x:Identity -> { compose x retrn = x } @-}
rightIdentity :: Identity -> Proof
rightIdentity (Val x) = trivial

{-@ leftIdentity :: x:Int -> f:(Int -> Identity) -> { compose (retrn x) f = f x } @-}
leftIdentity :: Int -> (Int -> Identity) -> Proof
leftIdentity x f = trivial

{- unsupported due to the lambda in the refinement
{-@ associativity :: x:Identity -> f:(Int -> Identity) -> g:(Int -> Identity)
                  -> { compose (compose x f) g = compose x (\r:Int -> compose (f r) g) } @-}
associativity :: Identity -> (Int -> Identity) -> (Int -> Identity) -> Proof
associativity (Val x) f g = trivial
-}
