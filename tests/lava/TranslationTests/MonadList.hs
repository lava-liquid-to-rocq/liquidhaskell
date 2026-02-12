{-@ LIQUID "--lava" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}

module TranslationTests.MonadList where

{- HLInt ignore -}
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (return)

-- | Monad Laws :
-- | Left identity:   retrn a >>= f  ≡ f a
-- | Right identity:   m >>= retrn    ≡ m

{-@ data L where
        Emp :: L
        C :: Int -> L -> L @-}
data L where
  Emp :: L
  C :: Int -> L -> L
  deriving (Eq)

{-@ reflect retrn @-}
{-@ retrn :: Int -> L @-}
retrn :: Int -> L
retrn x = C x Emp

{-@ reflect bind @-}
{-@ bind :: L -> (Int -> L) -> L @-}
bind :: L -> (Int -> L) -> L
bind Emp f = Emp
bind (C x xs) f = append (f x) (bind xs f)

{-@ reflect append @-}
{-@ append :: L -> L -> L @-}
append :: L -> L -> L
append Emp ys = ys
append (C x xs) ys = C x (append xs ys)

-- | Left Identity

{-@ left_identity :: x:Int -> f:(Int -> L) -> { bind (retrn x) f == f x } @-}
left_identity :: Int -> (Int -> L) -> Proof
left_identity x f =
  prop_append_neutral (f x)

-- | Right Identity

{-@ right_identity :: x:L -> { bind x retrn == x } @-}
right_identity :: L -> Proof
right_identity Emp =
  trivial
right_identity (C x xs) =
  right_identity xs

prop_append_neutral :: L -> Proof
{-@ prop_append_neutral :: xs:L -> { append xs Emp == xs }  @-}
prop_append_neutral Emp =
  trivial
prop_append_neutral (C x xs) =
  prop_append_neutral xs

{- unsupported due to the lambda in the refinement
{-@ associativity :: x:L -> f:(Int -> L) -> g:(Int -> L)
                  -> { compose (compose x f) g = compose x (\r:Int -> compose (f r) g) } @-}
associativity :: L -> (Int -> L) -> (Int -> L) -> Proof
associativity Emp f g = trivial
associativity (C x xs) f g
  =   bind_append (f x) (bind xs f) g ? associativity xs f g
-}

-- 37 SLOC

