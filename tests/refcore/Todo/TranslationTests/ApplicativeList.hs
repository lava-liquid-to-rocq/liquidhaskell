{-@ LIQUID "--refcore" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
{-# LANGUAGE FlexibleContexts #-}

module Todo.TranslationTests.ApplicativeList where

{- HLInt ignore -}
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (C, L, N, fmap, id, pure, seq)

-- | Applicative Laws :
-- | identity      pure id <*> v = v
-- | composition   pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
-- | homomorphism  pure f <*> pure x = pure (f x)
-- | interchange   u <*> pure y = pure ($ y) <*> u

{-@ data L where
        N :: L
        C :: Int -> L -> L @-}
data L where
  N :: L
  C :: Int -> L -> L
  deriving (Eq)

{-@ data LF where
      NF :: LF
      CF :: n:(Int -> Int) -> LF -> LF @-}
data LF where
  NF :: LF
  CF :: (Int -> Int) -> LF -> LF

{-@ data LF1 where
      NF1::LF1
      CF1 :: n:((Int -> Int) -> Int) -> LF1 -> LF1 @-}
data LF1 where
  NF1 :: LF1
  CF1 :: ((Int -> Int) -> Int) -> LF1 -> LF1

{-@ data LF2 where
      NF2::LF2
      CF2 :: n:((Int -> Int) -> Int -> Int) -> LF2 -> LF2 @-}
data LF2 where
  NF2 :: LF2
  CF2 :: ((Int -> Int) -> Int -> Int) -> LF2 -> LF2

{-@ data LF3 where
      NF3::LF3
      CF3 :: n:((Int -> Int) -> (Int -> Int) -> Int -> Int) -> LF3 -> LF3 @-}
data LF3 where
  NF3 :: LF3
  CF3 :: ((Int -> Int) -> (Int -> Int) -> Int -> Int) -> LF3 -> LF3

{-@ reflect pure @-}
{-@ pure :: Int -> L @-}
pure :: Int -> L
pure x = C x N

{-@ reflect pureF @-}
{-@ pureF :: (Int -> Int) -> LF @-}
pureF :: (Int -> Int) -> LF
pureF f = CF f NF

{-@ reflect pureF1 @-}
{-@ pureF1 :: ((Int -> Int) -> Int) -> LF1 @-}
pureF1 :: ((Int -> Int) -> Int) -> LF1
pureF1 f = CF1 f NF1

{-@ reflect pureF3 @-}
{-@ pureF3 :: ((Int -> Int) -> (Int -> Int) -> Int -> Int) -> LF3 @-}
pureF3 :: ((Int -> Int) -> (Int -> Int) -> Int -> Int) -> LF3
pureF3 f = CF3 f NF3

{-@ reflect seq @-}
{-@ seq :: LF -> L -> L @-}
seq :: LF -> L -> L
seq (CF f fs) xs =
  append (fmap f xs) (seq fs xs)
seq _ _ = N

{-@ reflect append @-}
{-@ append :: L -> L -> L @-}
append :: L -> L -> L
append N ys =
  ys
append (C x xs) ys =
  C x (append xs ys)

{-@ reflect fmap @-}
{-@ fmap:: f:(Int->Int) -> l:L -> L @-}
fmap :: (Int -> Int) -> L -> L
fmap f N = N
fmap f (C x xs) = C (f x) (fmap f xs)

{-@ reflect seqF @-}
{-@ seqF :: LF1 -> LF -> L @-}
seqF :: LF1 -> LF -> L
seqF (CF1 f fs) xs =
  append (fmapF f xs) (seqF fs xs)
seqF _ _ = N

{-@ reflect fmapF @-}
{-@ fmapF:: f:((Int -> Int) -> Int) -> l:LF -> L @-}
fmapF :: ((Int -> Int) -> Int) -> LF -> L
fmapF f NF = N
fmapF f (CF x xs) = C (f x) (fmapF f xs)

{-@ reflect seqF1 @-}
{-@ seqF1 :: LF2 -> LF -> LF @-}
seqF1 :: LF2 -> LF -> LF
seqF1 (CF2 f fs) xs =
  appendF (fmapF2 f xs) (seqF1 fs xs)
seqF1 _ _ = NF

{-@ reflect appendF @-}
{-@ appendF :: LF -> LF -> LF @-}
appendF :: LF -> LF -> LF
appendF NF ys =
  ys
appendF (CF x xs) ys =
  CF x (appendF xs ys)

{-@ reflect fmapF2 @-}
{-@ fmapF2:: f:((Int -> Int) -> Int -> Int) -> l:LF -> LF @-}
fmapF2 :: ((Int -> Int) -> Int -> Int) -> LF -> LF
fmapF2 f NF = NF
fmapF2 f (CF x xs) = CF (f x) (fmapF2 f xs)

{-@ reflect seqF2 @-}
{-@ seqF2 :: LF3 -> LF -> LF2 @-}
seqF2 :: LF3 -> LF -> LF2
seqF2 (CF3 f fs) xs =
  appendF2 (fmapF3 f xs) (seqF2 fs xs)
seqF2 _ _ = NF2

{-@ reflect appendF2 @-}
{-@ appendF2 :: LF2 -> LF2 -> LF2 @-}
appendF2 :: LF2 -> LF2 -> LF2
appendF2 NF2 ys =
  ys
appendF2 (CF2 x xs) ys =
  CF2 x (appendF2 xs ys)

{-@ reflect fmapF3 @-}
{-@ fmapF3:: f:((Int -> Int) -> (Int -> Int) -> Int -> Int) -> l:LF -> LF2 @-}
fmapF3 :: ((Int -> Int) -> (Int -> Int) -> Int -> Int) -> LF -> LF2
fmapF3 f NF = NF2
fmapF3 f (CF x xs) = CF2 (f x) (fmapF3 f xs)

{-@ reflect id @-}
{-@ id :: Int -> Int @-}
id :: Int -> Int
id x = x

{-@ reflect idL @-}
{-@ idL :: L -> L @-}
idL :: L -> L
idL x = x

{-@ reflect idollar @-}
{-@ idollar :: Int -> (Int -> Int) -> Int @-}
idollar :: Int -> (Int -> Int) -> Int
idollar x f = f x

{-@ reflect compose @-}
{-@ compose :: (Int -> Int) -> (Int -> Int) -> Int -> Int @-}
compose :: (Int -> Int) -> (Int -> Int) -> Int -> Int
compose f g x = f (g x)

-- | L

{-@ identity :: x:L -> { seq (pureF id) x == x } @-}
identity :: L -> Proof
identity xs =
  fmap_id xs ? prop_append_neutral xs

-- | Composition

{-@ composition :: x:LF
                -> y:LF
                -> z:L
                -> { (seq (seqF1 (seqF2 (pureF3 compose) x) y) z) == seq x (seq y z) } @-}
composition :: LF -> LF -> L -> Proof
composition NF ys zs =
  seq_nillF3 (pureF3 compose)
composition (CF x xs) ys zs =
  prop_append_neutralF2 (fmapF3 compose (CF x xs))
    ? prop_append_neutralF2 (fmapF3 compose (CF x xs))
    ? seq_append (fmapF2 (compose x) ys) (seqF1 (fmapF3 compose xs) ys) zs
    ? seq_fmap x ys zs
    ? prop_append_neutralF2 (fmapF3 compose xs)
    ? composition xs ys zs

-- | homomorphism  pure f <*> pure x = pure (f x)

{-@ homomorphism :: f:(Int -> Int) -> x:Int
                 -> {  seq (pureF f) (pure x) == pure (f x) } @-}
homomorphism :: (Int -> Int) -> Int -> Proof
homomorphism f x =
  prop_append_neutral (C (f x) N)

-- | interchange
interchange :: LF -> Int -> Proof
{-@ interchange :: u:LF -> y:Int
     -> { seq u (pure y) == seqF (pureF1 (idollar y)) u }
  @-}
interchange NF y =
  seq_nillF (pureF1 (idollar y))
interchange (CF x xs) y =
  prop_append_neutral (fmapF (idollar y) (CF x xs))
    ? seq_one' (idollar y) xs
    ? interchange xs y
    ? seq_prop xs y

{-@ seq_prop :: xs:LF -> y:Int -> {seq xs (C y N) == seq xs (pure y)} @-}
seq_prop :: LF -> Int -> Proof
seq_prop _ _ = trivial

{-@ llen :: L -> Int @-}
llen :: L -> Int
llen N = 0
llen (C _ xs) = 1 + llen xs

{-@ llenF :: LF -> Int @-}
llenF :: LF -> Int
llenF NF = 0
llenF (CF _ xs) = 1 + llenF xs

-- | TODO: Currently I cannot improve proofs
-- | HERE I duplicate the code...

-- TODO: remove stuff out of HERE
{-@ seq_nillF :: fs:LF1 -> {v:Proof | seqF fs NF == N } @-}
seq_nillF :: LF1 -> Proof
seq_nillF NF1 =
  trivial
seq_nillF (CF1 x xs) =
  seq_nillF xs

{-@ seq_nillF3 :: fs:LF3 -> {v:Proof | seqF2 fs NF == NF2 } @-}
seq_nillF3 :: LF3 -> Proof
seq_nillF3 NF3 =
  trivial
seq_nillF3 (CF3 x xs) =
  seq_nillF3 xs

{-@ append_fmap :: f:(Int -> Int) -> xs:L -> ys: L
      -> {append (fmap f xs) (fmap f ys) == fmap f (append xs ys) } @-}
append_fmap :: (Int -> Int) -> L -> L -> Proof
append_fmap _ N _ = trivial
append_fmap f (C _ xs) ys = append_fmap f xs ys

seq_fmap :: (Int -> Int) -> LF -> L -> Proof
{-@ seq_fmap :: f: (Int -> Int) -> fs:LF -> xs:L
         -> { seq (fmapF2 (compose f) fs) xs == fmap f (seq fs xs) }
  @-}
seq_fmap _ NF _ = trivial
seq_fmap f (CF g gs) xs =
  seq_fmap f gs xs
    ? append_fmap f (fmap g xs) (seq gs xs)
    ? map_fusion0 f g xs

{-@ append_distr :: xs:L -> ys:L -> zs:L
      -> {v:Proof | append xs (append ys zs) == append (append xs ys) zs } @-}
append_distr :: L -> L -> L -> Proof
append_distr N _ _ = trivial
append_distr (C _ xs) ys zs = append_distr xs ys zs

{-@ seq_one' :: f:((Int -> Int) -> Int) -> xs:LF -> {fmapF f xs == seqF (pureF1 f) xs} @-}
seq_one' :: ((Int -> Int) -> Int) -> LF -> Proof
seq_one' _ NF = trivial
seq_one' f (CF _ xs) = seq_one' f xs

{-@ seq_one :: xs:LF -> {v:Proof | fmapF3 compose xs == seqF2 (pureF3 compose) xs} @-}
seq_one :: LF -> Proof
seq_one NF = trivial
seq_one (CF _ xs) = seq_one xs

{-@ seq_append :: fs1:LF -> fs2: LF -> xs: L
      -> { seq (appendF fs1 fs2) xs == append (seq fs1 xs) (seq fs2 xs) } @-}
seq_append :: LF -> LF -> L -> Proof
seq_append NF _ _ = trivial
seq_append (CF f1 fs1) fs2 xs =
  append_distr (fmap f1 xs) (seq fs1 xs) (seq fs2 xs)
    ? seq_append fs1 fs2 xs

{-@ map_fusion0 :: f:(Int -> Int) -> g:(Int -> Int) -> xs:L
      -> {v:Proof | fmap (compose f g) xs == fmap f (fmap g xs) } @-}
map_fusion0 :: (Int -> Int) -> (Int -> Int) -> L -> Proof
map_fusion0 _ _ N = trivial
map_fusion0 f g (C _ xs) = map_fusion0 f g xs

-- | FunctorList

{-@ fmap_id :: xs:L -> {v:Proof | fmap id xs == idL xs } @-}
fmap_id :: L -> Proof
fmap_id N =
  trivial
fmap_id (C x xs) =
  fmap_id xs

-- imported from Append
prop_append_neutral :: L -> Proof
{-@ prop_append_neutral :: xs:L -> {v:Proof | append xs N == xs }  @-}
prop_append_neutral N =
  trivial
prop_append_neutral (C x xs) =
  prop_append_neutral xs

prop_append_neutralF2 :: LF2 -> Proof
{-@ prop_append_neutralF2 :: xs:LF2 -> {v:Proof | appendF2 xs NF2 == xs }  @-}
prop_append_neutralF2 NF2 =
  trivial
prop_append_neutralF2 (CF2 x xs) =
  prop_append_neutralF2 xs
