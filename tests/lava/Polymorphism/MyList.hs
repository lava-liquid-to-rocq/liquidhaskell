{-@ LIQUID "--lava" @-}

-- Simplest recursive polymorphic datatype
module MyList where

import GHC.Types
{-@ embed GHC.Types.Int as Int @-}

import Prelude hiding (length)

{-@ data MyList a = Nil | Cons a (MyList a) @-}
data MyList a = Nil | Cons a (MyList a)

{-@ unsorted :: MyList {v:Int | v != 0} @-}
unsorted :: MyList Int
unsorted = Cons 2 (Cons (-7) (Cons 5 (Cons (-3) Nil)))

{-@ length :: MyList a -> {v:Int | v >= 0} @-}
length :: MyList a -> Int
length Nil = 0
length (Cons x xs') = 1 + length xs'
