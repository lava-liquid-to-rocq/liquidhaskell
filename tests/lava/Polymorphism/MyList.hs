{-# OPTIONS_GHC -fplugin=Lava #-}

-- Simplest recursive polymorphic datatype
module MyList where

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
