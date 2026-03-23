{-# OPTIONS_GHC -Wall #-}
module Language.Haskell.Liquid.Lava.Print (OUT (..), outPostfix) where

data OUT = ILH | ILHC | ECoq | Coq | Paper
  deriving (Show)

outPostfix :: OUT -> String
outPostfix ILH = ".ilh"
outPostfix ILHC = ".ilhc"
outPostfix ECoq = ".ecoq"
outPostfix Coq = ".v"
outPostfix Paper = "_paper.v"
