{-# OPTIONS_GHC -Wall #-}
module Language.Haskell.Liquid.Lava.Print (OUT (..), outPostfix) where

data OUT = ILH | ECoq | Coq | Paper
  deriving (Show)

outPostfix :: OUT -> String
outPostfix ILH = ".ilh"
outPostfix ECoq = ".ecoq"
outPostfix Coq = ".v"
outPostfix Paper = "_paper.v"
