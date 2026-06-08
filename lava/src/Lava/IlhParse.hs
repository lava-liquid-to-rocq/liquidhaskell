{-# OPTIONS_GHC -Wall #-}

-- | Load Calculus declarations back from binary written by
--   'Language.Haskell.Liquid.RefCore.Extract.writeIlhBin'. The wire format is
--   'Data.Binary' on the derived 'Generic' representations of 'Calc.Decl'.
module Lava.IlhParse (parseIlh) where

import qualified Data.Binary as Bin
import System.Directory (doesFileExist)

import qualified Language.Haskell.Liquid.RefCore.Calculus as Calc

-- | Load Calculus from the binary .ilhb file at the given path.
parseIlh :: FilePath -> IO [Calc.Decl]
parseIlh path = do
    exists <- doesFileExist path
    if exists
        then readIlhBin path
        else error ("Lava.IlhParse.parseIlh: file not found: " ++ path)

-- | Load Calculus declarations from a binary file written by
--   'Language.Haskell.Liquid.RefCore.Extract.writeIlhBin'.
readIlhBin :: FilePath -> IO [Calc.Decl]
readIlhBin = Bin.decodeFile
