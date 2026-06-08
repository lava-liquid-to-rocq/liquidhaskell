{-# OPTIONS_GHC -Wall #-}

-- | Load Calculus declarations back from binary written by
--   'Language.Haskell.Liquid.RefCore.Extract.writeIlhBin'. The wire format is
--   'Data.Binary' on the derived 'Generic' representations of 'Calc.Decl'.
module Lava.IlhParse (parseIlh) where

import Data.List (isSuffixOf)
import System.Directory (doesFileExist)

import qualified Language.Haskell.Liquid.RefCore.Calculus as Calc
import           Language.Haskell.Liquid.RefCore.Extract (readIlhBin)

-- | Load Calculus from disk. Accepts either the binary file directly or the
--   text .ilh_no_elab path, in which case the @.bin@ companion is loaded.
parseIlh :: FilePath -> IO [Calc.Decl]
parseIlh path = do
    let resolved = if ".bin" `isSuffixOf` path then path else path ++ ".bin"
    exists <- doesFileExist resolved
    if exists
        then readIlhBin resolved
        else error ("Lava.IlhParse.parseIlh: file not found: " ++ resolved)
