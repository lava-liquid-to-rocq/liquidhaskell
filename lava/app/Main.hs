{-# OPTIONS_GHC -Wall #-}

-- | The @lava@ executable for Calculus to Rocq translation. Consumes the .ilh_no_elab.bin
--   file that was written by liquidhaskell-boot's plugin (see
--   'Language.Haskell.Liquid.Lava.Extract.writeIlhBin').
--
--   Usage:
--
--   > lava [--equations] [--has-imports] [--output-folder DIR] PATH.ilh_no_elab.bin
--
--   The module name is derived from the input file's base name. The output
--   folder defaults to the input file's directory.
module Main (main) where

import Data.Maybe ( fromMaybe )
import Data.List (partition)
import System.Environment (getArgs, getProgName)
import System.Exit (exitFailure)
import System.FilePath (dropExtensions, takeDirectory, takeFileName)
import System.IO (hPutStrLn, stderr)

import Lava.IlhParse (parseIlh)
import Lava.Translate (CalcMeta (..), runFromCalculus)

data Opts = Opts
  { optEquations    :: Bool
  , optHasImports   :: Bool
  , optOutputFolder :: Maybe FilePath
  , optInputPath    :: FilePath
  }

readFlags :: [String] -> FilePath -> Either String Opts
readFlags flags path = go (Opts False False Nothing path) flags
  where
    go o []                              = Right o
    go o ("--equations"    : rest)       = go o { optEquations  = True } rest
    go o ("--has-imports"  : rest)       = go o { optHasImports = True } rest
    go o ("--output-folder": dir : rest) = go o { optOutputFolder = Just dir } rest
    go _ (unknown : _)                   = Left ("unknown flag: " ++ unknown)

parseArgs :: IO Opts
parseArgs = do
    args <- getArgs
    let (flags, positional) = partition (\a -> take 2 a == "--") args
    case positional of
        [path] -> case readFlags flags path of
            Right o  -> pure o
            Left err -> die err
        _ -> die "expected exactly one .ilh file path"

die :: String -> IO a
die msg =
  do name <- getProgName
     hPutStrLn stderr (name ++ ": " ++ msg)
     hPutStrLn stderr "usage: lava [--equations] [--has-imports] [--output-folder DIR] PATH.ilh_no_elab"
     exitFailure

run :: Opts -> IO ()
run opts = do
    calcSource <- parseIlh (optInputPath opts)
    _ <- runFromCalculus (meta opts) calcSource (optEquations opts)
    pure ()
  where
    meta o = CalcMeta
        { cmOutputFolder = fromMaybe (takeDirectory (optInputPath o)) (optOutputFolder o)
        , cmModuleName   = dropExtensions (takeFileName (optInputPath o))
        , cmHasImports   = optHasImports o
        }

main :: IO ()
main = parseArgs >>= run
