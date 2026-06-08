{-# OPTIONS_GHC -Wall #-}

-- | GHC plugin that runs the Lava translation to Rocq. Use alongside the LH plugin:
--
--   > {-# OPTIONS_GHC -fplugin=LiquidHaskellBoot -fplugin=Lava.Plugin #-}
--
--   With @--refcore@ passed to the LH plugin, LH writes
--   the .ilh_no_elab.bin file; this plugin then parses it and runs the Rocq pipeline.
--
--   Plugin options:
--
--   > -fplugin-opt=Lava.Plugin:--equations
module Lava.Plugin (plugin) where

import Control.Monad (when)
import Control.Monad.IO.Class (liftIO)
import System.Directory (doesFileExist, getCurrentDirectory)

import GHC.Plugins (CommandLineOption, ModuleName, Plugin (..), defaultPlugin, moduleNameString, purePlugin)
import GHC.Tc.Types (TcGblEnv, TcM)
import GHC.Unit.Module.ModSummary (ModSummary (..))
import GHC.Unit.Types (moduleName)
import qualified Language.Haskell.Liquid.RefCore.Calculus as Calc
import           Language.Haskell.Liquid.RefCore.Extract (CalcMeta (..), OUT (..), getOutputFolder, outPath)

import Lava.IlhParse (parseIlh)
import Lava.Translate (runFromCalculus)

plugin :: Plugin
plugin =
  defaultPlugin
    { typeCheckResultAction = lavaHook
    , pluginRecompile       = purePlugin
    }

lavaHook :: [CommandLineOption] -> ModSummary -> TcGblEnv -> TcM TcGblEnv
lavaHook opts ms gblEnv =
  do let equations = "--equations" `elem` opts
     liftIO $ do meta <- calcMetaFor (moduleName (ms_mod ms)) (ms_hspp_file ms)
                 let binPath = outPath Bin meta
                 exists <- doesFileExist binPath
                 when exists $ do
                   putStrLn ("Lava.Plugin: consuming " ++ binPath)
                   calcSource <- parseIlh binPath
                   let hasImports = any (\d -> case d of Calc.Import _ _ -> True; _ -> False) calcSource
                       meta'      = meta { cmHasImports = hasImports }
                   _ <- runFromCalculus meta' calcSource equations
                   pure ()
     pure gblEnv

-- | Reconstruct the 'CalcMeta' that @writeIlh@ used, given just the module
--   name and the source file path, so the .ilh file can be located without
--   re-running extraction.
--
--   Note: 'cmHasImports' is set to 'False' here; it is derived from the parsed
--   .ilh contents in 'lavaHook'.
calcMetaFor :: ModuleName -> FilePath -> IO CalcMeta
calcMetaFor modName filename = do
    workingPath <- getCurrentDirectory
    let moduleId = moduleNameString modName
        modulename = moduleBaseName moduleId
        outputFolder = getOutputFolder moduleId filename workingPath
    pure (CalcMeta outputFolder modulename False)

-- | Last dotted component of a module name (e.g. @A.B.C@ -> @C@).
moduleBaseName :: String -> String
moduleBaseName name = reverse (takeWhile (/= '.') (reverse name))
