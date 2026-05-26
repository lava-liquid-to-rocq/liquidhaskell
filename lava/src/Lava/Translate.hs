{-# OPTIONS_GHC -Wall #-}

-- | The Calculus to Rocq Lava pipeline. Consumes Calculus
--   declarations that were produced upstream.
module Lava.Translate
  ( runFromCalculus
  , CalcMeta (..)
  ) where

import Data.List (partition)
import qualified Text.PrettyPrint.HughesPJClass as PP

import qualified Language.Haskell.Liquid.Lava.Calculus as Calc
import           Language.Haskell.Liquid.Lava.Extract (CalcMeta (..), writeOut)
import           Language.Haskell.Liquid.Lava.Names (OUT (..), preamble)

import qualified Lava.Coq as Coq (Decl (..))
import           Lava.Declaration (trDecl)
import           Lava.Elaboration (elaborate)
import           Lava.TopologicalSort (topologicalSort)

-- | Sort, elaborate, translate to Rocq, write outputs.
--   The boolean selects the Equations preamble.
runFromCalculus :: CalcMeta -> [Calc.Decl] -> Bool -> IO [Coq.Decl]
runFromCalculus meta calcSource equations =
    case elaborate (sortDecls calcSource) of
        Left err -> putStrLn (PP.prettyShow err) >> pure []
        Right calcSourceElaborated ->
            do putStrLn "––Typechecking and elaboration OK––"
               writeOut outputFolder modulename ILH PP.empty calcSourceElaborated
               let coqPreamble = if cmHasImports meta then PP.empty else preamble equations
                   coqResult = concatMap (trDecl equations) calcSourceElaborated
               writeOut outputFolder modulename Rocq coqPreamble coqResult
               pure coqResult
  where
    outputFolder = cmOutputFolder meta
    modulename = cmModuleName meta

-- | Topologically sort declarations, keeping Import decls at the front in
--   their original order.
sortDecls :: [Calc.Decl] -> [Calc.Decl]
sortDecls ds = imports ++ topologicalSort rest where
    (imports, rest) = partition isImport ds
    isImport (Calc.Import _ _) = True
    isImport _                 = False
