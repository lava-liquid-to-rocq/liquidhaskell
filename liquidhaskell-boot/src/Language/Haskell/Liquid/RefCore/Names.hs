-- | Collection of names and strings used in the translation
module Language.Haskell.Liquid.RefCore.Names where

import Data.Hashable (hash)
import Data.List (find)
import Data.Maybe (fromJust)
import Data.Set (Set)
import Text.PrettyPrint.HughesPJClass
import Prelude hiding ((<>))

-- | Identifiers in both LH and Rocq
type Id = String

-- | return a variable fresh wrt to a set of Id
freshVar :: Id -> Set Id -> Id
freshVar x vars =
  let start :: Integer
      start = 1
      names = x : [x ++ "_" ++ show i | i <- [start ..]]
   in fromJust $ find (`notElem` vars) names

-- | Produce an (almost certainly) unique number string for the given printable object
hashName :: (Pretty a) => a -> Id
hashName e = take 8 $ prettyShow (abs . hash $ prettyShow e)

-- * Names of the output files

-- | Internal LH not elaborated and elaborated, and Rocq
data OUT = ILHNoElab | ILH | Rocq
  deriving (Show)

outPostfix :: OUT -> String
outPostfix ILHNoElab = ".ilh_no_elab"
outPostfix ILH = ".ilh"
outPostfix Rocq = ".v"

-- * Rocq

{- ORMOLU_DISABLE -}

-- A non-exhaustive list of reserved names
rocqReservedNames :: [Id]
rocqReservedNames = [
  "Z", "bool", "Set", "Type", "Prop",
  "From", "Require", "Import", "Export", "Open", "Scope", "Z_scope", "Int_scope",
  "LiquidPreludeUtil", "Unicode",
  "Inductive", "Fixpoint", "Theorem", "Lemma", "Definition", "Hint",
  "Proof", "Qed", "Defined", "Opaque", "Transparent",
  "Resolve", "Global", "global", "Instance", "Notation", "Rewrite",
  "match", "with", "let", "in", "by", "end", "if", "then", "else"]

{- ORMOLU_ENABLE -}
