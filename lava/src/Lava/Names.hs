-- | Collection of names and strings used in the translation
module Lava.Names where

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

-- | Preamble for the Rocq file
preamble :: Doc
preamble =
  vcat [text "From coqDeps Require Export LiquidPreludeUtil.", scope "Z", scope "Int"]
  where
    scope x = text "Open Scope" <+> text x <> text "_scope."

{- ORMOLU_DISABLE -}

constrWfName :: Id -> Id -> Id
wfLemName :: Id -> Id
eqReflLemName :: Id -> Id
eqEqbEqLemName :: Id -> Id
leibnitzInstanceName :: Id -> Id
constrWfName c x = "wf_" ++ c ++ "_" ++ x
wfLemName tp = tp ++ "_wf_ref"
eqReflLemName tp = tp ++ "_eq_refl"
eqEqbEqLemName tp = tp ++ "_eqb_eq"
leibnitzInstanceName tc = "leibnitz_eq_" ++ tc

relPostfix :: Id
relDefName :: Id -> Id
relDefThmName :: Id -> Id
relDefLemName :: Id -> Id
relDefThmName' :: Id -> Id
relDefRwLemName :: Id -> Id
exLemName :: Id -> Id
relDefMkLemName :: Id -> Id
funcHoodLemName :: Id -> Id
relDefBranchName :: Id -> Id
relBranchLemName :: Id -> Id
relPostfix = "_rel"
relDefName name = name ++ relPostfix
relDefThmName name = name ++ "__" ++ relDefName name
relDefLemName name = relDefThmName name ++ "'"
relDefThmName' name = relDefThmName name ++ "'"
relDefRwLemName name = name ++ "__" ++ relDefName name ++ "_rw"
exLemName name = name ++ relPostfix ++ "_ex"
relDefMkLemName name = relDefName name ++ "_mk"
funcHoodLemName name = relDefName name ++ "_funct"
relDefBranchName name = name ++ "_def"
relBranchLemName name = name ++ "_lem"

ihSpecName :: Id -> Id -> Id
ihSpecName ihNm x =
  if any (`elem` x) "- "
    -- \| x contains an illegal character, so we take the hash instead
    then ihNm ++ "_" ++ hashName x
    else ihNm ++ "_" ++ x

ih :: [Id] -> Id
ih = foldl ihSpecName "IH"

ihName :: Id -> Id
ihName ihVar = ih [ihVar]

-- ** names used internally for translation of TCs to Coq

psConstrLemName :: Id -> Id
psConstrLemName c = c ++ "_lem"
tcEqName :: Id -> Id
tcEqName tc = tc ++ "_eq"

packDefName :: Id
packRelName :: Id
upackRelName :: Id
upackFunctName :: Id
mkUPackName :: Id
refProjName :: Id
packInstanceName :: Id -> Id
upackInstanceName :: Id -> Id
uPackWfName :: Id
packDefName = "f_def"
packRelName = "f_rel"
upackRelName = "rel_u"
upackFunctName = "funct_u"
mkUPackName = "mkUPack"
refProjName = "refinement_proj"
packInstanceName f = f ++ "_pack"
upackInstanceName f = f ++ "_upack"
uPackWfName = "uPack_wf"

{- ORMOLU_ENABLE -}
