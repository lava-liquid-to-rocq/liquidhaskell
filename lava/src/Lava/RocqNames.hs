-- | Rocq-specific names used by the Lava translation.
--
--   Re-exports the shared 'Language.Haskell.Liquid.RefCore.Names' and
--   adds the name-mangling helpers that only the Rocq translation needs.
module Lava.RocqNames
  ( module Language.Haskell.Liquid.RefCore.Names
  , preamble
  , specName
  , unrefinedTCName
  , refinedConstrName
  , unrefinedConstrName
  , wfTCName
  , eqFunctionName
  , packName
  , upackName
  , projPackName
  , funToPackName
  , argListTName
  , subsetWitnessNm
  , constrWfName
  , wfLemName
  , eqReflLemName
  , eqEqbEqLemName
  , leibnitzInstanceName
  , relPostfix
  , relDefName
  , relDefThmName
  , relDefLemName
  , relDefThmName'
  , relDefRwLemName
  , exLemName
  , relDefMkLemName
  , funcHoodLemName
  , relDefBranchName
  , relBranchLemName
  , ihSpecName
  , ih
  , ihName
  , psConstrLemName
  , tcEqName
  , packDefName
  , packRelName
  , upackRelName
  , upackFunctName
  , mkUPackName
  , refProjName
  , packInstanceName
  , upackInstanceName
  , uPackWfName
  ) where

import Text.PrettyPrint.HughesPJClass
import Prelude hiding ((<>))

import Language.Haskell.Liquid.RefCore.Names

-- | Preamble for the Rocq file
preamble :: Bool -> Doc
preamble equations =
  vcat $
    [ text "From coqDeps Require Export LiquidPreludeUtil.",
      scope "Z",
      scope "Int",
      text "Set Universe Polymorphism.",
      text "From Coq Require Import Unicode.Utf8."
      -- For debugging
      -- text "Ltac solver := quicksolve."
    ]
      ++ [text "From Equations Require Import Equations." | equations]
      ++ [text "#[local] Obligation Tactic := solver." | equations]
  where
    scope x = text "Open Scope" <+> text x <> text "_scope."

{- ORMOLU_DISABLE -}

specName :: Id -> Id
specName def = def ++ "_spec"
unrefinedTCName :: Id -> Id
unrefinedTCName name = name ++ "_u"
refinedConstrName :: Id -> Id
refinedConstrName = id
unrefinedConstrName :: Id -> Id
unrefinedConstrName name = name ++ "_u"
wfTCName :: Id -> Id
wfTCName name = name ++ "_wf"
eqFunctionName :: Id -> Id
eqFunctionName name = name ++ "_rec"

packName :: Id
upackName :: Id
projPackName :: Id
funToPackName :: Id
argListTName :: Id
packName = "@Pack"
upackName = "@uPack"
projPackName = "packProj"
funToPackName = "fun_to_pack"
argListTName = "ArgListT"

subsetWitnessNm :: Id -> Id
subsetWitnessNm x = x ++ "_p"

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
