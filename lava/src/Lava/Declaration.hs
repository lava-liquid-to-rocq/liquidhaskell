-- | This module contains the functions for the translation of declarations
module Lava.Declaration where

import Lava.Calculus as LH
import Lava.Coq as Coq
import Lava.Translation
import Lava.TypingEnvironment as TypEnv hiding (map)

trDecl :: LH.Decl -> Coq.Decl
trDecl (LH.Data tc alts) = undefined
trDecl (LH.Definition f tpf e isReflected) =
  let (args, ret) = arrs tpf
   in undefined

-- | Translation of an unreflected definition
trDefinition :: Id -> RefType -> [Coq.Decl]
trDefinition f tpf = undefined

{- [Coq.Definition f (map (,False) args) ret (Coq.ProofBody $ destructs ++ cleanInductions (usedIHs tacs) tacs) Coq.Transparent]
where
  argsNames = map fst $ filter ((\case Pi {} -> False; _ -> True) . argTp . snd) (argsTps tpf) -- = map fst args
  destructs = map (\x -> Coq.DestructSubsetTerm (Coq.Var x) (Coq.ConjDestrPat [Coq.SingleIdPat x, Coq.SingleIdPat $ subsetWitnessNm x])) argsNames
  (args, ret) = arrs tpf -}
