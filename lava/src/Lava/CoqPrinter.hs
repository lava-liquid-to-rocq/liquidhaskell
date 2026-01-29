{-# LANGUAGE DeriveDataTypeable #-}

module Lava.CoqPrinter
  ( Decl (),
    printCoqDecl,
  )
where

import Lava.Coq
import Lava.CoqUtil
import Lava.Util
import Prelude

-- | Used to represent a Coq Declaration
data Decl = Decl String deriving (Eq)

instance Show Decl where
  show (Decl d) = d

-- | print a 'CoqDecl' to essentially a string
printCoqDecl :: [CoqDecl] -> CoqDecl -> [Decl]
printCoqDecl decls decl = {- trace ("transCoqDecl ... "++show decl) $ -} case decl of
  TCDecl tc constrs -> concatMap (printCoqDecl decls) (transRefTC decls tc constrs)
  other -> singleton . Decl $ show other

{-
-- | Create a spec definition and a definition for the declaration with given spec and tactics (as body)
mkExtendedDecl :: [CoqDecl] -> Id -> [Arg] -> CoqType -> [CoqTactic] -> [CoqDecl]
mkExtendedDecl decls f args ret tacs = [specDecl, defDecl]
  where
    specDecl = Definition (specDeclName f) [] (baseKind TypeKind) (ProofBody specDefT) Transparent
    defDecl = Definition f [] (baseKind . SpecDef $ specDeclName f) (ProofBody defDeclTacs) Transparent

    -- \| this way the system can fill proof holes in ret
    specDefT = [RefineT $ mkFuncType args ret]
    defDeclTacs = introsVars (map fst args) : tacs
-}

