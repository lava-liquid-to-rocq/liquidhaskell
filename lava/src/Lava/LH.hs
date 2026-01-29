{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Lava.LH
  ( -- * type aliases for intermediate data during LH/GHC -> ILH parsing
    Lemma,
    Def,

    -- * Dependencies and Binder classes and instances
    Dependencies (..),
    Binder (..),
    topologicalSort,
  )
where

import Data.Graph
import Lava.InternalLH (ArrType (..), LHDecl (..), LHSimpleTerm (..), LHTerm (..), LHType (Buildin, TDat), RefType (..))
import qualified Lava.InternalLH as ILH
import Lava.Util
import Prelude

-- * type aliases for intermediate data during LH/GHC -> ILH parsing

type Lemma = (Def, ArrType, Bool)

type Def = (Id, [Id], LHTerm, Bool)

-- * 'Dependencies' class and instances, 'Binder class' and instance for 'LHDecl'

class Dependencies a where
  dependsOn :: a -> Id -> Bool

instance Dependencies LHType where
  dependsOn (TDat typ) name = typ == name
  dependsOn (Buildin _) _ = False
  dependsOn (ILH.Pi (x, dom) codom) name = (dom `dependsOn` name || codom `dependsOn` name) && x /= name

instance Dependencies LHSimpleTerm where
  dependsOn (Neg p) name = dependsOn p name
  dependsOn (Bop _ s t) name = dependsOn s name || dependsOn t name
  dependsOn (App f ts) name = dependsOn f name || any (`dependsOn` name) ts
  dependsOn (Var n) name = n == name
  dependsOn _ _ = False

dependsBranch :: (Id, [Id], LHTerm) -> Id -> Bool

-- | if a variable bound in the match name-clashes with 'name', then that nameclash ensures the branch cannot depend on 'name'
-- Todo: what happens if 'name' is a constructor
dependsBranch (c, ts, e) name = (c == name || e `dependsOn` name) && name `notElem` ts

-- \|| any (\c -> c == name && isUpper (head c)) ts

instance Dependencies LHTerm where
  dependsOn (BasicTerm t) name = t `dependsOn` name
  dependsOn (Annot t rt) name = t `dependsOn` name || rt `dependsOn` name
  dependsOn (Case x branches _) name = any (`dependsBranch` name) branches || x `dependsOn` name
  dependsOn (Let x df tm) name = (df `dependsOn` name || tm `dependsOn` name) && x /= name
  dependsOn (Lambda x bdy) name = bdy `dependsOn` name && name /= x
  dependsOn Undefined _ = False
  dependsOn (SEqn s t z) name = s `dependsOn` name || z `dependsOn` name || t `dependsOn` name
  dependsOn (QMark z expr) name = expr `dependsOn` name || z `dependsOn` name

instance Dependencies RefType where
  dependsOn (RefType _ t reft) name = dependsOn t name || dependsOn reft name

instance Dependencies ArrType where
  dependsOn (ArrType args ret) name = any (`dependsOn` name) args || dependsOn ret name

instance Dependencies (Id, RefType) where
  (n, arg) `dependsOn` name = arg `dependsOn` name && n /= name

instance Dependencies LHDecl where
  dependsOn (Import _ decls) name = any (`dependsOn` name) decls
  dependsOn (Data n constrs) name = n == name || any (\(c, ILH.ArrType cargs cret) -> c == n || any (`dependsOn` name) (cret : map snd cargs)) constrs
  dependsOn (Definition f tp expr _) name = f == name || any (`dependsOn` name) (argsTps tp) || retTp tp `dependsOn` name || expr `dependsOn` name

instance Binder LHDecl where
  bindName (Import n _) = n
  bindName (Data n _) = n
  bindName (Definition n _ _ _) = n

-- * implementing topological sorting for 'LHDecl' using 'Dependencies' and 'Binder' instances

-- | topologically sort the declarations in dependency order
topologicalSort :: (Dependencies a) => (Binder a) => [a] -> [a]
topologicalSort l = flattenSCCs $ stronglyConnComp graph
  where
    keys = map bindName l
    mkVertex decl = (decl, bindName decl, filter (decl `dependsOn`) keys)
    graph = map mkVertex l
