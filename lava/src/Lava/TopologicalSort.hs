{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OrPatterns #-}

-- | This module defines the Dependencies and Binder classes and instances, used
-- to export a sort function respecting dependencies order
module Lava.TopologicalSort (topologicalSort) where

import Data.Graph
import qualified Lava.Calculus as LH
import qualified Lava.Coq as Coq
import Lava.Names (Id)
import Prelude

-- * 'Dependencies' class and instances, 'Binder class' and instance for 'LHDecl'

class Dependencies a where
  dependsOn :: a -> Id -> Bool

instance (Dependencies a) => Dependencies (Maybe a) where
  dependsOn Nothing _ = False
  dependsOn (Just tm) name = tm `dependsOn` name

-- * 'Dependencies' and 'Binder' instances for 'Calc.Decl'

instance Dependencies LH.BaseType where
  dependsOn (LH.TC typ) name = typ == name
  dependsOn (LH.Builtin _) _ = False

instance Dependencies LH.Reft where
  dependsOn (LH.Var n _ _) name = n == name
  dependsOn (LH.App f t) name = dependsOn f name || dependsOn t name
  dependsOn (LH.Neg p) name = dependsOn p name
  dependsOn (LH.Bop _ s t) name = dependsOn s name || dependsOn t name
  dependsOn (LH.QMark r rh rp) name = dependsOn r name || dependsOn rh name || dependsOn rp name
  dependsOn (LH.Pop _ r1 r2) name = dependsOn r1 name || dependsOn r2 name
  dependsOn (LH.Sub r _ _) name = dependsOn r name
  dependsOn (LH.Inj r _) name = dependsOn r name
  dependsOn (LH.Proj r) name = dependsOn r name
  dependsOn _ _ = False

instance Dependencies LH.RefType where
  dependsOn (LH.RefType _ t reft) name = dependsOn t name || dependsOn reft name
  dependsOn (LH.ArrType x dom codom) name = (dom `dependsOn` name || codom `dependsOn` name) && x /= name

dependsBranchCalc :: ((Id, [(Id, Bool)]), Maybe LH.Expr) -> Id -> Bool
dependsBranchCalc ((c, ys), body) name = (c == name || body `dependsOn` name) && name `notElem` map fst ys

instance Dependencies LH.Expr where
  dependsOn (LH.Reft r) name = dependsOn r name
  dependsOn (LH.Let x tp df tm) name = (df `dependsOn` name || tm `dependsOn` name || tp `dependsOn` name) && x /= name
  dependsOn (LH.Case r branches _) name = dependsOn r name || any (`dependsBranchCalc` name) branches

instance Dependencies LH.Decl where
  dependsOn (LH.Data n constrs) name =
    n == name || any (\(c, tp) -> c == name || dependsOn tp name) constrs
  dependsOn (LH.Definition f tp expr _) name =
    f == name || dependsOn tp name || dependsOn expr name

class Binder a where
  bindName :: a -> Id

instance Binder LH.Decl where
  bindName (LH.Data n _) = n
  bindName (LH.Definition n _ _ _) = n

instance Binder Coq.Decl where
  bindName d = case d of
    Coq.Fix n _ _ _ -> n
    Coq.Definition f _ _ _ _ -> f
    Coq.CoqInductive tc _ _ _ -> tc
    Coq.CoqNewType t _ -> t
    Coq.Equations f _ _ _ -> f
    -- \| load, visibility modifier, hint
    (Coq.AddHint {}; Coq.ChangeVisibility {}; Coq.Load {}; Coq.Instance {}; Coq.TacInstance {}) -> ""

-- * Topological sort for declarations using 'Dependencies' and 'Binder' instances

-- | Topologically sort the declarations in dependency order
topologicalSort :: (Dependencies a) => (Binder a) => [a] -> [a]
topologicalSort l = flattenSCCs $ stronglyConnComp graph
  where
    keys = map bindName l
    mkVertex decl = (decl, bindName decl, filter (decl `dependsOn`) keys)
    graph = map mkVertex l
