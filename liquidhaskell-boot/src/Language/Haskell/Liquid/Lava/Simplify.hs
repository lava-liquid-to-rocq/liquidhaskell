{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.Haskell.Liquid.Lava.Simplify (simplify) where

import Control.Monad.State.Strict
import Data.Bifunctor (second)
import Data.List (isPrefixOf)

import GHC.Core
import GHC.Types.Var
import Language.Haskell.Liquid.GHC.Misc (showPpr)

import Lava.Util (showStripped)

class Simplifiable a where
  simplify :: a -> a

instance Simplifiable CoreBind where
  simplify (NonRec x e) = NonRec x (simplify e)
  simplify (Rec xes)    = Rec (map (second simplify) xes)

instance Simplifiable CoreExpr where
  simplify e =
    let (e', su) = grapANFs e
    in subst su e'

-------------------------------------------------------------------------------

-- | Substitutions ------------------------------------------------------------

-------------------------------------------------------------------------------

binds :: CoreBind -> [Var]
binds (NonRec x _) = [x]
binds (Rec xes)    = map fst xes

isANFVar :: Var -> Bool
isANFVar = isPrefixOf "lq_anf" . showStripped

-- TODO use Map instead?
type Subst = [(Var, CoreExpr)]

without :: Subst -> [Var] -> Subst
without su xs = filter ((`notElem` xs) . fst) su

eqSubst :: Subst -> Subst -> Bool
eqSubst s1 s2 =
  length s1 == length s2
    && and (zipWith (\(v1, e1) (v2, e2) -> v1 == v2 && showPpr e1 == showPpr e2) s1 s2)

fixpSubst :: Subst -> Subst
fixpSubst su =
  let su' = [(x, subst su ex) | (x, ex) <- su]
  in if eqSubst su su' then su else fixpSubst su'

class Subable a where
  subst :: Subst -> a -> a

instance Subable CoreExpr where
  subst su (Var x)
    | Just e <- lookup x su = e
    | otherwise = Var x
  subst _ (Lit l) = Lit l
  subst su (App e1 e2) = App (subst su e1) (subst su e2)
  subst su (Lam x e) = Lam x (subst (su `without` [x]) e)
  subst su (Let b e) = Let (subst su b) (subst (su `without` binds b) e)
  subst su (Case e x t alts) = Case (subst su e) x t (subst (su `without` [x]) alts)
  subst su (Cast e c) = Cast (subst su e) c
  subst su (Tick t e) = Tick t (subst su e)
  subst _ (Type t) = Type t
  subst _ (Coercion c) = Coercion c

instance Subable CoreAlt where
  subst su (Alt c xs e) = Alt c xs (subst (su `without` xs) e)

instance Subable a => Subable [a] where
  subst su = map (subst su)

instance Subable CoreBind where
  subst su (NonRec x e) = NonRec x (subst (su `without` [x]) e)
  subst su (Rec xes) = Rec (map (second (subst su')) xes)
    where
      su' = su `without` map fst xes

-------------------------------------------------------------------------------

-- | Grap ANF -----------------------------------------------------------------

-------------------------------------------------------------------------------

grapANFs :: CoreExpr -> (CoreExpr, Subst)
grapANFs expr = (e', fixpSubst su)
  where
    (e', su) = runState (go expr) []

    go (Let (NonRec x ex) e)
      | isANFVar x = do ex' <- go ex
                        modify ((x, ex') :)
                        go e
      | otherwise = do ex' <- go ex
                       Let (NonRec x ex') <$> go e
    go (Let (Rec xes) e) = do xes' <- traverse (traverse go) xes
                              Let (Rec xes') <$> go e
    go (App e1 e2)       = App <$> go e1 <*> go e2
    go (Lam x e)         = Lam x <$> go e
    go (Case e x t alts) = do e' <- go e
                              Case e' x t <$> traverse goAlt alts
    go (Cast e c)         = (`Cast` c) <$> go e
    go (Tick t e)         = Tick t <$> go e
    go e@(Type _)         = pure e
    go e@(Coercion _)     = pure e
    go e@(Lit _)          = pure e
    go e@(Var _)          = pure e

    goAlt (Alt c xs e) = Alt c xs <$> go e

