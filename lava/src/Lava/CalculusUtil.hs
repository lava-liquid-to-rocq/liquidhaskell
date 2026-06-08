{-# LANGUAGE OrPatterns #-}

-- | Helper functions on the ILH 'Calculus' grammar used by the Lava
--   translation.
--
--   Re-exports the shared 'Language.Haskell.Liquid.RefCore.Calculus'
--   and adds the AST-manipulation helpers that only the translation needs.
module Lava.CalculusUtil
  ( module Language.Haskell.Liquid.RefCore.Calculus
  , builtinDCs
  , builtinTCs
  , mkVarWithAnnot
  , mkAnd
  , mkSub
  , mkProj
  , mkRefType
  , fromArrType
  , arity
  , defaultRef
  , tpArgs
  , tpArgsArLoc
  , headVar
  , popToBop
  , isValue
  , isRecTC
  , harmonizeBinderNames
  , removeArgProjs
  , removeProjs
  , traceFunc
  ) where

import Prelude hiding ((<>))
import Data.Bifunctor (second)
import Data.Set (Set)
import qualified Data.Set as Set

import Text.PrettyPrint.HughesPJClass
import Debug.Trace (trace)

import Language.Haskell.Liquid.RefCore.Calculus
import Language.Haskell.Liquid.RefCore.Names (Id)

builtinDCs :: [Reft]
builtinTCs :: [BaseType]
builtinDCs = [ttTm, ffTm, unitTm]
builtinTCs = [boolTp, unitTp]

mkVarWithAnnot :: Id -> RefType -> Localization -> Reft
mkVarWithAnnot x tpx loc =
  let typeAnnot =
        case arrs tpx of
          ([], _) -> Nothing
          (_, (_, retTp, _)) -> Just retTp
   in Var x typeAnnot loc

-- | Wrapper for And, defined as TT for empty conjuncts list
mkAnd :: [Reft] -> Reft
mkAnd args = if null args' then ttTm else foldl1 (Bop And) args'
  where
    args' = filter (/= ttTm) args

-- | mkSub(r, from, to) makes a subsumption cast unless tp1 = tp2
--   Should we collapse casts? Would it hide intermediate properties needed for automation?
mkSub :: Reft -> RefType -> RefType -> Reft
mkSub r from to | from == to = r
mkSub r from to = Sub r from to

-- | Build a projection, removing the outer injection or subsumptions.
mkProj :: ProjKind -> Reft -> Reft
mkProj _ (Inj r _) = r
mkProj k (Sub r _ _) = mkProj k r
mkProj k r = Proj k r

-- | Make a refinement type
mkRefType :: (Id, BaseType, Reft) -> RefType
mkRefType (x, a, r) = RefType x a r

-- | Extracts the elements out of an ArrType and raises an error for another type
fromArrType :: RefType -> (Id, RefType, RefType)
fromArrType (ArrType x tpx tp) = (x, tpx, tp)
fromArrType _ = error "ArrType expected"

-- | Arity of a refinement type
arity :: RefType -> Integer
arity (ArrType _ _ tp) = 1 + arity tp
arity (RefType {}) = 0

-- | defaultRef tp := {VV : tp | True}
defaultRef :: BaseType -> RefType
defaultRef tp = RefType "VV" tp ttTm

-- | tpArgs(x_i:R_i|r_i)_{i ≤ n} -> R) = [x_i]_{i ≤ n}
tpArgs :: RefType -> [Id]
tpArgs = map fst . fst . arrs

-- | tpArgsArLoc((x_i:R_i|r_i)_{i ≤ n} -> R) = [Var x_i R_i Local]_{i ≤ n}
-- Used to give the initial patterns on the parameters of a function
tpArgsArLoc :: RefType -> [Reft]
tpArgsArLoc = map (\(x, tp) -> mkVarWithAnnot x tp Local) . fst . arrs

-- | Head variable of an application (also when projected)
headVar :: Reft -> Maybe Id
headVar r = case fst (apps r) of
  Var f _ _ -> Just f
  Proj _ (Var f _ _) -> Just f
  _ -> Nothing

-- | Gives the bop corresponding to a pop
popToBop :: ProofOp -> Bop
popToBop PEq = Eq
popToBop PLeq = Leq
popToBop PGeq = Geq

-- | Whether a refinement is a value: a local variable, a constructor applied to values, a literal or a projected value
isValue :: Reft -> Bool
isValue (Var _ _ Local; Var _ _ (Recursive {}); StringLit _; IntLit _; FloatLit _; DC _) = True
isValue r@(App {}) =
  case apps r of
    (DC _, args) -> all isValue args
    _ -> False
isValue (QMark r _ _) = isValue r
isValue (Pop _ _ r) = isValue r
isValue (Sub r _ _) = isValue r
isValue (Inj r _) = isValue r
isValue (Proj _ r) = isValue r
isValue (Var {}; Neg {}; Bop {}) = False

isRecTC :: Id -> [(Id, RefType)] -> Bool
isRecTC tc = any (isRecursive . snd)
  where
    isRecursive tp = any (isTC . snd) (fst $ arrs tp)
    isTC tp' = case tp' of RefType _ (TC tc') _ -> tc' == tc; _ -> False

-- | Harmonize the names of the variables bound by arrows:
--
-- > harmonizeBinderNames(x1:{x1':tp1 | r1} -> … -> xn:{xn':tpn | rn} -> {v:tp | rv})
-- >   = (x1:{x1:tp1 | r1{x1'/x1}} -> … -> xn:{xn:tpn | rn{xn'/xn}} -> {v:tp | rv})
harmonizeBinderNames :: RefType -> RefType
harmonizeBinderNames (ArrType x tpx tp) =
  let tpx' = case tpx of
        RefType x' a r -> RefType x a (rename x x' r)
        ArrType {} -> harmonizeBinderNames tpx
   in ArrType x tpx' $ harmonizeBinderNames tp
harmonizeBinderNames tp@(RefType {}) = tp

-- | Remove projections around first-order arguments of the type
-- If the flag is True, remove them everywhere.
-- This function should be used when only variables appear inside projections.
removeArgProjs :: Bool -> RefType -> RefType
removeArgProjs allProjs tp =
  let (args, (v, retTp, retReft)) = arrs tp
      args' = map (second (removeProjs allProjs Set.empty)) args
      ret' = removeProjs allProjs Set.empty (RefType v retTp retReft)
   in foldr (\(x, tpx) acc -> ArrType x tpx acc) ret' args'

-- | Remove projections around first-order variables in a type
-- The first parameter contains the variables for those we should keep the projection:
-- variables introduced by the arrow of a HO parameter.
-- The second parameter contains variables whose projection should not be erased
removeProjs :: Bool -> Set Id -> RefType -> RefType
-- In x:tpx -> tp, we do not want to remove projections around the occurences of x in tp (if allProjs is False)
removeProjs allProjs vars (ArrType x tpx tp') =
  ArrType x (removeProjs allProjs vars tpx) (removeProjs allProjs (x `Set.insert` vars) tp')
removeProjs allProjs vars' (RefType y a reft) = RefType y a (aux vars' reft)
  where
    aux _ (Proj _ r) | allProjs = r
    aux vars projx@(Proj _ (Var x Nothing loc)) =
      if x `elem` vars then projx else Var x Nothing loc
    aux _ projf@(Proj _ (Var _ (Just _) _)) = projf
    aux _ p@(Proj {}) =
      error $ "Calculus.removeArgProjs should only be used at top-level, when projections are made only on local variables. Found term: " ++ prettyShow p
    aux _ r@(Var {}; StringLit {}; IntLit {}; FloatLit {}; DC {}) = r
    aux vars (App r1 r2) = App (aux vars r1) (aux vars r2)
    aux vars (Neg r) = Neg (aux vars r)
    aux vars (Bop bop r1 r2) = Bop bop (aux vars r1) (aux vars r2)
    aux vars (QMark r rh rp) = QMark (aux vars r) (aux vars rh) (aux vars rp)
    aux vars (Pop pop r1 r2) = Pop pop (aux vars r1) (aux vars r2)
    aux _ (Sub {}; Inj {}) = error "Subsumption or injection cast found in type refinement in Calculus.removeArgProjs."

-- | renameFresh(x,tm) gives x a fresh name in tm
-- Unused, kept for reference.
-- renameFresh :: (HasVars a) => Id -> a -> a
-- renameFresh x tm = rename (fresh x tm) x tm

traceFunc :: Id -> [Doc] -> Bool
traceFunc f args =
  let doc = text f <> parens (hsep $ punctuate comma args)
   in trace (render doc) False
