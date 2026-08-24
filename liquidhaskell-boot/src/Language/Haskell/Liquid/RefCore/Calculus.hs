{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Grammars, printer and suable functions for ILH
module Language.Haskell.Liquid.RefCore.Calculus
  ( -- * Grammar
    Builtin (..),
    BaseType (..),
    RefType (..),
    Decl (..),
    Expr (..),
    Reft (..),
    ProjKind (..),
    Localization (..),
    DesState (..),
    Bop (..),
    ProofOp (..),

    -- * Builtin type and data constructors
    boolTp,
    ttTm,
    ffTm,
    unitTp,
    unitTm,
    listTp,
    consTm,
    nilTm,

    -- * Construction and destruction
    mkVar,
    arrs,
    mkArrows,
    apps,
    mkApplications,
    renameParams,

    -- * Free variables and substitution
    Subable (..),
    subableFreeVars,
    HasVars (..),
    freeTermVars,
    freeTypeVars,
    freeVars,
    fresh,
    substs,
  )
where

import Data.Bifunctor (first)
import Data.Binary (Binary)
import Data.Data
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
-- import Debug.Trace (trace)

import Data.Maybe (isNothing)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Tuple.Extra (first3, second3)
import GHC.Generics (Generic)
import Language.Haskell.Liquid.RefCore.Names (Id, boolTpName, consTmName, ffTmName, freshVar, listTpName, nilTmName, ttTmName, unitTmName, unitTpName)
import Text.PrettyPrint
import Text.PrettyPrint.HughesPJClass hiding (first)
import Prelude hiding (lookup, (<>))

-- * The grammar

-- ** Types

-- | Builtin types
-- In Fixpoint, we have the Constant types Integer, Double and Text. There, from GHC.Core,
-- Floats are stored as Double, and Chars and Strings are converted to Text (we switch back to
-- Strings for simplicity). Other GHC.Core literals are not relevant for us
--
-- > B ::= Integer | Double | String
data Builtin = Integer | Double | String deriving (Data, Eq, Show, Generic, Binary)

-- | Base Types
--
-- > A ::= B | TC R* | α
data BaseType = Builtin Builtin | TC Id [RefType] | TyVar Id deriving (Data, Eq, Show, Generic, Binary)

-- | Refinement types
--
-- > R ::= {x: A | r} | x:Rx -> R | ∀α, R
data RefType
  = RefType Id BaseType Reft
  | ArrType Id RefType RefType
  | FAType Id RefType
  deriving (Data, Show, Generic, Binary)

-- ** Declaration-level grammar

-- | Declarations
--
-- > D ::= data tc α* := (C :: R)*
-- >     | (reflect)? def f :: R := e
data Decl
  = -- | type constructor: name, type variables (for now all considered positive) and branches with (constructor name, type)
    Data Id [Id] [(Id, RefType)]
  | -- | (function) definition: name, type, body, is it reflected
    Definition Id RefType Expr Bool
  | -- | imported module: module name and its declarations
    Import Id [Decl]
  deriving (Data, Eq, Show, Generic, Binary)

-- TODO: make QMark, equality (and others?) actually polymorphic

-- | Structural expressions
--
-- > e ::= r
-- >     | let x (:: R)? := e in e
-- >     | case r of (C [(x,bool)]* |-> (e | unreachable))*
-- >     | e ? (e proves r)
data Expr
  = -- | Refinement used as expression
    Reft Reft
  | -- | Let with type annotation. binds the dependent variables in R
    --   for lets in the code, we can always get an annotation, but we also create some for ANF
    Let Id (Maybe RefType) Expr Expr
  | -- | Pattern matching (includes conditionals), with Maybe for optional branches.
    --   The boolean in the list of parameters is true if the parameter is inductive
    --   and we are destructing one of the parameters of the function
    --   The last element indicates if the case must be translated to
    --   destruct (Nothing) or induction, in which case we have the list of variables to generalize
    Case Reft [((Id, [(Id, Bool)]), Maybe Expr)] (Maybe [Id])
  | QMark Expr Expr Reft
  deriving (Data, Show, Generic, Binary)

-- | Simple LH terms including formulas.
--   Terms of this type can occur as (sub)terms in refinements
--   Variables are annotated with their localization and,
--   if they are a function type, with their unrefined return type
--
-- > r ::= x/(A,loc)
-- >     | lit ∈ B
-- >     | C
-- >     | r r
-- >     | r [R]
-- >     | ¬r
-- >     | r `op` r
-- >     | r `pop` r
data Reft
  = Var Id (Maybe BaseType) Localization
  | StringLit String
  | IntLit Integer
  | FloatLit Double
  | DC Id
  | App Reft Reft
  | TyApp Reft RefType
  | Neg Reft
  | Bop Bop Reft Reft
  | Pop ProofOp Reft Reft
  | Sub Reft RefType RefType
  | Inj Reft RefType
  | Proj ProjKind Reft
  deriving (Data, Eq, Show, Generic, Binary)

-- | The different kinds of projections:
-- `proj` from the generalized projections typeclass,
-- Rocq's `proj1_sig1` and `proj2_sig`
-- FIX: we shouldn't need this here, only in Rocq,
-- but Rocq cannot always find the correct instance
data ProjKind = GenProj | Sig1 | Sig2 deriving (Data, Eq, Show, Generic, Binary)

-- | Localization of the variables.
-- The recursive variables take the name of the induction variable
-- (this is used to clean up unused IHs) and the current branch pattern
--
-- loc ::= L | G | Y (x, σ)
data Localization = Local | Global | Recursive Id [DesState] deriving (Data, Eq, Show, Generic, Binary)

-- | State of the parameters: either intact (with name and arity) or destructed
-- This state is used to elaborate pattern matching and recursive variables, and to translate recursive calls
data DesState = Param Id Integer | Destructed deriving (Data, Eq, Show, Generic, Binary)

-- | Builtin binary operators (@op@)
data Bop
  = Plus
  | Minus
  | Times
  | Div
  | Mod
  | Eq
  | Neq
  | Leq
  | Geq
  | Lt
  | Gt
  | And
  | Or
  | Impl
  | Iff
  deriving (Data, Eq, Generic, Binary)

-- | Binary proof operators
--
-- > pop ::= === | =<= | =>=
data ProofOp = PEq | PLeq | PGeq deriving (Data, Eq, Generic, Binary)

-- Builtin type and data constructors

boolTp, unitTp :: BaseType
boolTp = TC boolTpName []
unitTp = TC unitTpName []

listTp :: RefType -> BaseType
listTp tp = TC listTpName [tp]

unitTm, ttTm, ffTm, consTm, nilTm :: Reft
ttTm = DC ttTmName
ffTm = DC ffTmName
unitTm = DC unitTmName
consTm = DC consTmName
nilTm = DC nilTmName

-- * Functions on the terms

-- ** Constructions

-- | Make a local variable reference with a dummy type
mkVar :: Id -> Reft
mkVar x = Var x Nothing Local

-- ** Other functions

-- | arrs(R) := forall (α_j)_{j ≤ m}, (x_i:R_i)_{i ≤ n} -> R' where n is maximal
arrs :: RefType -> ([Id], [(Id, RefType)], (Id, BaseType, Reft))
arrs (RefType x a r) = ([], [], (x, a, r))
arrs (ArrType x tpx tp) = ((x, tpx) :) `second3` arrs tp
arrs (FAType α tp) = (α :) `first3` arrs tp

-- | Inverse operation of arrs
mkArrows :: ([Id], [(Id, RefType)], RefType) -> RefType
mkArrows (αs, args, ret) =
  let monoArrow = foldr (\(n, t) acc -> ArrType n t acc) ret args
   in foldr FAType monoArrow αs

-- | Flattens an application
apps :: Reft -> (Reft, [RefType], [Reft])
apps (App tm1 tm2) = let (hd, args, refts) = apps tm1 in (hd, args, refts ++ [tm2])
apps tm@(TyApp {}) = let (hd, tpArgs) = aux tm in (hd, tpArgs, [])
  where
    aux (TyApp tm1 tm2) = let (hd, tpArgs) = aux tm1 in (hd, tpArgs ++ [tm2])
    aux (App {}) = error "Calculus.apps: found term application before type application"
    aux tm' = (tm', [])
apps tm = (tm, [], [])

-- | Inversion operaton of apps
mkApplications :: Reft -> [RefType] -> [Reft] -> Reft
mkApplications hd tpArgs args = foldl App (foldl TyApp hd tpArgs) args

-- | Rename all the arguments of an arrow:
--
-- > renameParams([β,y1,y2], ∀α, x1:{x1:α | True} -> x2:{x2:α | x1 == x2} -> {v:α | v = x1 + x2})
-- >   = ∀β, y1:{x1:β | True} -> y2:{x2:β | y1 == x2} -> {v:β | v = y1 + y2}
renameParams :: [Id] -> RefType -> RefType
-- renameParams ys tp | trace (render $ "renameParams (" <> pPrint ys <> comma <+> pPrint tp <> ")") False = undefined
renameParams = aux []
  where
    aux :: [(Id, Id)] -> [Id] -> RefType -> RefType
    -- aux σ ys tp | trace (render $ "renameParams.aux (" <+> pPrint σ <> comma <+> pPrint ys <> comma <+> pPrint tp <> ")") False = undefined
    aux σ [] tp = renames σ tp
    aux σ _ tp@(RefType {}) = renames σ tp
    aux σ (β : ys) (FAType α tp)
      | α `notElem` freeTypeVars tp || α == β =
          FAType α (aux σ ys tp)
    aux σ (y : ys) (ArrType x tpx tp)
      | x `notElem` freeTermVars tp || x == y =
          ArrType y (renames σ tpx) (aux σ ys tp)
    -- NOTE: we could handle some of the error cases by applying the
    -- substitutions globally for each binder, or by traversing the type in the
    -- opposite direction. But with reasonable namings that should not be necessary
    aux _ (β : _) (FAType α tp)
      | β `elem` freeVars tp =
          error . render $ "Name clash while renaming variable" <+> text α <+> "to" <+> text β <+> "in" <+> pPrint tp
    aux _ (y : _) tp0@(ArrType x _ tp)
      | y `elem` freeVars tp =
          error . render $ "Name clash while renaming variable" <+> text x <+> "to" <+> text y <+> "in" <+> pPrint tp0
    aux σ (β : ys) (FAType α tp) = FAType β (aux ((β, α) : σ) ys tp)
    aux σ (y : ys) (ArrType x tpx tp) = ArrType y (renames σ tpx) (aux ((y, x) : σ) ys tp)
    renames σ = substs (map (first Rename) σ)

-- ** Substitution and free variables

data Subable = TypeSub RefType | TermSub Reft | Rename Id

-- | Free variables of a subable term
-- Defined separately because we do not know if a Rename variable is a type or
-- term variable, and thus cannot define freeVarsMap
subableFreeVars :: Subable -> Set Id
subableFreeVars (TypeSub tp) = freeVars tp
subableFreeVars (TermSub r) = freeVars r
subableFreeVars (Rename x) = Set.singleton x

-- * Typeclass related to free variables

class HasVars a where
  -- | Return the free variables
  -- `Nothing` for type variables and the return type and localization for term variables
  freeVarsMap :: a -> Map Id (Maybe (Maybe BaseType, Localization))

  -- | Return the bound variables with their type (they are all local)
  boundVars :: a -> Set Id

  -- | subst r x tm is {r/x}tm
  subst :: Subable -> Id -> a -> a

-- | Free term variables with return type and localization annotations
freeTermVarsAnnot :: (HasVars a) => a -> Map Id (Maybe BaseType, Localization)
freeTermVarsAnnot = Map.mapMaybe id . freeVarsMap

-- | Free term variables
freeTermVars :: (HasVars a) => a -> Set Id
freeTermVars = Map.keysSet . freeTermVarsAnnot

-- | Free type variables
freeTypeVars :: (HasVars a) => a -> Set Id
freeTypeVars = Map.keysSet . Map.filter isNothing . freeVarsMap

-- | Free term and type variables
freeVars :: (HasVars a) => a -> Set Id
freeVars = Map.keysSet . freeVarsMap

-- | return a variable fresh wrt to the free and bound variables in the second argument
fresh :: (HasVars a) => Id -> a -> Id
fresh x tm = freshVar x (freeVars tm `Set.union` boundVars tm)

-- | Apply a list of substitutions, starting from the right
substs :: (HasVars a) => [(Subable, Id)] -> a -> a
substs = flip (foldr (uncurry subst))

instance HasVars Reft where
  freeVarsMap (Var x tp loc) = Map.singleton x (Just (tp, loc))
  freeVarsMap (App hd arg) = freeVarsMap [hd, arg]
  freeVarsMap (TyApp r tp) = freeVarsMap r `Map.union` freeVarsMap tp
  freeVarsMap (Bop _ r1 r2) = freeVarsMap [r1, r2]
  freeVarsMap (Neg r) = freeVarsMap r
  freeVarsMap (StringLit _; IntLit _; FloatLit _; DC _) = Map.empty
  freeVarsMap (Pop _ r1 r2) = freeVarsMap [r1, r2]
  freeVarsMap (Sub r from to) = freeVarsMap r `Map.union` freeVarsMap [from, to]
  freeVarsMap (Inj r tp) = freeVarsMap r `Map.union` freeVarsMap tp
  freeVarsMap (Proj _ r) = freeVarsMap r

  -- Empty on unelaborated refinements, but has the bound variables of the types in casts
  boundVars (Var {}; StringLit _; IntLit _; FloatLit _; DC _) = Set.empty
  boundVars (App hd arg) = boundVars [hd, arg]
  boundVars (TyApp r tp) = boundVars r `Set.union` boundVars tp
  boundVars (Bop _ r1 r2) = boundVars [r1, r2]
  boundVars (Neg r) = boundVars r
  boundVars (Pop _ r1 r2) = boundVars [r1, r2]
  boundVars (Sub r from to) = boundVars r `Set.union` boundVars [from, to]
  boundVars (Inj r tp) = boundVars r `Set.union` boundVars tp
  boundVars (Proj _ r) = boundVars r

  subst (TermSub r') x (Var y _ _) | y == x = r'
  subst (Rename z) x (Var y tp loc) | y == x = Var z tp loc
  subst _ _ r0@(Var {}; StringLit _; IntLit _; FloatLit _; DC _) = r0
  subst r' x (App h arg) = App (subst r' x h) (subst r' x arg)
  subst r' x (TyApp r tp) = TyApp (subst r' x r) (subst r' x tp)
  subst r' x (Bop bop r1 r2) = Bop bop (subst r' x r1) (subst r' x r2)
  subst r' x (Neg r) = Neg $ subst r' x r
  subst r' x (Pop pop r1 r2) = Pop pop (subst r' x r1) (subst r' x r2)
  subst r' x (Sub r tps tpt) = Sub (subst r' x r) (subst r' x tps) (subst r' x tpt)
  subst r' x (Inj r tp) = Inj (subst r' x r) (subst r' x tp)
  subst r' x (Proj kind r) = Proj kind (subst r' x r)

instance HasVars Expr where
  freeVarsMap (Reft r) = freeVarsMap r
  freeVarsMap (Let x tp ex e) =
    freeVarsMap tp `Map.union` Map.delete x (freeVarsMap [ex, e])
  freeVarsMap (Case r branches _) =
    freeVarsMap r `Map.union` Map.unions (map fvBranch branches)
    where
      fvBranch ((_, ys), ebr) = freeVarsMap ebr `Map.withoutKeys` Set.fromList (map fst ys)
  freeVarsMap (QMark r rh rp) = freeVarsMap [r, rh, Reft rp]

  boundVars (Reft r) = boundVars r
  boundVars (Let x tp ex e) =
    Set.singleton x `Set.union` boundVars tp `Set.union` boundVars [ex, e]
  boundVars (Case r branches _) =
    boundVars r `Set.union` Set.unions (map bvBranch branches)
    where
      bvBranch ((_, ys), e) = Set.fromList (map fst ys) `Set.union` boundVars e
  boundVars (QMark r rh rp) = boundVars [r, rh, Reft rp]

  subst r x (Reft re) = Reft $ subst r x re
  subst r x (Let y tp ey e')
    | y == x = Let y (subst r x tp) (subst r x ey) e'
    | y `Set.member` subableFreeVars r && x `Set.member` freeVars e' =
        Let z (subst r x tp) (subst r x ey) (substs [(r, x), (Rename z, y)] e')
    | otherwise = Let y (subst r x tp) (subst r x ey) (subst r x e')
    where
      z = freshVar y (subableFreeVars r `Set.union` freeVars (Let y tp ey e'))
  subst r x (Case r' branches genVars) =
    Case (subst r x r') (map substBranch branches) genVars
    where
      substBranch br@((_, ys), ebr)
        | x `elem` map fst ys || maybe True (notElem x . freeVars) ebr = br
      substBranch ((c, ys), ebr) = ((c, ys'), subst r x $ substs α ebr)
        where
          freshYs = foldr freshVars [] ys
          α = map (first Rename) . filter (uncurry (/=)) $ zipWith (\(y, _) z -> (z, y)) ys freshYs
          ys' = zipWith (\(_, b) z -> (z, b)) ys freshYs
          freshVars (y, _) vars =
            if y `elem` subableFreeVars r
              then freshVar y (fvre `Set.union` Set.fromList vars) : vars
              else y : vars
          fvre = subableFreeVars r `Set.union` freeVars (Case r' branches genVars)
  subst r x (QMark r' rh rp) = QMark (subst r x r') (subst r x rh) (subst r x rp)

instance HasVars RefType where
  freeVarsMap (RefType x tp r) = fvtp `Map.union` Map.delete x (freeVarsMap r)
    where
      fvtp = case tp of
        Builtin _ -> Map.empty
        TC _ tps -> freeVarsMap tps
        TyVar α -> Map.singleton α Nothing
  freeVarsMap (ArrType x tpx tp) = freeVarsMap tpx `Map.union` Map.delete x (freeVarsMap tp)
  freeVarsMap (FAType α tp) = Map.delete α (freeVarsMap tp)

  boundVars (RefType x tp r) = Set.unions [Set.singleton x, bvtp, boundVars r]
    where
      bvtp = case tp of
        (Builtin _; TC {}) -> Set.empty
        TyVar α -> Set.singleton α
  boundVars (ArrType x tpx tp) = Set.singleton x `Set.union` boundVars [tpx, tp]
  boundVars (FAType α tp) = Set.singleton α `Set.union` boundVars tp

  subst (TypeSub tp) α tp0@(RefType x (TyVar α') rx) | α == α' =
    case tp of
      RefType y b ry ->
        let rx' = subst (Rename y) x rx
            conj = if rx' == ttTm then ry else if ry == ttTm then rx' else Bop And rx' ry
         in RefType y b conj
      ArrType {} ->
        if rx == ttTm
          then tp
          else
            error
              ( render $
                  "TODO: trying to replace type variable with non-trivial refinement for arrow type: {" <> pPrint tp <> "/" <> text α <> "}" <+> pPrint tp0
              )
      FAType {} -> error "Forall found inside refined type (subst instance for RefType)"
  subst r x (RefType y b reft) =
    if y == x then RefType y bSubbed reft else RefType y bSubbed (subst r x reft)
    where
      bSubbed = case b of
        TC tc tps -> TC tc (map (subst r x) tps)
        (TyVar _; Builtin _) -> b
  subst r x (ArrType y tpy tp')
    | y == x = ArrType y (subst r x tpy) tp'
    | y `Set.member` subableFreeVars r && x `Set.member` freeVars tp' =
        ArrType z (subst r x tpy) (substs [(r, x), (Rename z, y)] tp')
    | otherwise = ArrType y (subst r x tpy) (subst r x tp')
    where
      z = freshVar y (subableFreeVars r `Set.union` freeVars (ArrType y tpy tp'))
  subst r x tp@(FAType α tp')
    | α == x = tp
    | α `Set.member` subableFreeVars r =
        FAType α' (substs [(r, x), (Rename α', α)] tp')
    | otherwise = FAType α (subst r x tp')
    where
      α' = freshVar α (subableFreeVars r `Set.union` freeVars tp)

instance (HasVars a) => HasVars [a] where
  freeVarsMap tms = Map.unions $ map freeVarsMap tms
  boundVars tms = Set.unions $ map boundVars tms
  subst r x = fmap (subst r x)

instance (HasVars a) => HasVars (Maybe a) where
  freeVarsMap = maybe Map.empty freeVarsMap
  boundVars = maybe Set.empty boundVars
  subst r x = fmap (subst r x)

{- instance HasVars Subable where
  freeVarsMap (TypeSub tp) = freeVarsMap tp
  freeVarsMap (TermSub tm) = freeVarsMap tm
  freeVarsMap (Rename x) = Map.singleton
  boundVars =
  subst r x = -}

-- * Equality instance using α-renaming

instance Eq RefType where
  tp1@(RefType x tpx rx) == tp2@(RefType y tpy ry) =
    let z = fresh x [tp1, tp2]
        (α1, α2) = if x /= y then ([(Rename z, x)], [(Rename z, y)]) else ([], [])
     in tpx == tpy && substs α1 rx == substs α2 ry
  tp1@(ArrType x tpx tp1') == tp2@(ArrType y tpy tp2') =
    let z = fresh x [tp1, tp2]
        (α1, α2) = if x /= y then ([(Rename z, x)], [(Rename z, y)]) else ([], [])
     in tpx == tpy && substs α1 tp1' == substs α2 tp2'
  tp1@(FAType x tp1') == tp2@(FAType y tp2') =
    let z = fresh x [tp1, tp2]
        (α1, α2) = if x /= y then ([(Rename z, x)], [(Rename z, y)]) else ([], [])
     in substs α1 tp1' == substs α2 tp2'
  _ == _ = False

instance Eq Expr where
  Reft r1 == Reft r2 = r1 == r2
  e1@(Let x tpx ex e1') == e2@(Let y tpy ey e2') =
    let z = fresh x [e1, e2]
        (α1, α2) = if x /= y then ([(Rename z, x)], [(Rename z, y)]) else ([], [])
     in tpx == tpy && ex == ey && substs α1 e1' == substs α2 e2'
  e1@(Case r1 alts1 genVars1) == e2@(Case r2 alts2 genVars2) =
    -- Equality is sensitive to the order of the alternatives
    r1 == r2 && all eqBranch (zip alts1 alts2) && genVars1 == genVars2
    where
      eqBranch (((c1, ys1), ebr1), ((c2, ys2), ebr2)) =
        let freshYs = foldr freshVars [] (zip ys1 ys2)
            α ys = map (first Rename) . filter (uncurry (/=)) $ zipWith (\(y, _) z -> (z, y)) ys freshYs
         in c1 == c2 && substs (α ys1) ebr1 == substs (α ys2) ebr2
      freshVars ((y1, _), (y2, _)) vars =
        if y1 /= y2
          then freshVar y1 (freeVars [e1, e2] `Set.union` Set.fromList vars) : vars
          else y1 : vars
  _ == _ = False

-- * Printer for the grammar

-- | Number of spaces in the indentation
identNb :: Int
identNb = 2

-- ** Precedence levels

-- TODO: harmonize with Rocq for simplicity

arrPrec :: Rational
arrPrec = 0

appPrec :: Rational
appPrec = 10

bopPrec :: Bop -> Rational
bopPrec Mod = 7
bopPrec Plus = 6
bopPrec Minus = 6
bopPrec Times = 7
bopPrec Div = 7
bopPrec Eq = 4
bopPrec Neq = 4
bopPrec Leq = 4
bopPrec Geq = 4
bopPrec Lt = 4
bopPrec Gt = 4
bopPrec And = 3
bopPrec Or = 2
bopPrec Impl = 1
bopPrec Iff = 1

popPrec :: ProofOp -> Rational
popPrec _ = 4

-- ** Instances

instance Pretty Builtin where
  pPrint = text . show

instance Pretty BaseType where
  pPrint (Builtin b) = pPrint b
  pPrint (TC tc tps) = hsep $ text tc : map pPrint tps
  pPrint (TyVar α) = text α

instance Pretty RefType where
  pPrintPrec _ _ (RefType _ a r) | r == ttTm = braces $ pPrint a
  pPrintPrec _ _ (RefType _ a r) | a == unitTp = braces . braces $ pPrint r
  pPrintPrec _ _ (RefType x a r) =
    braces (text x <> colon <+> pPrint a <+> char '|' <+> pPrint r)
  pPrintPrec l p (ArrType x tpx tp) =
    maybeParens (p > arrPrec) $ sep [text x <> colon <+> pPrintPrec l (arrPrec + 1) tpx, "->" <+> pPrintPrec l arrPrec tp]
  pPrintPrec _ _ (FAType α tp) = sep ["∀" <> text α <> comma, pPrint tp]

instance Pretty Decl where
  pPrint (Data tc αs constrs) =
    sep [ppTC, nest identNb . sep $ map (\dc -> char '|' <+> ppConstr dc) constrs]
    where
      ppTC = "data" <+> hsep (map text (tc : αs)) <+> ":="
      ppConstr (c, tpc) = text c <+> "::" <+> pPrint tpc
  pPrint (Definition f tp e isRefl) =
    sep [ppRefl <+> ppF, nest identNb (pPrint e)]
    where
      ppRefl = if isRefl then "refl" else empty
      ppF = "def" <+> text f <+> "::" <+> pPrint tp <+> ":="
  pPrint (Import modName decls) =
    vcat $ ("import" <+> text modName) : map (nest identNb . pPrint) decls

instance Pretty Expr where
  pPrint (Reft r) = pPrint r
  pPrint (Let x tpx ex e) = sep [sep [ppLet, pPrint ex], nest 1 ("in" <+> pPrint e)]
    where
      ppLet = "let" <+> ppTp <+> ":="
      ppTp = case tpx of
        Nothing -> text x
        Just tp -> parens (text x <> colon <+> pPrint tp)
  pPrint (Case r alts genVars) =
    vcat $ (des <+> pPrint r <+> "of") : map ppAlt alts
    where
      des = case genVars of Nothing -> "destruct"; Just _ -> "induct"
      ppAlt (pat, e) = sep [char '|' <+> ppPat pat <+> "->", nest identNb $ maybe "undefined" pPrint e]
      ppPat (c, ys) = text c <+> hsep (map (text . fst) ys)
  pPrint (QMark r rh rp) =
    pPrint r <+> char '?' <+> parens (pPrint rh <+> "proves" <+> pPrint rp)

instance Pretty Reft where
  pPrintPrec _ _ (Var x _ _) = text x
  pPrintPrec _ _ (StringLit s) = quotes $ text s
  pPrintPrec _ _ (IntLit i) = integer i
  pPrintPrec _ _ (FloatLit f) = double f
  pPrintPrec _ _ (DC c) = text c
  pPrintPrec l p (App r1 r2) =
    maybeParens (p > appPrec) $ pPrintPrec l p r1 <+> pPrintPrec l (appPrec + 1) r2
  pPrintPrec l p (TyApp r tp) =
    maybeParens (p > appPrec) $ pPrintPrec l p r <+> pPrint tp
  pPrintPrec l p (Neg r) =
    maybeParens (p > appPrec) $ "not" <+> pPrintPrec l (appPrec + 1) r
  pPrintPrec l p (Bop bop r1 r2) =
    maybeParens (p > bopPrec bop) $ pPrintPrec l (bopPrec bop) r1 <+> pPrint bop <+> pPrintPrec l (bopPrec bop) r2
  pPrintPrec l p (Pop pop r1 r2) =
    maybeParens (p > popPrec pop) $ pPrintPrec l (popPrec pop) r1 <+> pPrint pop <+> pPrintPrec l (popPrec pop) r2
  pPrintPrec _ p (Sub r from to) =
    maybeParens (p > appPrec) $ "sub" <+> parens (hsep $ punctuate comma (pPrint r : map pPrint [from, to]))
  pPrintPrec _ p (Inj r tp) =
    maybeParens (p > appPrec) $ "inj" <+> parens (pPrint r <> comma <+> pPrint tp)
  pPrintPrec l p (Proj _ r) =
    maybeParens (p > appPrec) $ "proj" <+> pPrintPrec l (appPrec + 1) r

instance Pretty Localization where
  pPrint Local = char 'L'
  pPrint Global = char 'G'
  pPrint (Recursive indVar _) = char 'Y' <+> text indVar

instance Show Bop where
  show Mod = "`mod`"
  show Plus = "+"
  show Minus = "-"
  show Times = "*"
  show Div = "/"
  show Eq = "=="
  show Neq = "/="
  show Leq = "<="
  show Geq = ">="
  show Lt = "<"
  show Gt = ">"
  show And = "&&"
  show Or = "||"
  show Impl = "=>"
  show Iff = "<=>"

instance Pretty Bop where
  pPrint = text . show

instance Show ProofOp where
  show PEq = "==="
  show PLeq = "=<="
  show PGeq = "=>="

instance Pretty ProofOp where
  pPrint = text . show
