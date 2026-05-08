{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Grammars, printer and suable functions for ILH
module Lava.Calculus where

import Data.Bifunctor (first, second)
import Data.Data
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace (trace)
import Lava.Names (Id, freshVar)
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
data Builtin = Integer | Double | String deriving (Data, Eq, Show)

-- | Base Types
--
-- > A ::= B | TC
data BaseType = Builtin Builtin | TC Id deriving (Data, Eq, Show)

-- | Refinement types
--
-- > R ::= {x: A | r} | x:Rx -> R
data RefType
  = RefType {argName :: Id, argTp :: BaseType, argRef :: Reft}
  | ArrType {parName :: Id, parTp :: RefType, retTp :: RefType}
  deriving (Data, Show)

-- ** Declaration-level grammar

-- | Declarations
--
-- > D ::= data tc := (C :: R)*
-- >     | (reflect)? def f :: R := e
data Decl
  = -- | type constructor: name and branches with (constructor name, type)
    Data Id [(Id, RefType)]
  | -- | (function) definition: name, type, body, is it reflected
    Definition Id RefType Expr Bool
  | -- | imported module: module name and its declarations
    Import Id [Decl]
  deriving (Data, Eq, Show)

-- | Structural expressions
--
-- > e ::= r
-- >     | let x (:: R)? := e in e
-- >     | case r of (C [(x,bool)]* |-> (e | unreachable))*
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
  deriving (Data, Show)

-- | Simple LH terms including formulas.
--   Terms of this type can occur as (sub)terms in refinements
--
-- > r ::= x/(ar,loc)
-- >     | lit ∈ B
-- >     | C
-- >     | r r
-- >     | ¬r
-- >     | r `op` r
-- >     | r ? (r proves r)
-- >     | r `pop` r
data Reft
  = Var Id Integer Localization
  | StringLit String
  | IntLit Integer
  | FloatLit Double
  | DC Id
  | App Reft Reft
  | Neg Reft
  | Bop Bop Reft Reft
  | QMark Reft Reft Reft
  | Pop ProofOp Reft Reft
  | Sub Reft RefType RefType
  | Inj Reft RefType
  | Proj Reft
  deriving (Data, Eq, Show)

-- | Localization of the variables.
-- The recursive variables take the name of the induction variable
-- (this is used to clean up unused IHs) and the current branch pattern
--
-- loc ::= L | G | Y (x, σ)
data Localization = Local | Global | Recursive Id [DesState] deriving (Data, Eq, Show)

-- | State of the parameters: either intact (with name and arity) or destructed
-- This state is used to elaborate pattern matching and recursive variables, and to translate recursive calls
data DesState = Param Id Integer | Destructed deriving (Data, Eq, Show)

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
  deriving (Data, Eq)

-- | Binary proof operators
--
-- > pop ::= === | =<= | =>=
data ProofOp = PEq | PLeq | PGeq deriving (Data, Eq)

-- Builtin type and data constructors

{- ORMOLU_DISABLE -}
boolTp :: BaseType
boolTpName :: Id
ttTm :: Reft
ttTmName :: Id
ffTm :: Reft
ffTmName :: Id
boolTp = TC boolTpName
boolTpName = "Bool"
ttTm = DC ttTmName
ttTmName = "True"
ffTm = DC ffTmName
ffTmName = "False"

unitTp :: BaseType
unitTpName :: Id
unitTm :: Reft
unitTmName :: Id
unitTp = TC unitTpName
unitTpName = "Unit"
unitTm = DC unitTmName
unitTmName = "unit"

builtinDCs :: [Reft]
builtinTCs :: [BaseType]
builtinDCs = [ttTm, ffTm, unitTm]
builtinTCs = [boolTp, unitTp]
{- ORMOLU_ENABLE -}

-- * Functions on the terms

-- ** Constructions

-- | Make a local variable reference
mkVar :: Id -> Reft
mkVar s = Var s 0 Local

-- | mkSub(r, from, to) makes a subsumption cast unless tp1 = tp2
--   Should we collapse casts? Would it hide intermediate properties needed for automation?
mkSub :: Reft -> RefType -> RefType -> Reft
mkSub r from to | from == to = r
mkSub r from to = Sub r from to

-- | Build a projection, removing the outer injection or subsumptions.
mkProj :: Reft -> Reft
mkProj (Inj r _) = r
mkProj (Sub r _ _) = mkProj r
mkProj r = Proj r

-- | Make a refinement type
mkRefType :: (Id, BaseType, Reft) -> RefType
mkRefType (x, a, r) = RefType x a r

-- ** Destructions

-- | Extracts the elements out of an ArrType and raises an error for another type
fromArrType :: RefType -> (Id, RefType, RefType)
fromArrType (ArrType x tpx tp) = (x, tpx, tp)
fromArrType _ = error "ArrType expected"

-- ** Other functions

-- | Arity of a refinement type
arity :: RefType -> Integer
arity (ArrType _ _ tp) = 1 + arity tp
arity (RefType {}) = 0

-- | defaultRef tp := {VV : tp | True}
defaultRef :: BaseType -> RefType
defaultRef tp = RefType "VV" tp ttTm

-- | arrs(R) := (x_i:R_i)_{i ≤ n} -> R' where n is maximal
arrs :: RefType -> ([(Id, RefType)], (Id, BaseType, Reft))
arrs (RefType x a r) = ([], (x, a, r))
arrs (ArrType x tpx tp) = ((x, tpx) :) `first` arrs tp

-- | tpArgs(x_i:R_i|r_i)_{i ≤ n} -> R) = [x_i]_{i ≤ n}
tpArgs :: RefType -> [Id]
tpArgs = map fst . fst . arrs

-- | tpArgsArLoc((x_i:R_i|r_i)_{i ≤ n} -> R) = [Var x_i ar(R_i) Local]_{i ≤ n}
-- Used to give the initial patterns on the parameters of a function
tpArgsArLoc :: RefType -> [Reft]
tpArgsArLoc = map (\(x, tp) -> Var x (arity tp) Local) . fst . arrs

-- | Flattens an application
apps :: Reft -> (Reft, [Reft])
apps (App tm1 tm2) = let (hd, args) = apps tm1 in (hd, args ++ [tm2])
apps tm = (tm, [])

-- | Head variable of an application (also when projected)
headVar :: Reft -> Maybe Id
headVar r = case fst (apps r) of
  Var f _ _ -> Just f
  Proj (Var f _ _) -> Just f
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
isValue (Proj r) = isValue r
isValue (Var _ _ Global; Neg {}; Bop {}) = False

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

-- | Rename all the arguments of an arrow:
--
-- > renameParams([y1,y2], x1:{x1:B | True} -> x2:{x2:B | x1 == x2} -> {v:B | v = x1 + x2})
-- >   = y1:{x1:B | True} -> y2:{x2:B | y1 == x2} -> {v:B | v = y1 + y2}
renameParams :: [Id] -> RefType -> RefType
renameParams = aux []
  where
    aux :: [(Id, Id)] -> [Id] -> RefType -> RefType
    aux σ _ tp@(RefType {}) = renames σ tp
    aux σ [] tp = renames σ tp
    aux σ (y : ys) (ArrType x tpx tp)
      | x `notElem` freeVars tp || x == y =
          ArrType y (renames σ tpx) (aux σ ys tp)
    -- TODO: handle by renaming
    aux _ (y : _) tp0@(ArrType x _ tp)
      | y `elem` freeVars tp =
          error . render $ "Name clash while renaming variable" <+> text x <+> "to" <+> text y <+> "in" <+> pPrint tp0
    aux σ (y : ys) (ArrType x tpx tp) =
      ArrType y (renames σ tpx) (aux ((y, x) : σ) ys tp)

-- Remove projections around the *first-order* arguments of the constructor, in
-- a context where FO arguments are given unrefined types
-- This function should be used at top-level, where only variables appear inside projections
removeFOArgProjs :: RefType -> RefType
removeFOArgProjs (ArrType x tpx tp) = ArrType x (removeFOArgProjs tpx) (removeFOArgProjs tp)
removeFOArgProjs (RefType y a reft) = RefType y a (aux reft)
  where
    aux (Proj (Var x n Local)) = Var x n Local
    aux p@(Proj _) =
      error $ "Calculus.removeFOArgProjs should only be used at top-level, when projections are made only on local FO variable. Found term: " ++ prettyShow p
    aux r@(Var {}; StringLit {}; IntLit {}; FloatLit {}; DC {}) = r
    aux (App r1 r2) = App (aux r1) (aux r2)
    aux (Neg r) = Neg (aux r)
    aux (Bop bop r1 r2) = Bop bop (aux r1) (aux r2)
    aux (QMark r rh rp) = QMark (aux r) (aux rh) (aux rp)
    aux (Pop pop r1 r2) = Pop pop (aux r1) (aux r2)
    aux (Sub {}; Inj {}) = error "Subsumption or injection cast found in type refinement."

-- * Typeclass related to free variables

-- To use Sets with Localization inside
instance Ord Localization where
  -- since we do not care about getting the branch pattern with
  -- freeVarsArLoc, we do not compare it
  compare Local Local = EQ
  compare Global Global = EQ
  compare (Recursive ih1 _) (Recursive ih2 _) = compare ih1 ih2
  compare Local (Global; Recursive _ _) = LT
  compare Global (Recursive _ _) = LT
  compare (Recursive _ _) (Global; Local) = GT
  compare Global Local = GT

class HasVars a where
  -- | Return the free variables with their arity and localization
  freeVarsArLoc :: a -> Set (Id, (Integer, Localization))

  -- | Return the bound variables with their arity (they are all local)
  boundVarsArLoc :: a -> Set (Id, Integer)

  -- | subst r x tm is {r/x}tm
  subst :: Reft -> Id -> a -> a

freeVars :: (HasVars a) => a -> Set Id
freeVars tm = Set.map fst $ freeVarsArLoc tm

boundVars :: (HasVars a) => a -> Set Id
boundVars tm = Set.map fst $ freeVarsArLoc tm

-- | return a variable fresh wrt to the free and bound variables in the second argument
fresh :: (HasVars a) => Id -> a -> Id
fresh x tm = freshVar x (freeVars tm `Set.union` boundVars tm)

-- | Rename the second argument to the first in the third
--
-- > rename y x tm = {y/x}tm
rename :: (HasVars a) => Id -> Id -> a -> a
rename new old tm =
  let olds = Set.filter ((==) old . fst) $ freeVarsArLoc tm
   in if Set.size olds == 0
        then tm
        else
          -- We assume a single occurrence of `old` and retrieve its arity and
          -- localization to build a Var
          let (_, (ar, loc)) = Set.elemAt 0 olds
           in subst (Var new ar loc) old tm

-- | renameFresh(x,tm) gives x a fresh name in tm
renameFresh :: (HasVars a) => Id -> a -> a
renameFresh x tm = rename (fresh x tm) x tm

-- | Apply a list of renamings, starting from the right
renames :: (HasVars a) => [(Id, Id)] -> a -> a
renames = flip (foldr (uncurry rename))

-- | Apply a list of substitutions, starting from the right
substs :: (HasVars a) => [(Reft, Id)] -> a -> a
substs = flip (foldr (uncurry subst))

instance HasVars Reft where
  freeVarsArLoc (Var x ar loc) = Set.singleton (x, (ar, loc))
  freeVarsArLoc (App hd arg) = freeVarsArLoc [hd, arg]
  freeVarsArLoc (Bop _ r1 r2) = freeVarsArLoc [r1, r2]
  freeVarsArLoc (Neg r) = freeVarsArLoc r
  freeVarsArLoc (StringLit _; IntLit _; FloatLit _; DC _) = Set.empty
  freeVarsArLoc (QMark r rh rp) = freeVarsArLoc [r, rh, rp]
  freeVarsArLoc (Pop _ r1 r2) = freeVarsArLoc [r1, r2]
  freeVarsArLoc (Sub r from to) = freeVarsArLoc r `Set.union` freeVarsArLoc [from, to]
  freeVarsArLoc (Inj r tp) = freeVarsArLoc r `Set.union` freeVarsArLoc tp
  freeVarsArLoc (Proj r) = freeVarsArLoc r

  -- Empty on unelaborated refinements, but has the bound variables of the types in casts
  boundVarsArLoc (Var {}; StringLit _; IntLit _; FloatLit _; DC _) = Set.empty
  boundVarsArLoc (App hd arg) = boundVarsArLoc [hd, arg]
  boundVarsArLoc (Bop _ r1 r2) = boundVarsArLoc [r1, r2]
  boundVarsArLoc (Neg r) = boundVarsArLoc r
  boundVarsArLoc (QMark r rh rp) = boundVarsArLoc [r, rh, rp]
  boundVarsArLoc (Pop _ r1 r2) = boundVarsArLoc [r1, r2]
  boundVarsArLoc (Sub r from to) = boundVarsArLoc r `Set.union` boundVarsArLoc [from, to]
  boundVarsArLoc (Inj r tp) = boundVarsArLoc r `Set.union` boundVarsArLoc tp
  boundVarsArLoc (Proj r) = boundVarsArLoc r

  subst r' x r0 = case r0 of
    Var y _ _ | y == x -> r'
    (Var {}; StringLit _; IntLit _; FloatLit _; DC _) -> r0
    App h arg -> App (subst r' x h) (subst r' x arg)
    Bop bop r1 r2 -> Bop bop (subst r' x r1) (subst r' x r2)
    Neg r -> Neg $ subst r' x r
    QMark r rh rp -> QMark (subst r' x r) (subst r' x rh) (subst r' x rp)
    Pop pop r1 r2 -> Pop pop (subst r' x r1) (subst r' x r2)
    Sub r tps tpt -> Sub (subst r' x r) (subst r' x tps) (subst r' x tpt)
    Inj r tp -> Inj (subst r' x r) (subst r' x tp)
    Proj r -> Proj (subst r' x r)

instance HasVars Expr where
  freeVarsArLoc (Reft r) = freeVarsArLoc r
  freeVarsArLoc (Let x tp ex e) =
    freeVarsArLoc tp `Set.union` Set.delete (x, (maybe 0 arity tp, Local)) (freeVarsArLoc [ex, e])
  freeVarsArLoc (Case r branches _) =
    freeVarsArLoc r `Set.union` Set.unions (map fvBranch branches)
    where
      fvBranch ((_, ys), ebr) =
        let ysSet = foldr (\(y, _) -> Set.insert (y, (0, Local))) Set.empty ys
         in freeVarsArLoc ebr Set.\\ ysSet

  boundVarsArLoc (Reft r) = boundVarsArLoc r
  boundVarsArLoc (Let x tp ex e) =
    Set.singleton (x, maybe 0 arity tp) `Set.union` boundVarsArLoc tp `Set.union` boundVarsArLoc [ex, e]
  boundVarsArLoc (Case r branches _) =
    boundVarsArLoc r `Set.union` Set.unions (map bvBranch branches)
    where
      bvBranch ((_, ys), e) =
        Set.fromList (map (second $ const 0) ys) `Set.union` boundVarsArLoc e

  subst r x e = case e of
    Reft re -> Reft $ subst r x re
    Let y tp ey e' | y == x -> Let y (subst r x tp) (subst r x ey) e'
    Let y tp ey e'
      | y `Set.member` freeVars r && x `Set.member` freeVars e' ->
          let z = freshVar y fvre in Let z (subst r x tp) (subst r x ey) (subst r x $ rename z y e')
    Let y tp ey e' -> Let y (subst r x tp) (subst r x ey) (subst r x e')
    Case r' branches genVars ->
      Case (subst r x r') (map substBranch branches) genVars
      where
        substBranch br@((_, ys), ebr)
          | x `elem` map fst ys || maybe True (notElem x . freeVars) ebr = br
        substBranch ((c, ys), ebr) =
          let freshYs = foldr freshVars [] ys
              α = filter (uncurry (/=)) $ zipWith (\(y, _) z -> (z, y)) ys freshYs
              ys' = zipWith (\(_, b) z -> (z, b)) ys freshYs
           in ((c, ys'), subst r x $ renames α ebr)
          where
            freshVars (y, _) vars =
              if y `elem` freeVars r
                then freshVar y (fvre `Set.union` Set.fromList vars) : vars
                else y : vars
    where
      fvre = freeVars r `Set.union` freeVars e

instance HasVars RefType where
  freeVarsArLoc (RefType x _ r) = Set.delete (x, (0, Local)) (freeVarsArLoc r)
  freeVarsArLoc (ArrType x tpx tp) =
    freeVarsArLoc tpx `Set.union` Set.delete (x, (arity tpx, Local)) (freeVarsArLoc tp)

  boundVarsArLoc (RefType x _ r) = Set.singleton (x, 0) `Set.union` boundVarsArLoc r
  boundVarsArLoc (ArrType x tpx tp) =
    Set.singleton (x, arity tpx) `Set.union` boundVarsArLoc [tpx, tp]

  subst r x tp = case tp of
    RefType y _ _ | y == x -> tp
    RefType y b reft -> RefType y b $ subst r x reft
    ArrType y tpy tp' | y == x -> ArrType y (subst r x tpy) tp'
    ArrType y tpy tp'
      | y `Set.member` freeVars r && x `Set.member` freeVars tp' ->
          let z = freshVar y (freeVars r `Set.union` freeVars tp)
           in ArrType z (subst r x tpy) (subst r x $ rename z y tp')
    ArrType y tpy tp' -> ArrType y (subst r x tpy) (subst r x tp')

instance (HasVars a) => HasVars [a] where
  freeVarsArLoc tms = Set.unions $ map freeVarsArLoc tms
  boundVarsArLoc tms = Set.unions $ map boundVarsArLoc tms
  subst r x = fmap (subst r x)

instance (HasVars a) => HasVars (Maybe a) where
  freeVarsArLoc = maybe Set.empty freeVarsArLoc
  boundVarsArLoc = maybe Set.empty boundVarsArLoc
  subst r x = fmap (subst r x)

-- * Equality instance using α-renaming

instance Eq RefType where
  tp1@(RefType x tpx rx) == tp2@(RefType y tpy ry) =
    let z = fresh x [tp1, tp2]
        (α1, α2) = if x /= y then ([(z, x)], [(z, y)]) else ([], [])
     in tpx == tpy && renames α1 rx == renames α2 ry
  tp1@(ArrType x tpx tp1') == tp2@(ArrType y tpy tp2') =
    let z = fresh x [tp1, tp2]
        (α1, α2) = if x /= y then ([(z, x)], [(z, y)]) else ([], [])
     in tpx == tpy && renames α1 tp1' == renames α2 tp2'
  _ == _ = False

instance Eq Expr where
  Reft r1 == Reft r2 = r1 == r2
  e1@(Let x tpx ex e1') == e2@(Let y tpy ey e2') =
    let z = fresh x [e1, e2]
        (α1, α2) = if x /= y then ([(z, x)], [(z, y)]) else ([], [])
     in tpx == tpy && ex == ey && renames α1 e1' == renames α2 e2'
  e1@(Case r1 alts1 genVars1) == e2@(Case r2 alts2 genVars2) =
    -- Equality is sensitive to the order of the alternatives
    r1 == r2 && all eqBranch (zip alts1 alts2) && genVars1 == genVars2
    where
      eqBranch (((c1, ys1), ebr1), ((c2, ys2), ebr2)) =
        let freshYs = foldr freshVars [] (zip ys1 ys2)
            α ys = filter (uncurry (/=)) $ zipWith (\(y, _) z -> (z, y)) ys freshYs
         in c1 == c2 && renames (α ys1) ebr1 == renames (α ys2) ebr2
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

{- -- | Prints a function applied to arguments with parenthesis if needed
--
-- > pPrintFunc p "f" [x, y] = f (x, y)
pPrintFunc :: Rational -> String -> [Doc] -> Doc
pPrintFunc _ f [] = text f
pPrintFunc p f args =
  maybeParens (p > appPrec) $ text f <+> parens (hsep $ punctuate comma args) -}

-- ** Instances

instance Pretty Builtin where
  pPrint = text . show

instance Pretty BaseType where
  pPrint (Builtin b) = pPrint b
  pPrint (TC tc) = text tc

instance Pretty RefType where
  pPrintPrec _ _ (RefType _ a r) | r == ttTm = braces $ pPrint a
  pPrintPrec _ _ (RefType _ a r) | a == unitTp = braces . braces $ pPrint r
  pPrintPrec _ _ (RefType x a r) =
    braces (text x <> colon <+> pPrint a <+> char '|' <+> pPrint r)
  pPrintPrec l p (ArrType x tpx tp) =
    maybeParens (p > arrPrec) $ sep [text x <> colon <+> pPrintPrec l (arrPrec + 1) tpx, "->" <+> pPrintPrec l arrPrec tp]

instance Pretty Decl where
  pPrint (Data tc constrs) =
    sep [ppTC, nest identNb . sep $ map (\dc -> char '|' <+> ppConstr dc) constrs]
    where
      ppTC = "data" <+> text tc <+> ":="
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

instance Pretty Reft where
  -- pPrintPrec _ _ (Var x ar loc) = text x <> char '/' <> parens (integer ar <> comma <> pPrint loc)
  pPrintPrec _ _ (Var x _ _) = text x
  pPrintPrec _ _ (StringLit s) = quotes $ text s
  pPrintPrec _ _ (IntLit i) = integer i
  pPrintPrec _ _ (FloatLit f) = double f
  pPrintPrec _ _ (DC c) = text c
  pPrintPrec l p (App r1 r2) =
    maybeParens (p > appPrec) $ pPrintPrec l p r1 <+> pPrintPrec l (appPrec + 1) r2
  pPrintPrec l p (Neg r) =
    maybeParens (p > appPrec) $ "not" <+> pPrintPrec l (appPrec + 1) r
  pPrintPrec l p (Bop bop r1 r2) =
    maybeParens (p > bopPrec bop) $ pPrintPrec l (bopPrec bop) r1 <+> pPrint bop <+> pPrintPrec l (bopPrec bop) r2
  pPrintPrec l p (QMark r rh rp) =
    maybeParens (p > appPrec) $ pPrintPrec l p r <+> char '?' <+> parens (pPrint rh <+> "proves" <+> pPrint rp)
  pPrintPrec l p (Pop pop r1 r2) =
    maybeParens (p > popPrec pop) $ pPrintPrec l (popPrec pop) r1 <+> pPrint pop <+> pPrintPrec l (popPrec pop) r2
  pPrintPrec _ p (Sub r from to) =
    maybeParens (p > appPrec) $ "sub" <+> parens (hsep $ punctuate comma (pPrint r : map pPrint [from, to]))
  pPrintPrec _ p (Inj r tp) =
    maybeParens (p > appPrec) $ "inj" <+> parens (pPrint r <> comma <+> pPrint tp)
  pPrintPrec l p (Proj r) =
    maybeParens (p > appPrec) $ "proj" <+> pPrintPrec l (appPrec + 1) r

instance Pretty Localization where
  pPrint Local = char 'L'
  pPrint Global = char 'G'
  pPrint (Recursive indVar _) = char 'Y' <+> text indVar

instance Pretty DesState where
  pPrint = text . show

instance Show Bop where
  show op = case op of
    Mod -> "`mod`"
    Plus -> "+"
    Minus -> "-"
    Times -> "*"
    Div -> "/"
    Eq -> "=="
    Neq -> "/="
    Leq -> "<="
    Geq -> ">="
    Lt -> "<"
    Gt -> ">"
    And -> "&&"
    Or -> "||"
    Impl -> "=>"
    Iff -> "<=>"

instance Pretty Bop where
  pPrint = text . show

instance Show ProofOp where
  show PEq = "==="
  show PLeq = "=<="
  show PGeq = "=>="

instance Pretty ProofOp where
  pPrint = text . show

traceFunc :: Id -> [Doc] -> Bool
traceFunc f args =
  let doc = text f <> parens (hsep $ punctuate comma args)
   in trace (render doc) False
