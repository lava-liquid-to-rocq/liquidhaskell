{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OrPatterns #-}

-- | Grammars, printer and suable functions for ILH
module Lava.Calculus where

import Data.Bifunctor (first, second)
import Data.Data
-- to avoid errors if forgetting Map.lookup
import Data.Set (Set)
import qualified Data.Set as Set
import Lava.Util hiding (Id, sub, subst)
import Prelude hiding (lookup)

-- * The grammar

type Id = String

-- ** Types

-- | Builtin types
-- In Fixpoint, we have the Constant types Integer, Double and Text. There, from GHC.Core,
-- Floats are stored as Double, and Chars and Strings are converted to Text (we switch back to
-- Strings for simplicity). Other GHC.Core literals are not relevant for us
--
-- > B ::= Integer | Double | String
data Builtin = Integer | Double | String deriving (Data, Eq)

-- | Base Types
--
-- > A ::= B | TC
data BaseType = Builtin Builtin | TC Id deriving (Data, Eq)

-- | Refinement types
--
-- > R ::= {x: A | r} | x:Rx -> R
data RefType
  = RefType {argName :: Id, argTp :: BaseType, argRef :: Reft}
  | ArrType {parName :: Id, parTp :: RefType, retTp :: RefType}
  deriving (Data, Eq)

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
  deriving (Data, Eq)

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
    Case Reft [((Id, [(Id, Bool)]), Maybe Expr)] IndCase
  deriving (Data, Eq)

-- | Simple LH terms including formulas.
--   Terms of this type can occur as (sub)terms in refinements
--
-- > r ::= x/(ar,loc)
-- >     | lit ∈ B
-- >     | C
-- >     | r r
-- >     | ¬r
-- >     | r `op` r
-- >     | r ? r
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
  deriving (Data, Eq)

-- | Localization of the variables
--
-- loc ::= L | G | Y
data Localization = Local | Global | Recursive BranchPattern deriving (Data, Eq)

-- | Branch pattern: patterns of the current branch obtained
-- by destructing the parameters of the function.
-- This is an additional parameter of many of the typing functions, and is
-- necessary for the translation of case and recursive applications with tactics
type BranchPattern = [Reft]

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
  deriving (Data, Eq)

-- | Binary proof operators
--
-- > pop ::= === | =<= | =>=
data ProofOp = PEq | PLeq | PGeq deriving (Data, Eq)

-- | Whether a case must be translated to induct or destruct.
-- In the first option, we store the names of variables to generalize
data IndCase = Induct [Id] | Destruct deriving (Data, Eq)

-- Builtin type and data constructors

{- ORMOLU_DISABLE -}
ttTmName = "true"
ttTm = DC ttTmName
ffTmName = "false"
ffTm = DC ffTmName
boolTpName = "Bool"
boolTp = TC boolTpName
unitTmName = "unit"
unitTm = DC unitTmName
unitTpName = "Unit"
unitTp = TC unitTpName
builtinDCs = [ttTm, ffTm, unitTm]
builtinTCs = [boolTp, unitTp]
{- ORMOLU_ENABLE -}

-- * Functions on the terms

-- | Arity of a refinement type
arity :: RefType -> Integer
arity (ArrType _ _ tp) = 1 + arity tp
arity (RefType {}) = 0

-- | defaultRef tp := {VV : tp | True}
defaultRef :: BaseType -> RefType
defaultRef tp = RefType "VV" tp ttTm

-- | arrs(R) := (x_i:R_i)_{i ≤ n} -> R' where n is maximal
arrs :: RefType -> ([(Id, RefType)], RefType)
arrs tp@(RefType {}) = ([], tp)
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

-- | Gives the bop corresponding to a pop
popToBop :: ProofOp -> Bop
popToBop PEq = Eq
popToBop PLeq = Leq
popToBop PGeq = Geq

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

-- Remove projections around the *first-order* arguments of the constructor, in
-- a context where FO arguments are given unrefined types
-- This function should be used at top-level, where only variables appear inside projections
removeFOArgProjs (ArrType x tpx tp) = ArrType x (removeFOArgProjs tpx) (removeFOArgProjs tp)
removeFOArgProjs (RefType x a r) = RefType x a (aux r)
  where
    aux (Proj (Var x 0 Local)) = Var x 0 Local
    aux (Proj x) = x
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
  compare l1 l2 | l1 == l2 = EQ
  compare Local (Global; Recursive _) = LT
  compare Global (Recursive _) = LT
  compare (Recursive _) (Global; Local) = GT
  compare Global Local = GT

class HasVars a where
  -- | Return the free variables with their arity and localization
  freeVarsArLoc :: a -> Set (Id, (Integer, Localization))

  {- boundVars :: a -> Set Id -}

  -- | subst r x tm is {r/x}tm
  subst :: Reft -> Id -> a -> a

freeVars :: (HasVars a) => a -> Set Id
freeVars tm = Set.map fst $ freeVarsArLoc tm

-- | Rename `old` to `new` in `tm`
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

-- | Apply a list of renamings, starting from the right
renames :: (HasVars a) => [(Id, Id)] -> a -> a
renames = flip (foldr (uncurry rename))

-- | Apply a list of substitutions, starting from the right
substs :: (HasVars a) => [(Reft, Id)] -> a -> a
substs = flip (foldr (uncurry subst))

instance HasVars Reft where
  freeVarsArLoc (Var x ar loc) = Set.singleton (x, (ar, loc))
  freeVarsArLoc (App hd arg) = freeVarsArLoc hd `Set.union` freeVarsArLoc arg
  freeVarsArLoc (Bop _ r1 r2) = freeVarsArLoc r1 `Set.union` freeVarsArLoc r2
  freeVarsArLoc (Neg r) = freeVarsArLoc r
  freeVarsArLoc (StringLit _; IntLit _; FloatLit _; DC _) = Set.empty
  freeVarsArLoc (QMark r rh rp) = freeVarsArLoc r `Set.union` (freeVarsArLoc rh `Set.union` freeVarsArLoc rp)
  freeVarsArLoc (Pop _ r1 r2) = freeVarsArLoc r1 `Set.union` freeVarsArLoc r2
  freeVarsArLoc (Sub r _ _) = freeVarsArLoc r
  freeVarsArLoc (Inj r _) = freeVarsArLoc r
  freeVarsArLoc (Proj r) = freeVarsArLoc r

  {- boundVars _ = Set.empty -}

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
    Set.unions
      [maybe Set.empty freeVarsArLoc tp, freeVarsArLoc ex, Set.delete (x, (maybe 0 arity tp, Local)) (freeVarsArLoc e)]
  freeVarsArLoc (Case r branches _) =
    freeVarsArLoc r `Set.union` Set.unions (map fvBranch branches)
    where
      fvBranch (_, Nothing) = Set.empty
      fvBranch ((c, ys), Just ebr) =
        let ysSet = foldr (\(y, _) -> Set.insert (y, (0, Local))) Set.empty ys
         in freeVarsArLoc ebr Set.\\ ysSet

  {- boundVars (Reft r) = Set.empty
  boundVars (Let x _ ex e) = Set.insert x (boundVars ex `Set.union` boundVars e)
  boundVars (Case _ branches) = Set.unions (map (Set.fromList . snd . fst) branches) -}

  subst r x e = case e of
    Reft re -> Reft $ subst r x re
    Let y _ _ e'
      | y `Set.member` freeVars r && x `Set.member` freeVars e' -> error err
    Let y tp ey e' | y == x -> Let y (subst r x <$> tp) (subst r x ey) e'
    Let y tp ey e' -> Let y (subst r x <$> tp) (subst r x ey) (subst r x e')
    Case r' branches ind ->
      Case (subst r x r') (map substBranch branches) ind
      where
        substBranch ((_, ys), _) | not (Set.fromList (map fst ys) `Set.disjoint` freeVars r) = error err
        substBranch br@((_, ys), _) | x `elem` map fst ys = br
        substBranch ((c, ys), ebr) = ((c, ys), subst r x <$> ebr)
    where
      err = "Substitution {" ++ show r ++ "/" ++ x ++ "}(" ++ show e ++ ") is not sound because of variable capture."

instance HasVars RefType where
  freeVarsArLoc (RefType x tp r) = Set.delete (x, (0, Local)) (freeVarsArLoc r)
  freeVarsArLoc (ArrType x tpx tp) = freeVarsArLoc tpx `Set.union` Set.delete (x, (arity tpx, Local)) (freeVarsArLoc tp)

  {- boundVars (RefType x tp r) = Set.empty
  boundVars (ArrType x tpx tp) = Set.insert x (boundVars tpx `Set.union` boundVars tp) -}
  subst r x tp = case tp of
    RefType y _ _ | y == x -> tp
    RefType y b reft -> RefType y b $ subst r x reft
    ArrType y _ tp'
      | y `Set.member` freeVars r && x `Set.member` freeVars tp' ->
          error $ "Substitution {" ++ show r ++ "/" ++ x ++ "}(" ++ show tp ++ ") is not sound because of variable capture."
    ArrType y tpx tp' | y == x -> ArrType y (subst r x tpx) tp'
    ArrType y tpx tp' -> ArrType y (subst r x tpx) (subst r x tp')

instance (HasVars a) => HasVars [a] where
  freeVarsArLoc tms = Set.unions $ map freeVarsArLoc tms
  subst r x = fmap (subst r x)

instance (HasVars a) => HasVars (Maybe a) where
  freeVarsArLoc = maybe Set.empty freeVarsArLoc
  subst r x = fmap (subst r x)

-- * Printer for the grammar

instance Show Builtin where
  show b = undefined

instance Show BaseType where
  show tp = undefined

{- show tp = case tp of
  TDat "()" -> error "Unexpectedly found reserved identifier () as typename"
  TDat a -> a
  Builtin b -> show b
  Pi (x, rA) rB -> "(" ++ x ++ ": " ++ show rA ++ ") -> " ++ show rB -}

instance Show RefType where
  show = undefined

{- show (RefType x a r) = "{" ++ x ++ ": " ++ show a ++ " | " ++ show r ++ "}"
show (ArrType args ret) = unwords (map (\(x, r) -> "(" ++ x ++ ": " ++ show r ++ ") ->") args) ++ show ret -}

instance Show Decl where
  show d = case d of
    Data tc constrs -> "data " ++ tc ++ " = " ++ intercalate " | " (map show constrs)
    Definition f tp e _ -> "Def " ++ f ++ " :: " ++ show tp ++ " := " ++ showNewline 1 ++ prettyPrint 1 e

instance PrettyPrintable (Id, [Id], Expr) where
  -- \| pretty prints a branch of a Case or InductTerm
  prettyPrint indent (c, cargs, def) = c ++ " " ++ unwords cargs ++ " |-> " ++ defS
    where
      defS = case def of
        match@Case {} -> showNewline (indent + 1) ++ prettyPrint (indent + 1) match
        _ -> show def

instance PrettyPrintable Expr where
  -- \| pretty prints an Expr, printing branches of match expressions in separate indented lines
  prettyPrint indent e = undefined {- case e of
                                   BasicTerm t -> show t
                                   Undefined -> "undefined"
                                   Case x branches _ -> "case " ++ show x ++ " of " ++ showNewline (indent + 1) ++ showIndent " | " False (indent + 1) branches
                                   Let x tp def e' -> "let " ++ var ++ " := " ++ show def ++ " in " ++ show e'
                                     where
                                       var = maybe x (\tp' -> "(" ++ x ++ ": " ++ show tp' ++ ")") tp
                                   Lambda x e' -> "λ" ++ x ++ ". " ++ show e'
                                   SEqn s t hint -> showP s ++ (if hint == BasicTerm unitTm then "" else " ? " ++ showP hint) ++ " === " ++ showP t
                                   QMark z t -> showP z ++ " ? " ++ showP t
                                   Annot e' tp -> "(" ++ show e' ++ " :: " ++ show tp ++ ")" -}

instance Show Expr where
  show = prettyPrint 1

instance Show Reft where
  show = undefined

{- show (Neg r) = "not " ++ addParens (show r)
show (Bop b s t) = show s ++ " " ++ showP b ++ " " ++ showP t
show (Var x) = x
show (App f ts) = unwords $ map showP (f : ts)
show (StringLit s) = "\"" ++ s ++ "\""
show (IntLit n) = "I " ++ show n
show (FloatLit f) = "F " ++ show f -}

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
