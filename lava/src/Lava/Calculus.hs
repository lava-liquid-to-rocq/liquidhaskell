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

-- | Bas Types
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
-- >     | case r of (C x* |-> (e | unreachable))*
data Expr
  = -- | Refinement used as expression
    Reft Reft
  | -- | Let with type annotation. binds the dependent variables in R
    --   for lets in the code, we can always get an annotation, but we also create some for ANF
    Let Id (Maybe RefType) Expr Expr
  | -- | Pattern matching (includes conditionals), with Maybe for optional branches
    Case Reft [((Id, [Id]), Maybe Expr)]
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
data Localization = Local | Global | Recursive deriving (Data, Eq)

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

-- | Patterns
--
-- > p ::= x | C p*
data Pattern = VarPat Id | TCPat Id [Pattern] deriving (Data, Eq)

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

-- * Functions on the grammar

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

-- | Flattens an application
apps :: Reft -> (Reft, [Reft])
apps (App tm1 tm2) = let (hd, args) = apps tm1 in (hd, args ++ [tm2])
apps tm = (tm, [])

-- | Returns the application corresponding to the pattern of a case
-- Since we do not have higher-order constructors, all variables are of arity 0
matchToApp :: (Id, [Id]) -> Reft
matchToApp (c, ys) = foldr App (DC c) (map (\y -> Var y 0 Local) ys)

-- | Translates a pattern to a Reft, similar to  matchToApp
-- This function must not be called on a pattern “x” since this one can be a
-- higher-order argument
patternToReft :: Pattern -> Reft
patternToReft (VarPat x) = Var x 0 Local
patternToReft (TCPat c pats) = foldr App (DC c) (map patternToReft pats)

-- * Typeclass related to free variables

class HasVars a where
  freeVars :: a -> Set Id
  boundVars :: a -> Set Id
  subst :: Reft -> Id -> a -> a

instance HasVars Reft where
  freeVars (Var x _ _) = Set.singleton x
  freeVars (App hd arg) = freeVars hd `Set.union` freeVars arg
  freeVars (Bop _ r1 r2) = freeVars r1 `Set.union` freeVars r2
  freeVars (Neg r) = freeVars r
  freeVars (StringLit _; IntLit _; FloatLit _; DC _) = Set.empty
  freeVars (QMark r rh rp) = freeVars r `Set.union` (freeVars rh `Set.union` freeVars rp)
  freeVars (Pop _ r1 r2) = freeVars r1 `Set.union` freeVars r2
  freeVars (Sub r _ _) = freeVars r
  freeVars (Inj r _) = freeVars r
  freeVars (Proj r) = freeVars r

  boundVars _ = Set.empty

  subst r' x r0 = case r0 of
    Var y _ _ | y == x -> r'
    (Var {}; StringLit _; IntLit _; FloatLit _; DC _) -> r0
    App h arg -> App (subst r' x h) (subst r' x arg)
    Bop bop r1 r2 -> Bop bop (subst r' x r1) (subst r' x r2)
    Neg r -> Neg $ subst r' x r
    QMark r rh rp -> QMark (subst r' x r) (subst r x rh) (subst r x rp)
    Pop pop r1 r2 -> Pop pop (subst r' x r1) (subst r' x r2)
    Sub r tps tpt -> Sub (subst r' x r) (subst r' x tps) (subst r' x tpt)
    Inj r tp -> Inj (subst r' x r) (subst r' x tp)
    Proj r -> Proj (subst r' x r)

instance HasVars Expr where
  freeVars (Reft r) = freeVars r
  freeVars (Let x tp ex e) = Set.unions [maybe Set.empty freeVars tp, freeVars ex, Set.delete x (freeVars e)]
  freeVars (Case r branches) =
    freeVars r
      `Set.union` Set.unions (map (\((c, ys), ebr) -> maybe Set.empty freeVars ebr Set.\\ Set.fromList ys) branches)

  boundVars (Reft r) = Set.empty
  boundVars (Let x _ ex e) = Set.insert x (boundVars ex `Set.union` boundVars e)
  boundVars (Case _ branches) = Set.unions (map (Set.fromList . snd . fst) branches)

  subst r x e = case e of
    Reft re -> Reft $ subst r x re
    Let y _ _ e'
      | y `Set.member` freeVars r && x `Set.member` freeVars e' ->
          error $ "Variable " ++ x ++ " cannot be substituted in " ++ show e ++ " where it is bound."
    Let y tp ey e' | y == x -> Let y (subst r x <$> tp) (subst r x ey) e'
    Let y tp ey e' -> Let y (subst r x <$> tp) (subst r x ey) (subst r x e')
    Case r' branches ->
      Case (subst r x r') (map substBranch branches)
      where
        substBranch ((_, ys), _)
          | not (Set.fromList ys `Set.disjoint` freeVars r) =
              error $ "Variable " ++ x ++ " cannot be substituted in " ++ show e ++ " where it is bound."
        substBranch br@((_, ys), _) | x `elem` ys = br
        substBranch ((c, ys), ebr) = ((c, ys), subst r x <$> ebr)

instance HasVars RefType where
  freeVars (RefType x tp r) = Set.delete x (freeVars r)
  freeVars (ArrType x tpx tp) = freeVars tpx `Set.union` Set.delete x (freeVars tp)
  boundVars (RefType x tp r) = Set.empty
  boundVars (ArrType x tpx tp) = Set.insert x (boundVars tpx `Set.union` boundVars tp)
  subst r x tp = case tp of
    RefType y _ _ | y == x -> tp
    RefType y b reft -> RefType y b $ subst r x reft
    ArrType y _ tp' | y `Set.member` freeVars r && x `Set.member` freeVars tp' -> undefined
    ArrType y tpx tp' | y == x -> ArrType y (subst r x tpx) tp'
    ArrType y tpx tp' -> ArrType y (subst r x tpx) (subst r x tp')

substs :: (HasVars a) => [(Reft, Id)] -> a -> a
substs [] x = x
substs ((r, y) : subs) x = substs subs $ subst r y x

-- * Printer for the grammar

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
