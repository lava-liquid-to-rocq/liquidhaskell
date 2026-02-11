{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}

-- | Grammars, printer and suable functions for ILH
module Lava.Calculus where

import Data.Bifunctor (first, second)
import Data.Data
import Lava.Util hiding (Id)
import Prelude hiding (lookup) -- to avoid errors if forgetting Map.lookup

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
    Case Reft [(Id, [Id], Maybe Expr)]
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
data Localization
  = Local
  | Global
  | Recursive
  deriving (Data, Eq)

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
data ProofOp
  = PEq
  | PLeq
  | PGeq
  deriving (Data, Eq)

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
