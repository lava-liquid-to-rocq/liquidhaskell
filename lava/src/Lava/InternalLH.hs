{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}

-- |
-- - Grammars, printer and suable functions for ILH
module Lava.InternalLH where

{- ( -- ** Declaration-level grammar
  LHDecl (..),

  -- ** Object-level grammar
  ArrType (..),
  RefType (..),
  LHType (..),
  BuildInTps (..),

  -- *** Simple term grammar
  Bop (..),
  LHSimpleTerm (..),

  -- *** Term grammar
  LHTerm (..),
  unitTm,
  ffTm,
  ttTm,
  boolTp,
  unitTp,
) -}

import Data.Bifunctor (first, second)
import Data.Data
import Lava.Util
import Prelude hiding (lookup) -- to avoid errors if forgetting Map.lookup

-- * The grammar

-- ** Types

-- | Supported LH builtin types (@b@)
-- In Fixpoint, we have the Constant types Integer, Double and Text. There, from GHC.Core,
-- Floats are stored as Double, and Chars and Strings are converted to Text (we switch back to
-- Strings for simplicity). Other GHC.Core literals are not relevant for us
data BuildInTps = Integer | Double | String deriving (Data, Eq, Show)

-- | LH types
--
-- > A ::= B | tc | (x: R) → R -- [LP] I want to remove Pi
data LHType = Buildin BuildInTps | TDat Id | Pi (Id, RefType) RefType deriving (Data, Eq)

-- | Simply refined top-level arguments (to functions, data constructors, ...)
--
-- > R ::= {x: A | r}
data RefType = RefType {argName :: Id, argTp :: LHType, argRef :: LHSimpleTerm} deriving (Data, Eq)

-- | N-ary arrow types. Subsume RefType, but not always allowed
--
-- > W ::= x1:R1 → … → xn:Rn → R  --  n ≥ 0
data ArrType = ArrType {argsTps :: [(Id, RefType)], retTp :: RefType} deriving (Data, Eq)

-- ** Declaration-level grammar

-- | Modules
-- M ::= module x where D*
data LHModule = LHModule Id [LHDecl]

-- | Declarations
--
-- > d ::= import x
-- >     | data tc (c :: W)*
-- >     | (refl) Def f :: W := e
data LHDecl
  = -- | imported modules
    Import Id [LHDecl]
  | -- | type constructor: name, (optional) measure (not supported yet), branches with (constructor name, type)
    Data Id [(Id, ArrType)]
  | -- | (function) definition: name, type, body, is it reflected
    Definition Id ArrType LHTerm Bool
  deriving (Data, Eq)

-- | General LH terms
--
-- > e ::= r | (rec) case x of (| c y* |-> e)*
-- >      | let x := e in e
-- >      | if r then e else e
-- >      | undefined
-- >      | r === r ? e
-- >      | e ? e
data LHTerm
  = BasicTerm LHSimpleTerm
  | -- | type annotation
    Annot LHTerm RefType
  | -- | pattern matches, the flag indicates the presence of recursive calls
    Case LHSimpleTerm [(Id, [Id], LHTerm)] Bool
  | -- | special case of a pattern match on type bool
    Let Id LHTerm LHTerm
  | Lambda Id LHTerm
  | -- | represents the "missing term" in a "missing branch" in a match, where the case is provably redundant (as checked by LH)
    Undefined
  | SEqn LHSimpleTerm LHSimpleTerm LHTerm
  | QMark LHTerm LHTerm
  deriving (Data, Eq)

-- | Simple LH terms including formulas.
--   Terms of this type can occur as (sub)terms in refinements
--
-- > r ::= x
-- >     | lit ∈ B
-- >     | r r*
-- >     | r op r | ¬r
data LHSimpleTerm
  = Var Id -- TODO: it would be nice to separate constructors from variables
  | StringLit String
  | IntLit Integer
  | FloatLit Double
  | App LHSimpleTerm [LHSimpleTerm] -- TODO: for now at least, can be restricted to Id -> trouble when changing because of appsuable
  | Bop Bop LHSimpleTerm LHSimpleTerm
  | Neg LHSimpleTerm
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

ttTmName = "true"

ttTm = Var ttTmName

ffTmName = "false"

ffTm = Var ffTmName

boolTpName = "Bool"

boolTp = TDat boolTpName

unitTmName = "unit"

unitTm = Var unitTmName

unitTpName = "Unit"

unitTp = TDat unitTpName

builtinDCs = [ttTm, ffTm, unitTm]

builtinTCs = [boolTp, unitTp]

-- TODO: Definition of values, maybe add an arity to data constructors

-- * Printer for the grammar

instance Show LHType where
  show tp = case tp of
    TDat "()" -> error "Unexpectedly found reserved identifier () as typename"
    TDat a -> a
    Buildin b -> show b
    Pi (x, rA) rB -> "(" ++ x ++ ": " ++ show rA ++ ") -> " ++ show rB

instance Show ArrType where
  show (ArrType args ret) = unwords (map (\(x, r) -> "(" ++ x ++ ": " ++ show r ++ ") ->") args) ++ show ret

instance Show RefType where
  show (RefType x a r) = "{" ++ x ++ ": " ++ show a ++ " | " ++ show r ++ "}"

instance Show LHModule where
  show (LHModule x decls) = "module " ++ x ++ " where\n" ++ intercalate "\n" (map show decls)

instance Show LHDecl where
  show d = case d of
    Import m _ -> "import " ++ m
    Data tc constrs -> "data " ++ tc ++ " = " ++ intercalate " | " (map show constrs)
    Definition f tp e _ -> "Def " ++ f ++ " :: " ++ show tp ++ " := " ++ showNewline 1 ++ prettyPrint 1 e

instance PrettyPrintable (Id, [Id], LHTerm) where
  -- \| pretty prints a branch of a Case or InductTerm
  prettyPrint indent (c, cargs, def) = c ++ " " ++ unwords cargs ++ " |-> " ++ defS
    where
      defS = case def of
        match@Case {} -> showNewline (indent + 1) ++ prettyPrint (indent + 1) match
        _ -> show def

instance PrettyPrintable LHTerm where
  -- \| pretty prints an LHTerm, printing branches of match expressions in separate indented lines
  prettyPrint indent e = case e of
    BasicTerm t -> show t
    Undefined -> "undefined"
    Case x branches _ -> "case " ++ show x ++ " of " ++ showNewline (indent + 1) ++ showIndent " | " False (indent + 1) branches
    Let x def e' -> "let " ++ x ++ " := " ++ show def ++ " in " ++ show e'
    Lambda x e' -> "λ" ++ x ++ ". " ++ show e'
    SEqn s t hint -> showP s ++ (if hint == BasicTerm unitTm then "" else " ? " ++ showP hint) ++ " === " ++ showP t
    QMark z t -> showP z ++ " ? " ++ showP t
    Annot e' tp -> "(" ++ show e' ++ " :: " ++ show tp ++ ")"

instance Show LHTerm where
  show = prettyPrint 1

instance Show LHSimpleTerm where
  show (Neg r) = "not " ++ addParens (show r)
  show (Bop b s t) = show s ++ " " ++ showP b ++ " " ++ showP t
  show (Var x) = x
  show (App f ts) = unwords $ map showP (f : ts)
  show (StringLit s) = "\"" ++ s ++ "\""
  show (IntLit n) = "I " ++ show n
  show (FloatLit f) = "F " ++ show f

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

-- * Suable and AppSuable instances for productions in the grammar

instance AppSuable LHSimpleTerm LHSimpleTerm where
  findAndReplace p e = ifNotFullMatch p e $ case e of
    Neg f -> recurseFindAndRepl p Neg f
    App (App f ts) us -> findAndReplace p $ App f (ts ++ us)
    App f ts -> recurseFindAndReplApp p App f ts
    Bop op s t -> recurseFindAndRepl2 p (Bop op) s t
    Var y -> mapId Var y
    -- literals, Buildin
    _ -> unchanged
    where
      mapId op y = if isSubstOf p y then resRec [op y] id else unchanged

instance AppSuable LHType LHSimpleTerm where
  findAndReplace p (Pi (x, dom) codom) = resRec matches func
    where
      matches = [Var x | hasMatch p (Var x)] ++ findSubterm p dom ++ findSubterm p codom
      func r = Pi (renameO r x, replaceSubterm p r dom) (replaceSubterm p r codom)
      renameV y n = let Var v = replaceSubterm p (Var y) (Var n) in v
      renameO r n = case r of
        Var y -> renameV y n
        _ -> n
  findAndReplace _ _ = unchanged

instance AppSuable RefType LHSimpleTerm where
  findAndReplace p (RefType x tp ref) = resRec matches func
    where
      matches = [Var x | hasMatch p (Var x)] ++ findSubterm p tp ++ findSubterm p ref
      func r = RefType (renameO r x) (replaceSubterm p r tp) (replaceSubterm p r ref)
      renameV y n = let Var v = replaceSubterm p (Var y) (Var n) in v
      renameO r n = case r of
        Var y -> renameV y n
        _ -> n

instance AppSuable LHTerm LHSimpleTerm where
  findAndReplace p tm = {-trace (unwords ["findAndReplace", show p, show tm]) $ -} case tm of
    Annot t rt -> recurseFindAndRepl p (`Annot` rt) t
    BasicTerm t -> second (fmap $ \f r -> BasicTerm (f r)) $ findAndReplace p t
    Case (Var x) brs b -> resRec matches func
      where
        matches = [Var x | isSubstOf p x] ++ concatMap (\(c, argNms, e) -> map Var ([c | isSubstOf p c] ++ filter (isSubstOf p) argNms) ++ findSubterm p e) brs
        func r | isSubstOf p x = case r of
          -- \| we are replacing the variable matched on by another variable, i.e. just renamingthe variable
          Var v_r -> Case (Var v_r) (map (\(c, argNms, expr) -> (renameVar r c, map (renameVar r) argNms, replaceSubterm p r expr)) brs) b
          -- \| we cannot replace the variable matched on by an arbitrary term, as matches on arbitrary terms are not supported in ILH
          _ -> Let v_r (BasicTerm r) $ Case (Var v_r) (map (\(c, argNms, expr) -> (renameVar r c, map (renameVar r) argNms, replaceSubterm p r expr)) brs) b
            where
              v_r = "v_" ++ hashName r
        -- \| we don't need to replace the matched on variable
        func r = {- trace (unwords ["func", show r]) $ -} Case (Var x) (map (\(c, argNms, expr) -> (renameVar r c, map (renameVar r) argNms, replaceSubterm p r expr)) brs) b
        renameVar :: LHSimpleTerm -> Id -> Id
        renameVar r y =
          if isSubstOf p y
            then
              let y' = case replaceSubterm p r (Var y) of -- replaceSubterm p r = sub y r
                    Var y_ -> y_
                    other -> error $ "Error in AppSuable LHTerm LHSimpleTerm: " ++ show other
               in y'
            else y
    Case matchedTerm brs b -> resRec matches func
      where
        matches = concatMap (\(c, argNms, e) -> map Var ([c | isSubstOf p c] ++ filter (isSubstOf p) argNms) ++ findSubterm p e) brs
        func r = {- trace (unwords ["func", show r]) $ -} Case matchedTerm (map (\(c, argNms, expr) -> (renameVar r c, map (renameVar r) argNms, replaceSubterm p r expr)) brs) b
        renameVar :: LHSimpleTerm -> Id -> Id
        renameVar r y =
          if isSubstOf p y
            then
              let y' = case replaceSubterm p r (Var y) of -- replaceSubterm p r = sub y r
                    Var y_ -> y_
                    other -> error $ "Error in AppSuable LHTerm LHSimpleTerm: " ++ show other
               in y'
            else y
    Let x df e -> recurseFindAndRepl2 p (Let x) df e
    Lambda x e -> recurseFindAndRepl p (Lambda x) e
    Undefined -> unchanged
    SEqn s t z -> recurseFindAndRepl3 p SEqn s t z
    QMark z t -> recurseFindAndRepl2 p QMark z t

-- Annot e' tp -> recurseFindAndRepl e' (Annot tp)

instance AppSuable LHSimpleTerm LHTerm where
  findAndReplace p e = case e of
    Bop op s t -> recurseFindAndRepl2 p (Bop op) s t
    App (App f ts) us -> findAndReplace p $ App f (ts ++ us)
    Neg f -> recurseFindAndRepl p Neg f
    other@Var {} -> resRec matches func
      where
        matches = map BasicTerm $ findSubterm p' other
        func r = case r of
          BasicTerm e' -> replaceSubterm p' e' other
          _ -> error $ "findAndReplace " ++ showP p ++ " " ++ showP e ++ " is not supported."
        stripBasic ctm = case ctm of
          BasicTerm t -> t
          _ -> undefined
        p' = transPat stripBasic p
    -- \| UnitTerm or a literal
    _ -> unchanged

instance AppSuable LHTerm LHTerm where
  findAndReplace p tm = {- trace (unwords ["findAndReplace", show p, show e]) $ -} case tm of
    Annot t rt -> recurseFindAndRepl p (\s -> Annot s rt) t
    BasicTerm t -> recurseFindAndRepl p BasicTerm t
    -- \| Don't replace x itself if it is bound by this let binder
    Let x s t -> {- if isSubsId (Var x) then recurseFindAndRepl p (\y -> Let x y t) s else -} recurseFindAndRepl2 p (Let x) s t
    Lambda x e -> recurseFindAndRepl p (Lambda x) e
    Undefined -> unchanged
    Case (Var x) branches b -> resRec matches func
      where
        matches = [BasicTerm $ Var x | isSubstOf p x] ++ concatMap (\(c, argNms, expr) -> map (BasicTerm . Var) ([c | isSubstOf p c] ++ filter (isSubstOf p) argNms) ++ findSubterm p expr) branches
        p_ = case first toLHSimpleTermPat p of
          (Just stp, f) -> Just (stp, f)
          (Nothing, _) -> Nothing
        func r = case (r, p_) of
          (BasicTerm replTm, Just p') -> replaceSubterm p' replTm tm
          _ | not (isSubstOf p x) -> Case (Var x) (map (\(c, argNms, expr) -> (renameVar r c, map (renameVar r) argNms, replaceSubterm p r expr)) branches) b
          _ -> error $ "Cannot replace " ++ show p ++ " with " ++ show r ++ ". "

        renameVar :: LHTerm -> Id -> Id
        renameVar r y =
          if isSubstOf p y
            then
              let y' = case replaceSubterm p r (BasicTerm $ Var y) of -- replaceSubterm p r = sub y r
                    BasicTerm (Var y_) -> y_
                    other -> error $ "Error in AppSuable LHTerm LHTerm: " ++ show other
               in y'
            else y
        toLHSimpleTermPat :: TermPattern LHTerm -> Maybe (TermPattern LHSimpleTerm)
        toLHSimpleTermPat p' = case p' of
          TermPat (BasicTerm searchTm) -> Just $ TermPat searchTm
          IdPat y -> Just $ IdPat y
          AppPat gP tPs | not (any null (gPT : tsPT)) -> Just $ AppPat (fromJust gPT) (map fromJust tsPT)
            where
              gPT = toLHSimpleTermPat gP
              tsPT = map toLHSimpleTermPat tPs
          AnyPat -> Just AnyPat
          _ -> Nothing
    Case _ _ _ -> error "Match not on a variable found when substituting."
    SEqn s t hint -> recurseFindAndRepl3 p SEqn s t hint
    QMark s t -> recurseFindAndRepl2 p QMark s t

instance Suable LHSimpleTerm LHSimpleTerm where
  sub = replaceSubterm . (,True) . IdPat

instance Suable LHTerm LHSimpleTerm where
  sub = replaceSubterm . (,True) . IdPat

instance Suable LHSimpleTerm LHTerm where
  sub = replaceSubterm . (,True) . IdPat

instance Suable LHTerm LHTerm where
  sub = replaceSubterm . (,True) . IdPat

instance Suable LHType LHSimpleTerm where
  sub = replaceSubterm . (,True) . IdPat

instance Suable RefType LHSimpleTerm where
  sub = replaceSubterm . (,True) . IdPat
