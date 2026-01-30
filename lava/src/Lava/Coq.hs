{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
{- {-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-} -}

-- |
-- - (E)Coq grammar, printer to .ecoq file and suable functions
module Lava.Coq
  ( -- * names for derived declarations
    unrefinedTCName,
    wfTCName,
    refinedConstrName,
    unrefinedConstrName,

    -- * Names of boolean operators
    xorb,
    implb,
    negb,
    negB,

    -- * The ECoq grammar
    CoqModule (..),

    -- ** Declaration-level grammar
    CoqDecl (..),
    DefBody (..),
    CoqTermTC (..),
    CoqConstr (..),
    ChangeVisibility (..),
    Visibility (..),
    HintKind (..),
    HintDatabase (..),

    -- ** Object-level grammar
    BaseSort (..),
    Goal,
    CoqTerm (..),
    Bop (..),
    ProofTerm (..),
    CoqTactic (..),
    CoqDestrPat (..),
    RewriteDir (..),
    CoqIntroPat (..),
    coqBuiltinInductDataTypes,
    Builtin (..),
    RocqType (..),

    -- * Printer for grammar
    PrntPat (..),
    showCoqArg,
    prntTpls,

    -- * Other misc data type, class and instance definitions

    -- | convenience function to fetch refinement in 'SimpleRefType's
    getTCRef,
    -- | convenience functions to build certain buildin terms and types
    unitTm,
    unitTmName,
    btrue,
    btrueTmName,
    bfalse,
    bfalseTmName,
    boolTp,
    packName,
    projPackName,
    subsetWitnessNm,
    
    -- | argList related stuff
    ArgList (..),
    ArgListT (..),
    UArgList (..),
    UArgListT (..),
    mkArgList, mkUArgList, mkArgListT, mkUArgListT,
  )
where

import Data.Bifunctor
import Data.Data
import Data.List (sortBy)
import Lava.Util

unrefinedTCName :: Id -> Id
unrefinedTCName name = name ++ "_u"

refinedConstrName :: Id -> Id
refinedConstrName = id

unrefinedConstrName :: Id -> Id
unrefinedConstrName name = name ++ "_u"

wfTCName :: Id -> Id
wfTCName name = name ++ "_wf"

{- ORMOLU_DISABLE -}
packName :: Id
packName = "@Pack"
upackName :: Id
upackName = "@uPack"
projPackName = "packProj"

subsetWitnessNm x = x ++ "_p"

xorb = "xorb"
implb = "implb"
negb = "negb"
negB = "negBool"
unitTmName = "unit"
btrueTmName = "true"
bfalseTmName = "false"
unitTm = Cr unitTmName
btrue = Cr btrueTmName
bfalse = Cr bfalseTmName
boolTp = TC "bool" []
{- ORMOLU_ENABLE -}

-- | List of builtin CoqInductives like Nat or lists
coqBuiltinInductDataTypes :: [(Id, [(Id, RocqType)], [(Id, [(Id, RocqType)], RocqType)])]
coqBuiltinInductDataTypes =
  [ ( "bool",
      [],
      [ ("false", [], TC "bool" []),
        ("true", [], TC "bool" [])
      ]
    ),
    ("Unit", [], [("unit", [], TC "Unit" [])])
  ] -- ToDo: Fill this in

-- * The actual ECoq grammar

-- ** The (module and) declaration-level grammar

-- | A named ECoq module containing some declarations
--
-- > M ::= Module x. D* End x.
data CoqModule = CoqModule Id [CoqDecl] deriving (Eq, Data)

-- | Declarations
--
-- > d ::= Inductive tc : Set := (| c: A)*
-- >     | Opaque x. | Transparent x.
-- >     | AddHint HintKind x HintDatabase.
-- >     | Load x.
-- >     | Definition f (x: R)* : R. Proof. tac* Defined.
-- >     | Definition f := e.
-- >     | Definition x := tp.
-- >     | Axiom f ((x:tp)|[x:tp])* : tp.
-- >     | idef
-- >     | CoqInductive tc (x:tp)* : k := (| c: ∀(y:tp)*, tp)*.
-- >     | Transparent x. | Opaque x.
data CoqDecl
  = -- Stuff we have that is missing in Rocq, but should potentially be there

    -- | A declaration of an inductive data type
    TCDecl Id [CoqConstr]
  | -- | Mark definitions as Transparent or Opaque, as needed
    CoqMarkVisibility ChangeVisibility
  | -- | Add the hint to the specified hint database in Coq
    AddHint HintKind Id HintDatabase
  | -- Stuff also present in Rocq

    -- | a load declaration for some module to be loaded
    Load Id
  | -- | A fixpoint in Coq
    Fix
      Id
      [((Id, RocqType), Bool)]
      RocqType
      -- | Should we merge this into Definitions with an extra flag?
      CoqTerm
  | -- | A Coq definition/theorem
    Definition Id [((Id, RocqType), Bool)] RocqType DefBody Visibility
  | -- | A declaration of an axiom in Coq
    CoqAxiom
      Id
      [((Id, RocqType), Bool)]
      -- | TODO: Consider getting rid of the args, as Axioms cannot have arguments to the left of the :, however forallT doesn't currently support implicit arguments
      RocqType
  | -- | An inductively defined Prop, Type or Set (used only internally)
    CoqInductive Id [(Id, RocqType)] RocqType [CoqConstr]
  | -- Internal stuff

    -- | A term-level notation (like the refined constructors)
    CoqAlias Id CoqTerm
  | -- | A type-level notation (like the refined inductive data types)
    CoqNewType Id RocqType
  | -- | An instance of one of the dictionary classes used for lookup in the proof automation tactics in Coq
    Instance Id [Id] [(Id, CoqTerm)]
  | TacInstance Id Id CoqTactic
  deriving (Eq, Data)

data DefBody
  = ProofBody [CoqTactic]
  | TermBody CoqTerm
  deriving (Data, Eq)

-- | A refined type constructor, the only kind allowed in the image of the translation to ECoq, gets printed to its elaboration by the 'CoqPrinter'
--
-- > Inductive tc : Set := (| c: A)*
data CoqTermTC = InductiveData {cDataName :: Id, constructors :: [CoqConstr]} deriving (Data, Eq)

-- | Data constructors
--
-- > c: A
data CoqConstr = Constr {cConstrNm :: Id, cConstrTp :: RocqType} deriving (Data, Eq)

-- |
--
-- > Transparent x. | Opaque x.
data ChangeVisibility = ChangeVisibility Id Visibility deriving (Data, Eq)

data Visibility = Transparent | Opaque deriving (Data, Eq, Show)

data HintKind = UnfoldHint | ConstructorsHint | ResolveHint | RewriteHint deriving (Data, Eq)

data HintDatabase = CoreDB | GraphRelDB | GraphRelBackDB | WfDB | RefConstrDB | RelAxDB | EqHintDb deriving (Data, Eq)

-- ** Object-level grammar

-- | Basically the same as a RocqType, but shouldn't contain holes (it can still contain simple type goals, but those Coq should be able to infer when needed) or errors
type Goal = RocqType

-- TODO: rename names with 2

-- | Built-in datatypes
--
-- > B ::= Z | string | float
data Builtin = CTInt | CTString | CTFloat
  deriving (Eq, Data)

-- | Sorts
--
-- > κ ::= Type | Prop | Set
data BaseSort = TypeSort | PropSort | SetSort deriving (Eq, Data)


-- | Types
--
-- > A ::= B | κ | {x:A | e} | tc A* | A -> A | ∀(x:A),A | e
--       | uPack A A* | Pack n (x:A)* A* e* | _
data RocqType
  = Builtin Builtin
  | Sort BaseSort
  | Subset Id RocqType CoqTerm
  | TC Id [RocqType]
  -- | (simple-typed) arrow type 
  | Arrow RocqType RocqType
  -- | Pi type
  | FAType (Id, RocqType) RocqType
  -- | Prop-sorted Rocq Types
  | Prop CoqTerm
  -- | unrefined Packs
  |  UPack UArgListT RocqType
  | Pack ArgListT UArgListT CoqTerm RocqType CoqTerm
  | ArgumentList ArgListT
  | Hole
  deriving (Eq, Data)

newtype ArgListT = ArgListT [(Id, RocqType)] deriving (Eq, Data)
newtype ArgList = ArgList [CoqTerm] deriving (Eq, Data)
newtype UArgListT = UArgListT [RocqType] deriving (Eq, Data)
newtype UArgList = UArgList [CoqTerm]

mkArgListT :: ArgListT -> CoqTerm
mkArgListT (ArgListT xs) = foldl (\tlTm (x,t)->Bop ConsRT (TypeArg t) $ Lambda x t tlTm) (Def "nilRT") (reverse xs)

mkUArgListT :: UArgListT -> CoqTerm
mkUArgListT (UArgListT xs) = foldl (\tlTm t -> Bop ConsUT (TypeArg t) tlTm) (Def "nilUT") (reverse xs)

mkArgList :: ArgList -> CoqTerm
mkArgList (ArgList args) = foldl (flip (Bop ConsR)) (Def "nilR") args

mkUArgList :: UArgList -> CoqTerm
mkUArgList (UArgList uargs) = foldl (flip (Bop ConsU)) (Def "nilU") uargs

instance Show ArgListT where
  show = show . mkArgListT
instance Show ArgList where
  show = show . mkArgList
instance Show UArgListT where
  show = show . mkUArgListT
instance Show UArgList where
  show = show . mkUArgList

-- | An ECoq term of any kind
--
-- > e ::= ∀(x:tp)*, e | exists (x:tp)*, e
-- >     | e /\ e | e \/ e | e -> e | e <-> e | not e | True | False | is_true e
-- >     | x ∈ (Def, Abbr, Var, Cr) | e bop e | "s" (s ∈ String) | I n (n ∈ Z) | F f (f ∈ Float)
-- >     | e e* | λx:tp.e
-- >     | ⌊e⌋ | subCast R R e p | exist e e p
-- >     | match (e,)* with (| c x* => e)* | if e then e else e | let x := e in e
-- >     | undefined | _ | p
data CoqTerm
  = Forall [(Id, RocqType)] CoqTerm
  | Exists [(Id, RocqType)] CoqTerm
  | And CoqTerm CoqTerm
  | Or CoqTerm CoqTerm
  | Impl CoqTerm CoqTerm
  | Equiv CoqTerm CoqTerm
  | Neg CoqTerm
  | NegB CoqTerm
  | TT
  | FF
  | IsTrue CoqTerm
  | -- | represents a function name
    Def Id
  | -- | represents a notation
    Abbr Id
  | -- | represents a constructor name
    Cr Id
  | -- | represents a variable
    Var Id
  | Bop Bop CoqTerm CoqTerm
  | StringLiteral String
  | IntLiteral Integer
  | FloatLiteral Double
  | App CoqTerm [CoqTerm]
  | Lambda Id RocqType CoqTerm
  | Project CoqTerm
  | SubCast RocqType RocqType CoqTerm ProofTerm
  | Exist {cRefPred :: CoqTerm, cExistTerm :: CoqTerm, cExistPrf :: ProofTerm}
  | Match [CoqTerm] (Maybe Id) [([(Id, [Id])], CoqTerm)]
  | Ite CoqTerm CoqTerm CoqTerm
  | Let Id CoqTerm CoqTerm
  | Undefined
  | TermHole
  | PrfTerm Goal ProofTerm
  | InstanceProjection CoqTerm Id
  | InlineInstance [(Id, CoqTerm)]
  | TypeArg RocqType
  deriving (Data, Eq)

-- | Boolean operators
--
-- > bop ::= = | <> | <= | >= | < | > | + | - | * | /
-- >       | <=? | >=? | =? | <? | >? | && | ‖ | =>? | ==? |  eqb
data Bop = Eq | EqProp | Neq | Leq | Geq | Lt | Gt | Plus | Minus | Times | Div | Mod | Leqb | Geqb | Eqb | Neqb | Ltb | Gtb | Andb | Orb | ImplB | EqualB | NEqualB | Equal | EqualBProp | EqBool | PlusU | MinusU | TimesU | DivU | ModU | ConsRT | ConsUT | ConsR | ConsU deriving (Data, Eq)

-- | represents terms of Prop-kinded types in ECoq, in particular refinement witnesses
--
-- > p ::= s ∈ String | e | _ | ⌈e⌉ | conj e e
data ProofTerm
  = CoqProofTerm String
  | TermWitness CoqTerm
  | ProofHole (Maybe Id)
  | ByTac CoqTactic
  | RefWitness CoqTerm
  | Conj ProofTerm ProofTerm
  deriving (Data, Eq)

-- TODO: remove unnecessary tactics, once we get rid of legacy translation

-- | represents supported ECoq tactics, both custom tactics and basic Coq tactics (@tac@)
data CoqTactic
  = Easy
  | Oracle
  | Ple
  | Apply CoqTerm
  | -- In the branches, the Id is the name of the constructor in the branch (useful for reordering in the order needed by Coq)
    Destruct {destrExpr :: CoqTerm, destrBranches :: [(Id, (CoqDestrPat, [CoqTactic]))]}
  | Induction {indTerm :: CoqTerm, indBranches :: [(Id, (CoqDestrPat, [CoqTactic]))]}
  | Now CoqTactic
  | SplitB [CoqTactic] [CoqTactic]
  | Exact CoqTerm
  | RefineT RocqType
  | SubgoalMarkers [CoqTactic]
  | Admit [Id]
  | Pose Id CoqTerm
  | ProofPose Id CoqTerm
  | Try CoqTactic
  | Timeout Int CoqTactic
  | ApplyPartial CoqTerm
  | Refine CoqTerm
  | -- ToDo: Extend to a more useful version of this tactic
    DestructSubsetTerm CoqTerm CoqDestrPat
  | DestructConj Id Id Id
  | Simpl (Maybe Id)
  | Rewrite (Maybe RewriteDir) CoqTerm (Maybe Id)
  | Replace CoqTerm CoqTerm CoqTactic (Maybe Id)
  | Assert {assHypName :: Id, assClaim :: Goal, assPrf :: CoqTactic}
  | AssertTerm Id CoqTerm (Maybe Id)
  | Intros [CoqIntroPat]
  | Revert [Id]
  | GeneralizeDependent [Id]
  | Specialize Id [CoqTerm]
  | -- | represents the custom specialization tactics, currently no longer used in the translation
    SpecializeIH {unspecIh :: Id, spIhIhTp :: RocqType, spIhMatchedVar :: Id, spIhConstr :: Id, spIhCargs :: [Id], spIhBoundVar :: CoqTerm, spIhZ :: Maybe ProofTerm, newIHName :: Maybe Id}
  | Clear Id
  | ClearDependent Id
  | Inversion Id [[Id]]
  | Concat [CoqTactic]
  | Branches [CoqTactic]
  | Custom String
  | Exfalso
  deriving (Data, Eq)

-- | Destruction patterns
--
-- > des ::= [ des* ] | [ (des|)* ] | x | _
data CoqDestrPat
  = -- | represents a conjunctive pattern with several sub-patterns
    ConjDestrPat [CoqDestrPat]
  | -- | represents a disjunctive pattern with several branches
    DisjDestrPat [CoqDestrPat]
  | -- | represents an identifier in a destructor pattern
    SingleIdPat Id
  | -- | represents _ in patterns
    UnnamedIdPat
  deriving (Data, Eq)

data RewriteDir
  = -- | represents the -> rewrite pattern
    RwLR
  | -- | represents the <- rewrite pattern
    RwRL
  deriving (Data, Eq)

data CoqIntroPat = DestrPat CoqDestrPat | RewritePat RewriteDir deriving (Data, Eq)

-- * Functions on the grammar

-- | Regroup forall arguments
concatForalls :: RocqType -> ([(Id, RocqType)], RocqType)
concatForalls (FAType arg tp) = first (arg :) $ concatForalls tp
concatForalls tp = ([], tp)

-- * Printer for grammar

showCoqArg :: (Show a) => ((Id, a), Bool) -> String
showCoqArg ((x, tp), isImplicit) = if isImplicit then " [" ++ argBody ++ "]" else " (" ++ argBody ++ ")"
  where
    argBody = x ++ ": " ++ show tp

instance Show CoqModule where
  show (CoqModule name decls) = "module " ++ name ++ " " ++ intercalate "; " (map show decls)

instance Show CoqConstr where
  show (Constr c tp) = c ++ ": " ++ show tp

instance Show CoqTermTC where
  show (InductiveData n constrs) = "Inductive " ++ n ++ ": Set := " ++ intercalate " | " (map show constrs)

instance Show CoqDecl where
  show (TCDecl n constrs) = "Inductive " ++ n ++ ": Set := " ++ intercalate " | " (map show constrs)
  show (Definition f args ret body vis) = header ++ bdy
    where
      bdy = case body of
        ProofBody tacs -> prfBody tacs
        TermBody expr -> definien expr

      header = case ret of
        Prop {} | vis == Opaque -> "Theorem " ++ sign
        _ -> "Definition " ++ sign
      sign = f ++ concatMap showCoqArg args ++ ": " ++ show ret
      definien tm = " := \n\t" ++ show tm ++ ". "
      prfBody tacs = ". \nProof. \n\t" ++ showTacs 1 tacs ++ if admitted tacs then "\nAdmitted. " else qedSym
      qedSym = case vis of
        Transparent -> "\nDefined. "
        Opaque -> "\nQed. "
  show (Fix f args ret tm) = "Fixpoint " ++ f ++ concatMap showCoqArg args ++ ": " ++ show ret ++ " := \n\t" ++ show tm ++ ". "
  show (Load m) = "Load " ++ m ++ ". "
  show (CoqAlias f e) = "Notation " ++ f ++ " := " ++ show e ++ ". "
  show (CoqNewType t tp) = "Global Notation " ++ t ++ " := " ++ printRocqType tp False ++ ". "
  show (CoqAxiom ax args claim) = "Axiom " ++ ax ++ " : " ++ showForall (map fst args) claim ++ ". "
  show (CoqInductive f args k constrs) =
    "Inductive "
      ++ f
      ++ concatMap (\(x, tp) -> " (" ++ x ++ ": " ++ show tp ++ ")") args
      ++ " : "
      ++ showP k
      ++ " := "
      ++ concatMap (("\n\t | " ++) . show) constrs
      ++ ". "
  show (CoqMarkVisibility v) = show v
  show (AddHint kind ax db) = "#[global] Hint " ++ show kind ++ " " ++ ax ++ " : " ++ show db ++ "."
  show (Instance instName tp opDefs) = "#[global] Instance " ++ instName ++ " : " ++ unwords tp ++ " := { " ++ intercalate ";" (map (\(lookupOp, lookupRes) -> showNewline 1 ++ lookupOp ++ " := " ++ show lookupRes) opDefs) ++ "\n}."
  show (TacInstance instName tp tac) = "#[global] Instance " ++ instName ++ " : " ++ tp ++ ".\nProof. " ++ show tac ++ "\nDefined."

instance Show ChangeVisibility where
  show (ChangeVisibility f Transparent) = "Transparent " ++ f ++ ". "
  show (ChangeVisibility f Opaque) = "Opaque " ++ f ++ ". "

instance Show HintKind where
  show UnfoldHint = "Unfold"
  show ConstructorsHint = "Constructors"
  show ResolveHint = "Resolve"
  show RewriteHint = "Rewrite"

instance Show HintDatabase where
  show RefConstrDB = "ref_constr_db"
  show WfDB = "wf_constr_db"
  show GraphRelDB = "f_rel_funct_db"
  show CoreDB = "core_hint_db"
  show GraphRelBackDB = "f_rel_back"
  show RelAxDB = "rel_ax_db"
  show EqHintDb = "eq_hint_db"

instance Show Builtin where
  show CTInt = "Z"
  show CTString = "String"
  show CTFloat = "Float"

-- The flag indicates if we use our notations on subset types
-- (Bool for {_:bool|True} and {{…}} for a lemma)
printRocqType :: RocqType -> Bool -> String
printRocqType (Builtin b) _ = show b
printRocqType (Sort sort) _ = show sort
-- NOTE: for TC, there are cases where me might need to add (getTCRef x tc), the well-formedness predicate (as in prntRefType)
printRocqType (Subset x (TC tc []) e) True = case tc of
  "bool" | isTriv e -> "Bool"
  "Unit" | not (hasMatch (TermPat (Var x), True) e) -> "{{" ++ show e ++ "}}"
  _ -> case e of
    _ | builtin -> "{" ++ x ++ ": " ++ tc ++ " | " ++ show e ++ "}"
    And (App (Def wf) [Var x']) true | x == x' && wf == wfTCName tc && isTriv true -> tc
    _ -> "{" ++ x ++ ": " ++ unrefinedTCName tc ++ " | " ++ show e ++ "}"
  where
    isTriv TT = True
    isTriv (IsTrue b) = show b == btrueTmName
    isTriv _ = False
    builtin = elem tc $ map fst3 coqBuiltinInductDataTypes
printRocqType (Subset x tp e) _ = "{" ++ x ++ ": " ++ show tp ++ " | " ++ show e ++ "}"
printRocqType (TC tn []) _ | any ((== tn) . fst3) coqBuiltinInductDataTypes = tn
printRocqType (TC typeName tpArgs) _ = unrefinedTCName typeName ++ unwords (map show tpArgs)
printRocqType (Arrow tp1 tp2) _ = showP tp1 ++ " -> " ++ showP tp2
printRocqType tp@(FAType {}) _ = let (args, ret) = concatForalls tp in showForall args ret
printRocqType (Prop p) _ = show p
printRocqType (UPack uargTps t) _ = unwords [upackName, showP uargTps, showP t]
printRocqType (ArgumentList argTps) _ = addParens $ "ArgList " ++ show argTps
printRocqType (Pack argTps uargTps z t p) _ = addParens . unwords $
  [packName, showP argTps, showP uargTps, showP z, showP t, showP p]
printRocqType Hole _ = "_"

instance Show RocqType where
  show rt = printRocqType rt True

getTCRef :: Id -> String -> CoqTerm
getTCRef x a = App (Def $ wfTCName a) [Var x]

-- TODO: do this for our RocqType
-- equality of refinemed types is alpha-equivalence
-- refined inductive types are unfolded into refined instances of the unrefined data type
{- instance {-# OVERLAPPING #-} Eq SimpleRefType where
  (==) (x, a, q) (y, b, r) = a == b && sub y (Var x) r == q -}
{- instance {-# OVERLAPPING #-} Eq RocqType where
  (==) (Subset x a q) (Subset y b r) = a == b && sub y (Var x) r == q -}

instance Show BaseSort where
  show PropSort = "Prop"
  show TypeSort = "Type"
  show SetSort = "Set"

{- instance {-# OVERLAPPING #-} Show CoqArgContext where
  show [] = "∅ "
  show vars = "∅ , " ++ intercalate ", " (map (\(x, tp) -> x ++ ": " ++ show tp) vars) -}

formatLong s = if length s > 60 then "\n\t\t" ++ s else s

instance Show CoqTerm where
  show coqTerm = case coqTerm of
    Forall vars p -> if null vars then show p else "forall " ++ unwords (map (\(x, tp) -> "(" ++ x ++ ": " ++ show tp ++ ")") vars) ++ ", " ++ show p
    Exists vars p -> if null vars then show p else "exists " ++ unwords (map (\(x, tp) -> "(" ++ x ++ ": " ++ show tp ++ ")") vars) ++ ", " ++ show p
    IsTrue (App neg [f]) | neg == Def negb -> show $ Neg (IsTrue f)
    IsTrue (App impl [a, c]) | impl == Def implb -> show $ Impl (IsTrue a) (IsTrue c)
    IsTrue (Bop ImplB a c) -> show $ Impl (IsTrue a) (IsTrue c)
    IsTrue (Bop EqualBProp s t) -> show $ Bop EqProp s t
    -- IsTrue (Bop EqualB s t) -> show $ Bop Eq (IsTrue s) (IsTrue t) -- C.PExpr . C.eqTrue $ mkBEqual decls ctx CTBool s t
    IsTrue (App (Def ngb) [f])  | ngb == negb -> show . Neg $ IsTrue f
    -- IsTrue (Bop Neqb s t) -> show $ Bop Neq (IsTrue s) (IsTrue t)
    IsTrue (Bop EqualB s t)  | boolHeuristic s || boolHeuristic t -> show $ Bop EqProp (IsTrue s) (IsTrue t)
    --IsTrue (Bop Neqb s t)    | boolHeuristic s || boolHeuristic t -> show $ Bop Neq (IsTrue s) (IsTrue t)
    IsTrue (Bop EqualB s t)  | nonBoolHeuristic s || nonBoolHeuristic t -> show $ Bop Eq s t
    IsTrue (Bop EqualB s t) -> show $ Bop Equal s t
    IsTrue (Bop Neqb s t)    | boolHeuristic s || boolHeuristic t -> show . Neg $ Bop EqProp (IsTrue s) (IsTrue t)
    IsTrue (Bop Neqb s t)    {- | nonBoolHeuristic s || nonBoolHeuristic t -} -> show $ Bop Neq s t
    IsTrue (Bop Andb s t) -> show $ And (IsTrue s) (IsTrue t)
    IsTrue (Bop Orb s t) -> show $ Or (IsTrue s) (IsTrue t)
    IsTrue (Bop Leqb s t) -> showP s ++ " <= " ++showP t-- show $ Bop Leq s t
    IsTrue (Bop Ltb s t) -> showP s ++ " < " ++showP t -- show $ Bop Lt s t
    IsTrue (Bop Geqb s t) -> showP s ++ " >= " ++showP t --show $ Bop Geq s t
    IsTrue (Bop Gtb s t) -> showP s ++ " > " ++showP t --show $ Bop Gt s t
    IsTrue (Bop Eqb s t) -> show $ Bop Eq s t
    IsTrue b | show b == btrueTmName -> show TT
    IsTrue b | show b == bfalseTmName -> show FF
    IsTrue b -> show $ App (Def "is_true") [b]
    And p q -> showP p ++ " /\\ " ++ showP q
    Or p q -> showP p ++ " \\/ " ++ showP q
    Impl p q -> showP p ++ " -> " ++ showP q
    Equiv p q -> showP p ++ " <-> " ++ showP q
    Neg (IsTrue (Bop EqualB s t)) -> show . IsTrue $ Bop Neqb s t 
    App neg [Bop EqualB s t] | neg == Def negb -> show $ Bop NEqualB s t
    Neg (Neg p) -> show p
    Neg p -> "not " ++ showP p
    NegB (NegB p) -> show p
    NegB p -> negB ++ " " ++ showP p
    TT -> "True"
    FF -> "False"
    Def s -> {- "Def "++ -} s
    Abbr s -> {- "Abbr "++ -} s
    Bop bop s t -> showP s ++ " " ++ show bop ++ " " ++ showP t
    Var x -> x
    StringLiteral s -> "\"" ++ s ++ "\""
    IntLiteral n -> show n
    FloatLiteral f -> show f
    App f ts -> unwords apTmsFormatted where
      apSs = map showP (f : ts)
      apTmsFormatted = map formatLong apSs
    Cr s -> {- "Cr "++ -} s
    Lambda x a s -> "fun (" ++ x ++ ": " ++ showP a ++ ") => " ++ showP s
    Project (Exist _ t _) -> show t
    Project (Bop Plus s t) -> show $ Bop PlusU (projTm s) (projTm t)
    Project (Bop Minus s t) -> show $ Bop MinusU (projTm s) (projTm t)
    Project (Bop Times s t) -> show $ Bop TimesU (projTm s) (projTm t)
    Project (Bop Div s t) -> show $ Bop DivU (projTm s) (projTm t)
    Project (Bop Mod s t) -> show $ Bop ModU (projTm s) (projTm t)
    Project (App (Cr c) ts) -> showP $ App (Cr $ unrefinedConstrName c) (map projTm ts)
    Project (Cr c) -> showP . Cr $ unrefinedConstrName c
    Project (NegB p) -> show $ Neg (Project p)
    Project t -> "⌊ " ++ show t ++ " -⌋"
    SubCast (Subset n b need) _ (Exist _ tm ProofHole{}) (ProofHole idO) ->
      show $ Exist (Lambda n b need) tm (ProofHole idO)
    SubCast (Subset n b need) _ (Exist _ tm CoqProofTerm{}) (ProofHole idO) ->
      show $ Exist (Lambda n b need) tm (ProofHole idO)
    SubCast Hole _ (Exist _ tm CoqProofTerm{}) (TermWitness TermHole) ->
      show $ Exist TermHole tm (TermWitness TermHole)
    SubCast Hole _ (Exist _ tm CoqProofTerm{}) (ProofHole idO) ->
      show $ Exist TermHole tm (ProofHole idO)
    SubCast Hole _ (Exist _ tm ProofHole{}) (TermWitness TermHole) ->
      show $ Exist TermHole tm (TermWitness TermHole)
    SubCast need have t _ | need == have && need /= Hole -> show t
    SubCast Hole _ t z -> addParens $ unwords ["subsumptionCast", "_", "_", formatLong $ showP t, formatLong $ showP z]
    SubCast (Subset n b need) (Subset _ a _) t z | a == b -> addParens $ unwords ["subsumptionCast", formatLong $ showP a, formatLong $ showP (Lambda n a need), formatLong $ showP t, formatLong $ showP z]
    SubCast to from t z -> addParens $ unwords ["subCast", formatLong $ showP from, formatLong $ showP to, formatLong $ showP t, formatLong $ showP z]
    -- SubCast a b t p -> "subsumptionCast "++showP a++" "++showP b++" "++showP t++" "++showP p
    Exist p t z -> "exist " ++ showP p ++ " " ++ showP t ++ " " ++ showP z
    Match ts _ cases -> "match " ++ addParens (intercalate ", " (map show ts)) ++ " with " ++ intercalate " | " (map ((\(x, y) -> x ++ " => " ++ y) . bimap (addParens . intercalate ", " . map (\(c, args) -> unwords (c : args))) showP) cases) ++ " end"
    Ite r s t -> "if " ++ show r ++ " then " ++ show s ++ " else " ++ showP t
    Let x s t -> "let " ++ x ++ " := " ++ show s ++ " in " ++ showP t
    Undefined -> "undefined"
    InstanceProjection inst field -> showP inst ++".("++field++")"
    InlineInstance fields -> "{| " ++ intercalate "; " (map (\(field, val) -> field ++ " := " ++ show val) fields) ++ " |}"
    TypeArg tp -> show tp
    TermHole -> "_"
    PrfTerm _ z -> show z
    where
      boolHeuristic t = case t of
        Bop op _ _ | op `elem` [ImplB, EqualB, EqualBProp, Neqb, Andb, Orb, Leqb, Ltb, Geqb, Gtb, Eqb] -> True
        IsTrue (App impl _) | impl == Def implb -> True
        _ | t == btrue -> True
        _ | t == bfalse -> True
        TT -> True
        FF -> True
        _ -> False
      nonBoolHeuristic t | boolHeuristic t = False
      nonBoolHeuristic t = case t of
        Bop{} -> True
        Project{} -> True
        Exist{} -> True
        SubCast{} -> True
        IsTrue{} -> True
        Cr{} -> True
        _ -> False

      projTm tm = case tm of
        Exist _ term _ -> term
        SubCast _ _ term _ -> projTm term
        Cr c | isJust (stripSuffixO (unrefinedConstrName "") c) -> Cr c
        Cr c -> Cr (unrefinedConstrName c)
        App (Cr c) args | isJust (stripSuffixO (unrefinedConstrName "") c) -> App (Cr c) (map projTm args)
        App (Cr c) args -> App (Cr . unrefinedConstrName  $ c) (map projTm args)
        other -> Project other

instance Show Bop where
  show Eq = "="
  show EqProp = "<->"
  show Neq = "<>"
  show Leq = "<=Z"
  show Geq = ">="
  show Lt = "<Z"
  show Gt = ">"
  show Plus = "+Z"
  show Minus = "-Z"
  show Times = "*Z"
  show Div = "/Z"
  show Mod = undefined
  show Leqb = "<=?"
  show Geqb = ">=?"
  show EqBool = "eqb"
  show Eqb = "=?Z"
  -- show NeqZb = "!=?" -- there is no such infix notation in Coq for bool-valued equality on Z, so we define one ourselves
  show Neqb = "/=?" -- there is no such infix notation in Coq for bool-valued equality on Z, so we define one ourselves
  show Ltb = "<?"
  show Gtb = ">?"
  show Andb = "&&"
  show Orb = "||"
  show EqualB = "==?"
  show NEqualB = "/=?"
  show Equal = "=="
  show EqualBProp = "<=>?"
  show ImplB = "implb"
  show PlusU = "+"
  show MinusU = "-"
  show TimesU = "*"
  show DivU = "/"
  show ModU = "mod"
  show ConsRT = "::RT"
  show ConsUT = "::UT"
  show ConsR = "::R"
  show ConsU = "::U"

instance Show ProofTerm where
  show (CoqProofTerm s) = s
  show (TermWitness tm) | tm == unitTm = "_"
  show (TermWitness t) = show t
  show (RefWitness tm) = "⌈ " ++ show tm ++ " ⌉"
  show (ProofHole Nothing) = "(ltac: (" ++ show Oracle ++ "))"
  show (ProofHole (Just h)) = "(ltac: (" ++ show (Concat [Try (Clear h), Oracle]) ++ "))"
  show (ByTac tac) = "(" ++ "ltac: (" ++ show tac ++ "))"
  show (Conj l r) = "conj " ++ showP l ++ " " ++ showP r

-- | prints an 'CoqDestrPat' or 'CoqIntroPat' without the outermost angular bracket
class (Show a) => PrntPat a where
  prntPat :: a -> String
  prntPat = stripBrackets . show
    where
      stripBrackets s = if length s > 1 && head s == '[' && last s == ']' then init . tail $ s else s

instance PrntPat CoqDestrPat

instance Show CoqDestrPat where
  show p = case p of
    ConjDestrPat pats -> "[" ++ unwords (map show pats) ++ "]"
    DisjDestrPat pats -> "[" ++ intercalate " | " (map prntPat pats) ++ "]"
    UnnamedIdPat -> "_"
    SingleIdPat n -> n

instance Show RewriteDir where
  show RwLR = "->"
  show RwRL = "<-"

instance Show CoqIntroPat where
  show (DestrPat p) = show p
  show (RewritePat rwDir) = show rwDir

instance PrntPat CoqIntroPat

prntTpls [] = "_nil"
prntTpls (hd : tl) = showTpl hd ++ " _::_ " ++ prntTpls tl
  where
    -- (f, relDefName f, funcHoodLemName f, relDefThmName f, relDefRwLemName f, relDefLemName f, relDefMkLemName f)
    showTpl (f, f_rel {-}, f_func, f__f_rel, f_rel_rw, f__f_rel', f_rel_mk -}) = "(" ++ intercalate ", " [f, f_rel {-, f_func, f__f_rel, f_rel_rw, f__f_rel', f_rel_mk -}] ++ ")"

instance PrettyPrintable CoqTactic where
  prettyPrint indent tac = case tac of
    Easy -> "quicksolve"
    Oracle -> "solver"
    Admit hints -> (if null hints then "" else "(* hints: " ++ intercalate ", " hints ++ "*) ") ++ "admit"
    Ple -> "ple"
    Apply tm -> {-"apply " ++ showP tm -} "smt_app " ++ showP tm
    Destruct (Var x) branches | all ((== "") . intercalate "; " . map (prettyPrint indent) . snd . snd) branches -> "destruct " ++ x ++ " as [" ++ intercalate " | " (map (prntPat . fst . snd) branchesS) ++ "]"
      where
        branchesS = sortBy ordFunc branches
    Destruct (Var x) branches -> "destruct " ++ x ++ " as [" ++ intercalate " | " (map (prntPat . fst . snd) branchesS) ++ "]. " ++ showTacBranches (indent + 1) (map snd branchesS)
      where
        branchesS = sortBy ordFunc branches
    Destruct tm branches ->
      "let E := fresh \"E\" in "
        ++ showNewline indent
        ++ "destruct "
        ++ showP tm
        ++ " as ["
        ++ intercalate " | " (map (prntPat . fst . snd) branchesS)
        ++ "] eqn:E"
        ++ if all ((== "") . intercalate "; " . map (prettyPrint indent) . snd . snd) branchesS then "" else "; [" ++ intercalate " | " (map (prettyPrint indent . Concat . snd . snd) branchesS) ++ "]"
      where
        branchesS = sortBy ordFunc branches
    Induction t branches | all ((== "") . intercalate "; " . map (prettyPrint indent) . snd . snd) branches -> matchTac ++ show t ++ " as [" ++ intercalate " | " (map (\br -> "(*" ++ fst br ++ "*) " ++ (prntPat . fst $ snd br)) branchesS) ++ "]"
      where
        branchesS = sortBy ordFunc branches
        matchTac = if all ((== ConjDestrPat []) . fst . snd) branches then "destruct " else "induction "
    Induction tm branches -> "induction " ++ show tm ++ " as [" ++ intercalate " | " (map (\br -> "(*" ++ fst br ++ "*) " ++ (prntPat . fst $ snd br)) branchesS) ++ "]. " ++ showTacBranches (indent + 1) (map snd branchesS)
      where
        branchesS = sortBy ordFunc branches
    Now t -> "now " ++ prt t
    SplitB tacL tacR -> "split. " ++ showTacBranch (indent + 1) False tacL ++ showTacBranch (indent + 1) False tacR
    Exact t -> case t of
      SubCast _ _ (Exist _ tm (CoqProofTerm "eq_refl")) (ProofHole _) -> "refine " ++ showP (Exist TermHole tm (TermWitness TermHole)) ++ "; " ++ showNewline indent ++ show Oracle
      SubCast _ _ (Exist _ tm (CoqProofTerm "I")) (ProofHole _) -> "refine " ++ showP (Exist TermHole tm (TermWitness TermHole)) ++ "; " ++ showNewline indent ++ show Oracle
      SubCast _ have tm (ProofHole _) -> "refine " ++ showP (SubCast Hole have tm (TermWitness TermHole)) ++ "; " ++ showNewline indent ++ show Oracle
      SubCast _ have tm p -> "exact " ++ showP (SubCast Hole have tm p)
      -- Exist _ tm p -> Exist TermHole tm p
      _ -> "refine " ++ showP t
    RefineT tp -> "refine " ++ showP tp
    SubgoalMarkers tacs -> showTacBranch (indent + 1) True tacs
    Concat tacs -> intercalate ("; " ++ showNewline indent) $ map (prettyPrint indent) tacs'
      where
        tacs' = filter (\case (Custom "idtac") -> False; t -> prettyPrint indent t /= "") tacs
    Branches tacs | all ((== "") . prettyPrint indent) tacs -> ""
    Branches tacs -> "[" ++ intercalate ("| " ++ showNewline indent) (map (prettyPrint indent) tacs) ++ "]"
    Custom str -> str
    Exfalso -> "exfalso"
    Try t -> "try " ++ show t
    Timeout t tc -> "timeout " ++ show t ++ " " ++ addParens (prettyPrint indent tc)
    ApplyPartial tm -> "unshelve eapply " ++ showP tm
    Refine t -> "refine " ++ showP t
    DestructSubsetTerm tm destrPat -> "destruct " ++ show tm ++ " as [" ++ prntPat destrPat ++ "]"
    DestructConj h h1 h2 -> "destruct " ++ h ++ " as [" ++ h1 ++ " " ++ h2 ++ "]"
    Rewrite dirO tm (Just hyp) -> "rewrite " ++ dirS ++ showP tm ++ " in " ++ hyp
      where
        dirS = case dirO of
          Just dir -> show dir ++ " "
          Nothing -> ""
    Rewrite dirO tm Nothing -> "rewrite " ++ dirS ++ showP tm
      where
        dirS = case dirO of
          Just dir -> show dir ++ " "
          Nothing -> ""
    Replace s t tactic (Just hyp) -> "replace " ++ showP s ++ " with " ++ showP t ++ " in " ++ hyp ++ " by " ++ showP tactic
    Replace s t tactic Nothing -> "replace " ++ showP s ++ " with " ++ showP t ++ " by " ++ showP tactic
    Simpl hypO -> "simpl" ++ maybe "" (" in " ++) hypO
    Pose abbr tm -> "pose " ++ showP tm ++ " as " ++ abbr
    ProofPose abbr tm -> "pose proof " ++ showP tm ++ " as " ++ abbr
    Assert n claim prf -> "assert (" ++ n ++ ": " ++ show claim ++ ") by " ++ showP prf
    AssertTerm h tm Nothing -> "assert _ as " ++ h ++ " by " ++ showP (Concat [Refine tm, Oracle])
    AssertTerm h tm (Just ih) -> "assert _ as " ++ h ++ " by " ++ showP (Concat [Refine tm, Clear ih, Oracle])
    Intros pats -> "intros " ++ unwords (map show pats)
    Revert xs -> "revert " ++ unwords xs
    GeneralizeDependent xs -> intercalate "; " $ map (\x -> "try revert " ++ subsetWitnessNm x ++ "; generalize dependent " ++x) xs
    SpecializeIH ih _ _ _ _ y _ newIh -> unwords ["specTac", ih, showP y] ++ maybe "" (" as " ++) newIh
    Specialize hyp ts -> "specialize (" ++ hyp ++ concatMap ((" " ++) . showP) ts ++ ")"
    Clear hyp -> "clear " ++ hyp
    ClearDependent hyp -> "clear dependent " ++ hyp
    Inversion hyp pat -> "inversion " ++ hyp ++ " as " ++ "[" ++ patS ++ "]"
      where
        patS = intercalate " | " $ map unwords pat
    where
      prt = prettyPrint indent
      -- \| comparison operator to alphabetically order branches of Induction/Destruct
      ordFunc :: (Id, (CoqDestrPat, [CoqTactic])) -> (Id, (CoqDestrPat, [CoqTactic])) -> Ordering
      ordFunc ("true", _) ("false", _) = LT
      ordFunc ("false", _) ("true", _) = GT
      ordFunc br br' = compare (fst br) (fst br')
  includesBranches tac = case tac of
    Concat [] -> False
    Concat tacs -> includesBranches (last tacs)
    SplitB {} -> True
    Destruct Var {} _ -> True
    Destruct _ _ -> False
    Induction {} -> True
    SubgoalMarkers {} -> True
    _ -> False

instance Show CoqTactic where
  show = prettyPrint 1

admitted :: [CoqTactic] -> Bool
admitted = any containsAdmit
  where
    containsAdmit tac = case tac of
      Admit {} -> True
      Try t -> containsAdmit t
      Timeout _ t -> containsAdmit t
      Replace _ _ t _ -> containsAdmit t
      Destruct _ cases -> admitted $ concatMap (snd . snd) cases
      Induction _ cases -> admitted $ concatMap (snd . snd) cases
      Assert _ _ t -> containsAdmit t
      Now t -> containsAdmit t
      SubgoalMarkers ts -> admitted ts
      SplitB ts ts' -> admitted ts || admitted ts'
      Concat ts -> admitted ts
      Branches ts -> admitted ts
      _ -> False

-- * Suable and AppSuable instances

instance AppSuable (Id, RocqType) CoqTerm where
  findAndReplace p (x, tp) = let (ms, fO) = findAndReplace p tp in (ms, (\f -> Just $ \t -> (x, f t)) =<< fO)

instance Suable CoqTerm CoqTerm where
  sub = replaceSubterm . (,True) . IdPat

instance AppSuable CoqTerm CoqTerm where
  findAndReplace pat tm = ifNotFullMatch pat tm $ case tm of
    Def y -> mapId Def y
    Abbr y -> mapId Abbr y
    Bop op s t -> recurseFindAndRepl2 pat (Bop op) s t
    Var y -> mapId Var y
    App (App f ts) us -> findAndReplace pat $ App f (ts ++ us)
    App f ts -> recurseFindAndReplApp pat App f ts
    Cr y -> mapId Cr y
    -- \| if we have a substitution of a variable shadowed by the lambda ignore the entire body of the lambda
    Lambda y typ s | isSubsId (Var y) -> resRec [] (const $ Lambda y typ s)
    Lambda y typ s -> recurseFindAndRepl2 pat (Lambda y) typ s
    Project (Exist _ t _) -> findAndReplace pat t
    Project t -> recurseFindAndRepl pat Project t
    SubCast need have t z -> recurseFindAndRepl4 pat SubCast need have t z
    Exist p t z -> recurseFindAndRepl3 pat Exist p t z
    Match ts idO cases -> resRec matches func
      where
        matches = concatMap (findSubterm pat) ts ++ concatMap (findSubterm pat . snd) cases
        func r = Match (map (replaceSubterm pat r) ts) idO (mapSnd (replaceSubterm pat r) cases)
    Ite r s t -> recurseFindAndRepl3 pat Ite r s t
    Let y _ _ | isSubsId (Var y) -> error $ "nameclash between supposedly free variable in substitution and new variable name in pattern: " ++ showSubst
    -- \| if we have a substitution of a variable shadowed by the let ignore the entire body of the let
    Let y s t -> recurseFindAndRepl pat (\u -> Let y u t) s
    PrfTerm r z -> recurseFindAndRepl2 pat PrfTerm r z
    IsTrue b -> recurseFindAndRepl pat IsTrue b
    Forall args _ | capturedIn args -> unchanged
    Forall args ref -> recurseFindAndReplFuncBind pat Forall args ref
    Exists args _ | capturedIn args -> unchanged
    Exists args ref -> recurseFindAndReplFuncBind pat Exists args ref
    And p q -> recurseFindAndRepl2 pat And p q
    Or p q -> recurseFindAndRepl2 pat Or p q
    Impl a c -> recurseFindAndRepl2 pat Impl a c
    Equiv a c -> recurseFindAndRepl2 pat Equiv a c
    Neg f -> recurseFindAndRepl pat Neg f
    NegB f -> recurseFindAndRepl pat NegB f
    -- \| literals, TermHole
    _ -> unchanged
    where
      showSubst = show pat
      mapId op y = if isSubstOf pat y then mkRes [op y] id else unchanged
      isSubsId t = case t of
        Def y -> xO == Just y
        Abbr y -> xO == Just y
        Var y -> xO == Just y
        Cr y -> xO == Just y
        _ -> False
      capturedIn args = case xO of
        Just x -> x `elem` map fst args
        _ -> False
      xO = case pat of
        (TermPat (Var x), True) -> Just x
        (IdPat x, True) -> Just x
        _ -> Nothing
      mkRes :: [b] -> (b -> a) -> ([b], Maybe (b -> a))
      mkRes matches f = (matches, if null matches then Nothing else Just f)

instance Suable RocqType CoqTerm where
  sub = replaceSubterm . (,True) . IdPat

instance AppSuable ArgListT CoqTerm where
  findAndReplace p (ArgListT xTs) = resRec matches func
    where
      matches = concatMap (findSubterm p . snd) xTs
      func r = ArgListT (mapSnd (replaceSubterm p r) xTs)

instance Suable ArgListT CoqTerm where
  sub = replaceSubterm . (,True) . IdPat

instance AppSuable RocqType CoqTerm where
  findAndReplace p tp = case tp of
    ArgumentList argList -> recurseFindAndRepl p ArgumentList argList
    Builtin _ -> unchanged
    Sort _ -> unchanged
    Subset x a r -> case p of
      (_, True) | isSubst x -> unchanged
      (_, False) | isSubst x -> recurseFindAndRepl p (Subset y a) r
      _ -> recurseFindAndRepl p (Subset x a) r
      where
        y = case fst p of
          IdPat v -> v
          TermPat (Var v) -> v
          _ -> x
    TC tc args | isSubst tc -> resRec (concatMap (findSubterm p) args) func
          where
            func r = case r of
              Var tc' -> TC tc' args
              _ -> error "name-clash between supposedly free-variable in substitution and type-constructor"
    -- For now, forget about args, should be empty, so no substitution needed
    TC _ [] -> unchanged
    TC {} -> error "Found TC with non-empty arguments"
    Arrow _ _ -> unchanged
    FAType (x, _) _ | capturedIn x -> unchanged
    FAType (x, tx) t -> recurseFindAndReplFuncBind p (\[arg] -> FAType arg) [(x, tx)] t
    Prop r -> recurseFindAndRepl p Prop r
    UPack _ _ -> unchanged
    Pack (ArgListT xTs) uargTps z t q -> resRec matches func
          where
            matches = concatMap (findSubterm p . snd) xTs ++ findSubterm p t ++ findSubterm p q
            func r = Pack (ArgListT (mapSnd (replaceSubterm p r) xTs)) uargTps (replaceSubterm p r z) (replaceSubterm p r t) (replaceSubterm p r q)
    Hole -> unchanged
    where
      isSubst x = case fst p of
        IdPat y -> x == y
        TermPat (Var y) -> x == y
        _ -> False
      capturedIn x = case p of
        (IdPat y, False) -> x == y
        (TermPat (Var y), False) -> x == y
        _ -> False

instance AppSuable BaseSort CoqTerm where
  findAndReplace _ _ = unchanged

instance Suable BaseSort CoqTerm where
  sub = replaceSubterm . (,True) . IdPat

instance AppSuable CoqDestrPat CoqTerm where
  findAndReplace p dpat = case dpat of
    ConjDestrPat dpats -> recurseFindAndRepls p ConjDestrPat dpats
    DisjDestrPat dpats -> recurseFindAndRepls p DisjDestrPat dpats
    SingleIdPat x -> if isSubstOf p x then error $ "name-clash between supposedly free-variable in substitution and id in pattern: " ++ x {-mkRes [SingleIdPat x] id -} else unchanged
    UnnamedIdPat -> unchanged

instance Suable CoqDestrPat CoqTerm where
  sub = replaceSubterm . (,True) . IdPat

instance AppSuable CoqIntroPat CoqTerm where
  findAndReplace p ipat = case ipat of
    DestrPat dp -> recurseFindAndRepl p DestrPat dp
    RewritePat _ -> unchanged

instance Suable CoqIntroPat CoqTerm where
  sub = replaceSubterm . (,True) . IdPat

instance AppSuable CoqTactic CoqTerm where
  findAndReplace p tac = case tac of
    Apply t -> recurseFindAndRepl p Apply t
    Destruct t cases -> resRec matches func
      where
        matches = findSubterm p t ++ concatMap ((\(pat, tacs) -> findSubterm p pat ++ concatMap (findSubterm p) tacs) . snd) cases
        func r = Destruct (replaceSubterm p r t) (map (second (bimap (replaceSubterm p r) (map $ replaceSubterm p r))) cases)
    Induction t branches -> resRec matches func
      where
        matches = findSubterm p t ++ concatMap ((\(pat, tacs) -> findSubterm p pat ++ concatMap (findSubterm p) tacs) . snd) branches
        func r = Destruct (replaceSubterm p r t) (map (second (bimap (replaceSubterm p r) (map $ replaceSubterm p r))) branches)
    Exact t -> recurseFindAndRepl p Exact t
    Refine t -> recurseFindAndRepl p Refine t
    RefineT t -> recurseFindAndRepl p RefineT t
    SubgoalMarkers tacs -> recurseFindAndRepls p SubgoalMarkers tacs
    Concat tacs -> recurseFindAndRepls p Concat tacs
    Branches tacs -> recurseFindAndRepls p Branches tacs
    SplitB tacs moreTacs -> recurseFindAndRepls2 p SplitB tacs moreTacs
    ApplyPartial t -> recurseFindAndRepl p ApplyPartial t
    DestructSubsetTerm t pat -> recurseFindAndRepl2 p DestructSubsetTerm t pat
    -- DestructConj h h1 h2 -> recurseFindAndRepl3 p DestructConj h h1 h2
    Replace s t tc hO -> recurseFindAndRepl2 p (\s' t' -> Replace s' t' tc hO) s t
    Assert h _ _ | isSubstOf p h -> error $ "name-clash between supposedly free-variable in substitution and label of assert: " ++ h
    Assert h r z -> recurseFindAndRepl2 p (Assert h) r z
    AssertTerm h _ _ | isSubstOf p h -> error $ "name-clash between supposedly free-variable in substitution and label of AssertTerm: " ++ h
    AssertTerm h term idO -> recurseFindAndRepl p (\tm -> AssertTerm h tm idO) term
    Intros pats -> case fst p of
      IdPat _ -> resRec matches func
        where
          matches = concatMap (findSubterm p) pats
          func r = Intros $ map (replaceSubterm p r) pats
      _ -> unchanged
    _ -> unchanged

instance Suable CoqTactic CoqTerm where
  sub = replaceSubterm . (,True) . IdPat

{-
sub x tm tac = case tac of
  Rewrite dirO hyp hO -> Rewrite dirO (subs hyp) hO
  Replace s t tc hO -> Replace (subs s) (subs t) (subs tc) hO
  Assert h r z | h == x -> case tm of
    Var h' -> Assert h' r z
    _ -> error $ "name-clash between supposedly free-variable in substitution and label of assert: " ++ x
  Assert h r z -> Assert h (subs r) (subs z)
  AssertTerm h term idO -> AssertTerm h (subs term) idO
  Intros pats -> Intros (map subs pats)
  _ -> tac
  where
    subs :: (Suable a CoqTerm) => a -> a
    subs = sub x tm
-}

instance AppSuable ProofTerm CoqTerm where
  findAndReplace p z = case z of
    TermWitness t -> recurseFindAndRepl p TermWitness t
    RefWitness tm -> recurseFindAndRepl p RefWitness tm
    Conj q r -> recurseFindAndRepl2 p Conj q r
    _ -> unchanged

instance Suable ProofTerm CoqTerm where
  sub = replaceSubterm . (,True) . IdPat

instance Suable (Id, RocqType) CoqTerm where
  sub x _ (y, _) | y == x = error $ "name-clash between supposedly free-variable in substitution and identifier in arg: " ++ x
  sub x tm (y, tp) = (y, sub x tm tp)

-- * Other misc instance definitions and functions

instance Binder CoqDecl where
  bindName d = case d of
    TCDecl tc _ -> tc
    Fix n _ _ _ -> n
    Definition f _ _ _ _ -> f
    CoqAxiom ax _ _ -> ax
    CoqInductive tc _ _ _ -> tc
    CoqAlias n _ -> n
    CoqNewType t _ -> t
    -- \| load, visibility modifier, hint
    _ -> ""
