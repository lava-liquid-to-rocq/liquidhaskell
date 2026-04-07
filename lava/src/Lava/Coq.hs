{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{- {-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-} -}

-- |
-- - (E)Coq grammar, printer to .ecoq file and suable functions
module Lava.Coq where

import Data.Bifunctor
import Data.Data
import Data.List (sortBy, isSuffixOf, unsnoc)
import Text.PrettyPrint
import Text.PrettyPrint.HughesPJClass hiding (first)
import Prelude hiding ((<>))
import Lava.Names (Id)
import Lava.Calculus (arrPrec, appPrec)

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
upackName :: Id
projPackName :: Id
packName = "@Pack"
upackName = "@uPack"
projPackName = "packProj"

subsetWitnessNm :: Id -> Id
subsetWitnessNm x = x ++ "_p"

xorb :: Id
implb :: Id
negb :: Id
negB :: Id
unitTmName :: Id
btrueTmName :: Id
bfalseTmName :: Id
unitTm :: CoqTerm
btrue :: CoqTerm
bfalse :: CoqTerm
boolTp :: RocqType
unitTp :: RocqType
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
unitTp = TC "Unit" []
{- ORMOLU_ENABLE -}

-- | List of builtin CoqInductives
coqBuiltinInductDataTypes :: [RocqType]
coqBuiltinInductDataTypes = [boolTp, unitTp]

-- * The actual ECoq grammar

-- ** The (module and) declaration-level grammar

-- | A named ECoq module containing some declarations
--
-- > M ::= Module x. D* End x.
data CoqModule = CoqModule Id [Decl] deriving (Eq, Data)

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
data Decl
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
  | TacInstance Id RocqType Tactic
  deriving (Eq, Data)

data DefBody
  = ProofBody [Tactic]
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
  | UPack UArgListT RocqType
  | Pack ArgListT UArgListT CoqTerm RocqType CoqTerm
  | ArgumentList ArgListT
  | Hole
  deriving (Eq, Data)

newtype ArgListT = ArgListT [(Id, RocqType)] deriving (Eq, Data)
newtype ArgList = ArgList [CoqTerm] deriving (Eq, Data)
newtype UArgListT = UArgListT [RocqType] deriving (Eq, Data)
newtype UArgList = UArgList [CoqTerm]

mkArgListT :: ArgListT -> CoqTerm
mkArgListT (ArgListT xs) = foldl (\tlTm (x,t) -> Bop ConsRT (TypeArg t) $ Lambda x t tlTm) (Def "nilRT") (reverse xs)

mkUArgListT :: UArgListT -> CoqTerm
mkUArgListT (UArgListT xs) = foldl (\tlTm t -> Bop ConsUT (TypeArg t) tlTm) (Def "nilUT") (reverse xs)

mkArgList :: ArgList -> CoqTerm
mkArgList (ArgList args) = foldl (flip (Bop ConsR)) (Def "nilR") args

mkUArgList :: UArgList -> CoqTerm
mkUArgList (UArgList uargs) = foldl (flip (Bop ConsU)) (Def "nilU") uargs

-- | An ECoq term of any kind
--
-- > e ::= ∀(x:tp)*, e | exists (x:tp)*, e
-- >     | e /\ e | e \/ e | e -> e | e <-> e | not e | True | False | is_true e
-- >     | x ∈ (Def, Abbr, Var, Cr) | e bop e | "s" (s ∈ String) | I n (n ∈ Z) | F f (f ∈ Float)
-- >     | e e* | λx:tp.e
-- >     | ⌊e⌋ | subCast R R e p | exist e e p
-- >     | match (e,)* with (| c x* => e)* | if e then e else e | let x := e in e
-- >     | _ | p
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
  | Proj2sig CoqTerm
  | SubCast RocqType RocqType CoqTerm ProofTerm
  | Exist {cRefPred :: CoqTerm, cExistTerm :: CoqTerm, cExistPrf :: ProofTerm}
  | Match [CoqTerm] (Maybe Id) [([(Id, [Id])], CoqTerm)]
  | Ite CoqTerm CoqTerm CoqTerm
  | Let Id (Maybe RocqType) CoqTerm CoqTerm
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
  | ByTac Tactic
  | RefWitness CoqTerm
  | Conj ProofTerm ProofTerm
  deriving (Data, Eq)

-- | represents supported ECoq tactics, both custom tactics and basic Coq tactics (@tac@)
data Tactic
  = Easy
  | Oracle
  | -- In the branches, the Id is the name of the constructor in the branch (useful for reordering in the order needed by Coq)
    Destruct {destrExpr :: CoqTerm, destrBranches :: [(Id, (CoqDestrPat, [Tactic]))]}
    -- Like in LH, Induction contains the generalized varibles
  | Induction {indTerm :: CoqTerm, indBranches :: [(Id, (CoqDestrPat, [Tactic]))], indGenVars :: [Id]}
  | Exact CoqTerm
  | Admit [Id]
  | Pose Id CoqTerm
  | ProofPose Id CoqTerm
  | Try Tactic
  | Refine CoqTerm
  | -- ToDo: Extend to a more useful version of this tactic
    DestructSubsetTerm CoqTerm CoqDestrPat
  | DestructConj Id Id Id
  | Rewrite (Maybe RewriteDir) CoqTerm (Maybe Id)
  | Assert {assHypName :: Id, assClaim :: Goal, assPrf :: Tactic}
  | AssertTacs Id RocqType [Tactic]
  | Intros [CoqIntroPat]
  | GeneralizeDependent [Id]
  | Clear Id
  | Concat [Tactic]
  | Branches [Tactic]
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

-- * Constructors

-- | Build Concat [tacs] where [tacs] does not contain another concat
mkConcat :: [Tactic] -> Tactic
mkConcat = Concat . concatMap (\case Concat tacs' -> tacs'; tac -> [tac])

-- * Destructors

fromSubset :: RocqType -> (Id, RocqType, CoqTerm)
fromSubset (Subset x tpx rx) = (x, tpx, rx)
fromSubset _ = error "Subset expected"

-- * Functions on the grammar

-- | Regroup forall arguments
concatForalls :: RocqType -> ([(Id, RocqType)], RocqType)
concatForalls (FAType arg tp) = first (arg :) $ concatForalls tp
concatForalls tp = ([], tp)

-- | Whether a proposition is trivially equivalent to True
isTrivial :: CoqTerm -> Bool
isTrivial TT = True
isTrivial (IsTrue b) = simplifyIsTrue b == TT
isTrivial _ = False

-- * Printer for grammar

-- | Wrap document in (*...*)
rocqComment :: Doc -> Doc
rocqComment doc = "(*" <+> doc <+> "*)"

dot :: Doc -- ^ A '.' character
dot = char '.'

{- ORMOLU_DISABLE -}
-- ** Precedence levels

nodotPrec :: Rational
concatPrec :: Rational
dotPrec :: Rational
nodotPrec = 0
concatPrec = 1
dotPrec = 2

bopPrec :: Bop -> Rational
bopPrec Eq = 4
bopPrec EqProp = 4
bopPrec Neq = 4
bopPrec Leq = 4
bopPrec Geq = 4
bopPrec Lt = 4
bopPrec Gt = 4
bopPrec Plus = 6
bopPrec Minus = 6
bopPrec Times = 7
bopPrec Div = 7
bopPrec Mod = 7
bopPrec Leqb = 4
bopPrec Geqb = 4
bopPrec Eqb = 4
bopPrec Neqb = 4
bopPrec Ltb = 4
bopPrec Gtb = 4
bopPrec Andb = 3
bopPrec Orb = 2
bopPrec ImplB = 1
bopPrec EqualB = 4
bopPrec NEqualB = 4
bopPrec Equal = 4
bopPrec EqualBProp = 4
bopPrec EqBool = 4
bopPrec PlusU = 6
bopPrec MinusU = 6
bopPrec TimesU = 7
bopPrec DivU = 7
bopPrec ModU = 7
bopPrec ConsRT = 5
bopPrec ConsUT = 5
bopPrec ConsR = 5
bopPrec ConsU = 5
{- ORMOLU_ENABLE -}

-- | Appends the correct punctuation at the end of a doc (used for tactics)
dotted :: Rational -> Doc -> Doc
dotted p d =
  let sign
        | p == nodotPrec = empty
        | p == concatPrec = semi
        | otherwise = dot
   in d <> sign

-- | Prints the correct bullet according to the value of p
rocqBullet :: Rational -> Doc
rocqBullet p =
  -- if p' == 0 || p == 1 then error "Cannot print bullet inside concatenation of tactics."
  if p == nodotPrec || p == concatPrec then empty
  else let bullet
             | p' == truncate dotPrec = char '-'
             | p' == truncate dotPrec + 1 = char '+'
             | otherwise = char '*'
        -- negations to obtain the ceiling from the division
        in hcat $ replicate (-((-p') `div` 3)) bullet
  where p' :: Int
        p' = truncate p

-- | Number of indentation spaces
identNb :: Int
identNb = 2

-- | Prints and adds parenthesis. Can be optimized to not always add parenthesis
pPrintP :: (Pretty a) => a -> Doc
pPrintP = parens . pPrint

pPrintArg :: (Pretty a) => (Id, a) -> Doc
pPrintArg (x, tp) = text x <> colon <+> pPrint tp

pPrintArgs :: (Pretty a) => [(Id, a)] -> Doc
pPrintArgs args = sep $ map (parens . pPrintArg) args

pPrintImpArg :: (Pretty a) => ((Id, a), Bool) -> Doc
pPrintImpArg ((x, tp), isImplicit) = (if isImplicit then brackets else parens) (pPrintArg (x, tp))

instance Pretty CoqModule where
  pPrint (CoqModule name decls) =
     "module" <+> text name <+> vcat (punctuate "; " (map pPrint decls))

instance Pretty CoqConstr where
  pPrint (Constr c tp) = pPrintArg (c, tp)

instance Pretty CoqTermTC where
  pPrint (InductiveData n constrs) =
     "Inductive" <+> text n <>  ": Set :="
     $$ nest identNb (sep (map (("|" <+>) . pPrint) constrs))

instance Pretty Decl where
  pPrint (TCDecl n constrs) = "Inductive" <+> text n <>  ": Set :="
    $$ nest identNb (sep (map (("|" <+>) . pPrint) constrs))
  pPrint (Definition f args ret body vis) =
    case body of
      ProofBody tacs -> header <> dot
        $$ "Proof."
        $$ nest identNb (sep $ map pPrint tacs)
        $$ (if admitted tacs then "Admitted" else qedSym) <> dot
      TermBody expr -> header <> " :=" $$ nest identNb (pPrint expr <> dot)
    where
      header = case ret of
        Prop {} | vis == Opaque -> "Theorem" <+> sign
        _ ->  "Definition" <+> sign
      sign = sep [text f <+> sep (map pPrintImpArg args) <> colon, pPrint ret]
      qedSym = case vis of
        Transparent -> "Defined"
        Opaque -> "Qed"
  pPrint (Fix f args ret tm) =
     "Fixpoint" <+> text f <+>
    sep (map pPrintImpArg args) <> colon <+> pPrint ret <+>  ":="
    $$ nest identNb (pPrint tm <> dot)
  pPrint (Load m) =  "Load" <+> text m <> dot
  pPrint (CoqAlias f e) =
    sep [ "Notation" <+> text f <+>  ":=", pPrint e <> dot]
  pPrint (CoqNewType t tp) =
     "Global Notation" <+> text t <+>  ":=" <+> pPrintRocqType tp False <> dot
  pPrint (CoqAxiom ax args claim) =
     "Axiom" <+> text ax <> colon <+> pPrintForall (map fst args) claim <> dot
  pPrint (CoqInductive f args k constrs) =
    "Inductive" <+> text f <+> pPrintArgs args
      <> colon <+> pPrintP k <+> ":="
      $$ nest identNb (sep (map (("|" <+>) . pPrint) constrs) <> dot)
  pPrint (CoqMarkVisibility v) = pPrint v
  pPrint (AddHint kind ax db) =
    "#[global] Hint" <+> pPrint kind <+> pPrintArg (ax, db) <> dot
  pPrint (Instance instName tp opDefs) =
    "#[global] Instance" <+> text instName <> colon <+>
    hsep (map text tp) <+> ":=" <+> lbrace
    $$ nest identNb (vcat . punctuate semi $
      map (\(lookupOp, lookupRes) -> text lookupOp <+> ":=" <+> pPrint lookupRes) opDefs)
    <+> rbrace <> dot
  pPrint (TacInstance instName tp tac) =
    "#[global] Instance" <+> pPrintArg (instName, tp) <> dot
    $$ "Proof." <+> pPrint tac <+> "Defined."

instance Pretty ChangeVisibility where
  pPrint (ChangeVisibility f Transparent) = "Transparent" <+> text f <> char '.'
  pPrint (ChangeVisibility f Opaque) = "Opaque" <+> text f <> char '.'

instance Pretty HintKind where
  pPrint UnfoldHint = "Unfold"
  pPrint ConstructorsHint = "Constructors"
  pPrint ResolveHint = "Resolve"
  pPrint RewriteHint = "Rewrite"

instance Pretty HintDatabase where
  pPrint RefConstrDB = "ref_constr_db"
  pPrint WfDB = "wf_constr_db"
  pPrint GraphRelDB = "f_rel_funct_db"
  pPrint CoreDB = "core_hint_db"
  pPrint GraphRelBackDB = "f_rel_back"
  pPrint RelAxDB = "rel_ax_db"
  pPrint EqHintDb = "eq_hint_db"

instance Pretty Builtin where
  pPrint CTInt = "Z"
  pPrint CTString = "String"
  pPrint CTFloat = "Float"

-- The flag indicates if we use our notations on subset types
-- (Bool for {_:bool|True} and {{…}} for a lemma)
pPrintRocqType :: RocqType -> Bool -> Doc
pPrintRocqType (Builtin b) _ = pPrint b
pPrintRocqType (Sort sort) _ = pPrint sort
-- NOTE: for TC, there are cases where me might need to add (getTCRef x tc), the well-formedness predicate (as in prntRefType)
pPrintRocqType (Subset x tc@(TC tc' []) e) True = case tc' of
  "bool" | isTrivial e -> "Bool"
  "Unit" -> braces (braces (pPrint e))
  _ -> case e of
    _ | tc `elem` coqBuiltinInductDataTypes -> braces (pPrintArg (x, tc) <+> "|" <+> pPrint e)
    And (App (Def wf) [Var x']) true | x == x' && wf == wfTCName tc' && isTrivial true -> pPrint tc
    _ -> braces (pPrintArg (x, tc) <+> "|" <+> pPrint e)
pPrintRocqType (Subset x tp e) _ =
  braces (pPrintArg (x, tp) <+> "|" <+> pPrint e)
pPrintRocqType tc@(TC tc' []) _ | tc `elem` coqBuiltinInductDataTypes = text tc'
pPrintRocqType (TC typeName tpArgs) _ =
  hsep $ text typeName : map pPrint tpArgs
pPrintRocqType (Arrow tp1 tp2) _ = sep [pPrintP tp1, "->" <+> pPrintP tp2]
pPrintRocqType tp@(FAType {}) _ = let (args, ret) = concatForalls tp in pPrintForall args ret
pPrintRocqType (Prop p) _ = pPrint p
pPrintRocqType (UPack uargTps t) _ =
  sep [text upackName, pPrintP uargTps, pPrintP t]
pPrintRocqType (ArgumentList argTps) _ = parens ("ArgList" <+> pPrint argTps)
pPrintRocqType (Pack argTps uargTps z t p) _ = parens . sep $
  [pPrint packName, pPrintP argTps, pPrintP uargTps, pPrintP z, pPrintP t, pPrintP p]
pPrintRocqType Hole _ = char '_'

-- TODO: we probably want to use Maybe instead of using '_'
pPrintForall :: (Pretty a) => (Pretty b) => [(Id, a)] -> b -> Doc
pPrintForall [] ret = pPrint ret
pPrintForall (("_", t) : tl) ret = sep [pPrint t, "->", pPrintForall tl ret]
pPrintForall args ret =
  sep [if null args then empty else "forall" <+> sep (map printArg args) <> comma, pPrint ret]
  where
    printArg (x, tp) =
      if pPrint tp == char '_' then text x
      else parens (text x <+> colon <+> pPrint tp)

instance Pretty RocqType where
  pPrint tp = pPrintRocqType tp True

instance Pretty BaseSort where
  pPrint PropSort = "Prop"
  pPrint TypeSort = "Type"
  pPrint SetSort = "Set"

instance Pretty CoqTerm where
  pPrint (IsTrue b) =
    let b' = simplifyIsTrue b
     in if b' == b then "is_true" <+> pPrintP b else pPrint b'
  pPrint (Forall vars p) = pPrintForall vars p
  pPrint (Exists vars p) =
     sep [if null vars then empty else "exists" <+> pPrintArgs vars <> comma, pPrint p]
  pPrint (And p q) = pPrintP p <+> "/\\" <+> pPrintP q
  pPrint (Or p q) = pPrintP p <+> " \\/" <+> pPrintP q
  pPrint (Impl p q) = pPrintP p <+> "->" <+> pPrintP q
  pPrint (Equiv p q) = pPrintP p <+> "<->" <+> pPrintP q
  pPrint (Neg (IsTrue (Bop EqualB s t))) = pPrint . IsTrue $ Bop Neqb s t
  pPrint (App neg [Bop EqualB s t]) | neg == Def negb = pPrint $ Bop NEqualB s t
  pPrint (Neg (Neg p)) = pPrint p
  pPrint (Neg p) = "not" <+> pPrintP p
  pPrint (NegB (NegB p)) = pPrint p
  pPrint (NegB p) = pPrint negB <+> pPrintP p
  pPrint TT = "True"
  pPrint FF = "False"
  pPrint (Def s) = text s
  pPrint (Abbr s) = text s
  pPrint (Bop bop s t) = pPrintP s <+> pPrint bop <+> pPrintP t
  pPrint (Var x) = text x
  pPrint (StringLiteral s) = quotes (pPrint s)
  pPrint (IntLiteral n) = integer n
  pPrint (FloatLiteral f) = double f
  pPrint (App f ts) = sep (map pPrintP (f : ts))
  pPrint (Cr s) = text s
  pPrint (Lambda x a s) = "fun" <+> parens (pPrintArg (x, a)) <+> "=>" <+> pPrintP s
  pPrint (Project t) =
    let t' = simplifyProject t in
     if t' == t then char '⌊' <+> pPrint t <+> char '⌋' else pPrint t'
  pPrint (Proj2sig t) = char '⌈' <+> pPrint t <+> char '⌉'
  pPrint tm@(SubCast to from t z) =
    let tm' = simplifySubCast tm
     in if tm == tm' then
       case (to, from) of
          (Hole, _) -> sep ["subsumptionCast", char '_', char '_', pPrintP t, pPrintP z]
          (Subset n b need, Subset _ a _) | a == b ->
            sep ["subsumptionCast", pPrintP a, pPrintP (Lambda n a need), pPrintP t, pPrintP z]
          _ -> sep ["subCast", pPrintP from, pPrintP to, pPrintP t, pPrintP z]
      else pPrint tm'
  pPrint (Exist _ t (CoqProofTerm "I")) = char '#' <+> pPrint t
  pPrint (Exist p t z) = "exist" <+> pPrintP p <+> pPrintP t <+> pPrintP z
  pPrint (Match ts _ cases) =
    sep $ ("match" <+> parens (hsep $ punctuate comma (map pPrint ts)) <+> "with") :
      map (("|" <+>) . printCase) cases ++ ["end"]
    where
      printCase (pat, tm) =
        parens (hsep . punctuate comma $ map (\(c, args) -> hsep $ map text (c : args)) pat)
        <+> "=>" <+> pPrint tm
  pPrint (Ite r s t) = "if" <+> pPrint r <+> "then" <+> pPrint s <+> "else" <+> pPrint t
  pPrint (Let x tp s t) =
    sep ["let" <+> maybe (text x) (\tp' -> pPrintArg (x, tp')) tp <+> ":=", pPrint s <+> "in", pPrint t]
  pPrint (InstanceProjection inst field) = pPrintP inst <> dot <> parens (text field)
  pPrint (InlineInstance fields) =
    sep ["{|", sep . punctuate semi $ map (\(field, val) -> pPrint field <+> ":=" <+> pPrint val) fields, "|}"]
  pPrint (TypeArg tp) = pPrint tp
  pPrint TermHole = char '_'
  pPrint (PrfTerm _ z) = pPrint z

-- | Syntactic simplification of is_true(tm)
simplifyIsTrue :: CoqTerm -> CoqTerm
simplifyIsTrue tm = case tm of
    App neg [f] | neg == Def negb -> Neg (IsTrue f)
    App impl [a, c] | impl == Def implb -> Impl (IsTrue a) (IsTrue c)
    (Bop ImplB a c) -> Impl (IsTrue a) (IsTrue c)
    (Bop EqualBProp s t) -> Bop EqProp s t
    -- (Bop EqualB s t) -> Bop Eq (IsTrue s) (IsTrue t) -- C.PExpr . C.eqTrue $ mkBEqual decls ctx CTBool s t
    (App (Def ngb) [f])  | ngb == negb -> Neg (IsTrue f)
    -- (Bop Neqb s t) -> Bop Neq (IsTrue s) (IsTrue t)
    (Bop EqualB s t)  | boolHeuristic s || boolHeuristic t -> Bop EqProp (IsTrue s) (IsTrue t)
    --(Bop Neqb s t)    | boolHeuristic s || boolHeuristic t -> Bop Neq (IsTrue s) (IsTrue t)
    (Bop EqualB s t)  | nonBoolHeuristic s || nonBoolHeuristic t -> Bop Eq s t
    (Bop EqualB s t) -> Bop Equal s t
    (Bop Neqb s t)    | boolHeuristic s || boolHeuristic t -> Neg (Bop EqProp (IsTrue s) (IsTrue t))
    (Bop Neqb s t)    {- | nonBoolHeuristic s || nonBoolHeuristic t -} -> Bop Neq s t
    (Bop Andb s t) -> And (IsTrue s) (IsTrue t)
    (Bop Orb s t) -> Or (IsTrue s) (IsTrue t)
    (Bop Leqb s t) -> Bop Leq s t
    (Bop Ltb s t) -> Bop Lt s t
    (Bop Geqb s t) -> Bop Geq s t
    (Bop Gtb s t) -> Bop Gt s t
    (Bop Eqb s t) -> Bop Eq s t
    b | b == btrue -> TT
    b | b == bfalse -> FF
    _ -> tm
  where
    boolHeuristic t = case t of
      Bop op _ _ ->
        op `elem` [ImplB, EqualB, EqualBProp, Neqb, Andb, Orb, Leqb, Ltb, Geqb, Gtb, Eqb]
      IsTrue (App impl _) -> impl == Def implb
      (TT; FF) -> True
      _ -> t == btrue || t == bfalse
    nonBoolHeuristic t | boolHeuristic t = False
    nonBoolHeuristic (Bop{}; Project{}; Exist{}; SubCast{}; IsTrue{}; Cr{}) = True
    nonBoolHeuristic _ = False

-- | Syntactic simplification of Project
simplifyProject :: CoqTerm -> CoqTerm
simplifyProject proj = case proj of
  Exist _ t _ -> t
  Bop Plus s t -> Bop PlusU (simplifyProject s) (simplifyProject t)
  Bop Minus s t -> Bop MinusU (simplifyProject s) (simplifyProject t)
  Bop Times s t -> Bop TimesU (simplifyProject s) (simplifyProject t)
  Bop Div s t -> Bop DivU (simplifyProject s) (simplifyProject t)
  Bop Mod s t -> Bop ModU (simplifyProject s) (simplifyProject t)
  Cr c | unrefinedConstrName "" `isSuffixOf` c -> Cr c
  Cr c -> Cr $ unrefinedConstrName c
  App (Cr c) args -> App (Cr c') (map simplifyProject args)
       where c' = if unrefinedConstrName "" `isSuffixOf` c then c else unrefinedConstrName c
  NegB p -> Neg (Project p)
  SubCast _ _ t _ -> simplifyProject t
  _ -> proj

-- | Syntactic simplification of SubCast to exist
simplifySubCast :: CoqTerm -> CoqTerm
simplifySubCast (SubCast (Subset n b need) _ (Exist _ tm ProofHole{}) (ProofHole idO)) =
    Exist (Lambda n b need) tm (ProofHole idO)
simplifySubCast (SubCast (Subset n b need) _ (Exist _ tm CoqProofTerm{}) (ProofHole idO)) =
    Exist (Lambda n b need) tm (ProofHole idO)
simplifySubCast (SubCast Hole _ (Exist _ tm CoqProofTerm{}) (TermWitness TermHole)) =
    Exist TermHole tm (TermWitness TermHole)
simplifySubCast (SubCast Hole _ (Exist _ tm CoqProofTerm{}) (ProofHole idO)) =
    Exist TermHole tm (ProofHole idO)
simplifySubCast (SubCast Hole _ (Exist _ tm ProofHole{}) (TermWitness TermHole)) =
    Exist TermHole tm (TermWitness TermHole)
simplifySubCast (SubCast need have t _) | need == have && need /= Hole = t
simplifySubCast t = t

instance Pretty Bop where
  pPrint = text . show

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
  show Mod = error "TODO: support modulo in Rocq"
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

instance Pretty ProofTerm where
  pPrint (CoqProofTerm s) = text s
  pPrint (TermWitness tm) | tm == unitTm = char '_'
  pPrint (TermWitness t) = pPrint t
  pPrint (RefWitness tm) = char '⌈' <+> pPrint tm <+> char '⌉'
  pPrint (ProofHole Nothing) = "ltac:" <> parens (pPrintPrec prettyNormal nodotPrec Oracle)
  pPrint (ProofHole (Just h)) = "ltac:" <> parens (pPrintPrec prettyNormal nodotPrec (Concat [Try (Clear h), Oracle]))
  pPrint (ByTac tac) = "ltac:" <> parens (pPrintPrec prettyNormal 0 tac)
  pPrint (Conj l r) = "conj" <+> parens (pPrint l) <+> parens (pPrint r)

instance Pretty CoqDestrPat where
  pPrint pat = case pat of
    ConjDestrPat _ -> brackets (pPrintAux pat)
    DisjDestrPat _ -> brackets (pPrintAux pat)
    _ -> pPrintAux pat
    where
      pPrintAux (ConjDestrPat pats) = hsep $ map pPrint pats
      pPrintAux (DisjDestrPat pats) = hsep . punctuate "|" $ map pPrintAux pats
      pPrintAux UnnamedIdPat = char '_'
      pPrintAux (SingleIdPat n) = text n

instance Pretty RewriteDir where
  pPrint RwLR = "->"
  pPrint RwRL = "<-"

instance Pretty CoqIntroPat where
  pPrint (DestrPat p) = pPrint p
  pPrint (RewritePat rwDir) = pPrint rwDir

instance Pretty Tactic where
  -- We use the precedence to insert the right kind and number of bullets (-, + and *),
  -- and to know whether to put . or ; or nothing at the end of a tactic:
  -- - if p = 0, we use nothing (used before a parenthesis for instance) and if p = 1 we use ;
  --   (notice that we never use bullets in a list of tactics separated by ;)
  -- - if p > 1, we use . and we use the value of p to know what and how many bullets to put
  pPrint = pPrintPrec prettyNormal dotPrec
  pPrintPrec _ p Easy = dotted p "quicksolve"
  pPrintPrec _ p Oracle = dotted p "solver"
  pPrintPrec _ p (Admit hints) = dotted p $
    around (hsep (punctuate comma (map text hints))) <+> "admit"
    where around hs = if null hints then hs else rocqComment ("hints:" <+> hs)
  -- TODO: factorize printing of destruct and induction once the grammar is cleaned
  pPrintPrec l p (Destruct tm branches) =
    case tm of
    Var _ -> if nullBranches
      then dotted p destruct
      else hsep (destruct <> dot : map printTacBranch branchesSorted)
    _ -> sep
        ["let E := fresh \"E\" in", destruct <+> "eqn:E" <> if nullBranches then empty else semi,
        maybeBrackets (not nullBranches) (sep $ map (pPrintPrec l (p + 1) . mkConcat . snd) branchesSorted)]
    where
      branchesSorted = map snd $ sortBy ordFunc branches
      destruct = "destruct" <+> pPrint tm <+> "as" <+> pPrint (DisjDestrPat $ map fst branchesSorted)
      nullBranches = all (null . snd . snd) branches
      printTacBranch (_, tacs) = rocqBullet p <+> sep (map (pPrintPrec l (p + 1)) tacs)
  pPrintPrec l p (Induction t branches genVars) =
    if nullBranches then dotted p induct else dotted p gendepInduct $$ printTacBranches
    where
      branchesSorted = map snd $ sortBy ordFunc branches
      matchTac = if all ((== ConjDestrPat []) . fst . snd) branches && nullBranches then "destruct" else "induction"
      -- induction t as ...
      induct = text matchTac <+> pPrint t <+> "as" <+> pPrint (DisjDestrPat $ map fst branchesSorted)
      -- generalize dependent genVars
      gendeps =
        sep . punctuate semi $ map (\x -> "try revert" <+> text (subsetWitnessNm x) <> semi <+> "generalize dependent" <+> text x) genVars
      -- generalize dependent genVars; induction t as ...; intros
      gendepInduct =
        if null genVars then induct else sep $ punctuate semi [gendeps, induct, "intros"]
      nullBranches = all (null . snd . snd) branches
      -- The branches of an induct/destruct in a Concat are shown with [branch1 | … | branchn],
      -- and otherwise as - branch1. - … - branchn (with the correct bullet)
      printTacBranches =
        if p == concatPrec
        then dotted p (brackets . sep . punctuate " |" $ map (\(_, tacs) -> pPrintPrec l nodotPrec (mkConcat tacs)) branchesSorted)
        else vcat $ map (\(_, tacs) -> rocqBullet p <+> sep (map (pPrintPrec l (p + 1)) tacs)) branchesSorted
  pPrintPrec l p (Exact t) = case t of
    SubCast _ _ (Exist _ tm (CoqProofTerm prf)) (ProofHole _) | prf == "eq_refl" || prf == "I" ->
      refineOracle (Exist TermHole tm (TermWitness TermHole))
    SubCast _ have tm (ProofHole _) -> refineOracle (SubCast Hole have tm (TermWitness TermHole))
    SubCast _ have tm prf -> dotted p $ "exact" <+> parens (pPrint (SubCast Hole have tm prf))
    _ -> dotted p $ "refine" <+> pPrintP t
    where refineOracle x = sep ["refine" <+> parens (pPrint x) <> semi, pPrintPrec l p Oracle]
  pPrintPrec l p (Concat tacs) =
    case unsnoc tacs of
      Nothing -> empty
      Just (tacs', lastTac) ->
        dotted p . sep $ map (pPrintPrec l concatPrec) tacs' ++ [pPrintPrec l nodotPrec lastTac]
  pPrintPrec _ _ (Branches tacs) =
    if null tacs then empty else brackets . vcat . map pPrint $ tacs
  pPrintPrec _ p (Custom str) = dotted p $ text str
  pPrintPrec _ p Exfalso = dotted p "exfalso"
  pPrintPrec l p (Try t) = "try" <+> pPrintPrec l p t
  pPrintPrec l p (Refine t) = dotted p $ "refine" <+> parens (pPrintPrec l nodotPrec t)
  pPrintPrec _ p (DestructSubsetTerm tm destrPat) =
    dotted p $ "destruct" <+> pPrint tm <+> "as" <+> pPrint destrPat
  pPrintPrec _ p (DestructConj h h1 h2) =
    dotted p $ "destruct" <+> text h <+> "as" <+> brackets (text h1 <+> text h2)
  pPrintPrec _ p (Rewrite dir tm hyp) =
    dotted p $ "rewrite" <+> maybe empty pPrint dir <+> pPrintP tm
    <+> maybe empty ((<+>) "in" . text) hyp
  pPrintPrec _ p (Pose abbr tm) =
    dotted p $ "pose" <+> pPrintP tm <+> "as" <+> text abbr
  pPrintPrec _ p (ProofPose abbr tm) =
    dotted p $ "pose proof" <+> pPrintP tm <+> "as" <+> text abbr
  pPrintPrec _ p (Assert n claim prf) =
    dotted p $ "assert" <+> parens (pPrintArg (n, claim)) <+> "by" <+> parens (pPrint prf)
  pPrintPrec _ p (Intros pats) =
    dotted p $ "intros" <+> sep (map pPrint pats)
  pPrintPrec _ p (GeneralizeDependent xs) =
    dotted p $ sep . punctuate semi $ map (\x -> "try revert" <+> text (subsetWitnessNm x) <> semi <+> "generalize dependent" <+> text x) xs
  pPrintPrec _ p (Clear hyp) =
    dotted p $ "clear" <+> text hyp
  pPrintPrec l p (AssertTacs x tp tacs) =
    sep $ dotted p ("assert" <+> pPrintArg (x, tp)) : [braces (pPrintPrec l nodotPrec (Concat tacs)) | not $ null tacs]

-- | comparison operator to alphabetically order branches of Induction/Destruct
ordFunc :: (Id, (CoqDestrPat, [Tactic])) -> (Id, (CoqDestrPat, [Tactic])) -> Ordering
ordFunc ("true", _) ("false", _) = LT
ordFunc ("false", _) ("true", _) = GT
ordFunc br br' = compare (fst br) (fst br')

admitted :: [Tactic] -> Bool
admitted = any containsAdmit
  where
    containsAdmit tac = case tac of
      Admit {} -> True
      Try t -> containsAdmit t
      Destruct _ cases -> admitted $ concatMap (snd . snd) cases
      Induction _ cases _ -> admitted $ concatMap (snd . snd) cases
      Assert _ _ t -> containsAdmit t
      Concat ts -> admitted ts
      Branches ts -> admitted ts
      _ -> False

instance Pretty ArgListT where
  pPrint = pPrint . mkArgListT
instance Pretty ArgList where
  pPrint = pPrint . mkArgList
instance Pretty UArgListT where
  pPrint = pPrint . mkUArgListT
instance Pretty UArgList where
  pPrint = pPrint . mkUArgList
