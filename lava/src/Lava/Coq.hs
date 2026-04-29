{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

{- {-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-} -}

-- |
-- - (E)Coq grammar, printer to .ecoq file and suable functions
module Lava.Coq where

import Data.Bifunctor
import Data.Data
import Data.List (isSuffixOf, sortBy, stripPrefix, unsnoc)
import qualified Data.List.NonEmpty as NE
import Data.Maybe (isNothing)
import Lava.Names
import Text.PrettyPrint
import Text.PrettyPrint.HughesPJClass hiding (first)
import Prelude hiding ((<>))

{- ORMOLU_DISABLE -}
unitTmName :: Id
btrueTmName :: Id
bfalseTmName :: Id
unitTm :: CoqTerm
btrue :: CoqTerm
bfalse :: CoqTerm
boolTp :: RocqType
unitTp :: RocqType
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
  = -- | Add the hint to the specified hint database in Coq
    AddHint HintKind Id HintDatabase
  | -- > Transparent x. | Opaque x.
    ChangeVisibility Id Visibility
  | -- | a load declaration for some module to be loaded
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
  | -- | An inductively defined Prop, Type or Set (used only internally)
    CoqInductive Id [(Id, RocqType)] RocqType [CoqConstr]
  | -- | A type-level notation (like the refined inductive data types)
    CoqNewType Id RocqType
  | -- | An instance of one of the dictionary classes used for lookup in the proof automation tactics in Coq
    Instance Id [Id] [(Id, CoqTerm)]
  | TacInstance Id RocqType Tactic
  deriving (Eq, Data)

data DefBody
  = ProofBody [Tactic]
  | TermBody CoqTerm
  deriving (Data, Eq, Show)

-- | Data constructors
--
-- > c: A
data CoqConstr = Constr {cConstrNm :: Id, cConstrTp :: RocqType} deriving (Data, Eq)

data Visibility = Transparent | Opaque deriving (Data, Eq, Show)

data HintKind = UnfoldHint | ConstructorsHint | ResolveHint | RewriteHint deriving (Data, Eq)

data HintDatabase = CoreDB | GraphRelDB | GraphRelBackDB | WfDB | RefConstrDB | RelAxDB | EqHintDb deriving (Data, Eq)

-- ** Object-level grammar

-- | Built-in datatypes
--
-- > B ::= Z | string | float
data Builtin = CTInt | CTString | CTFloat
  deriving (Eq, Data, Show)

-- | Sorts
--
-- > κ ::= Type | Prop | Set
data BaseSort = TypeSort | PropSort | SetSort deriving (Eq, Data, Show)

-- | Types
--
-- > A ::= B | κ | {x:A | e} | tc A* | A -> A | ∀(x:A),A | e
--       | uPack A A* | Pack n (x:A)* A* e* | _
data RocqType
  = Builtin Builtin
  | Sort BaseSort
  | Subset Id RocqType CoqTerm
  | TC Id [RocqType]
  | -- | (simple-typed) arrow type
    Arrow RocqType RocqType
  | -- | Pi type
    FAType (Id, RocqType) RocqType
  | -- | Prop-sorted Rocq Types
    Prop CoqTerm
  | -- | unrefined Packs
    UPack UArgListT RocqType
  | Pack ArgListT UArgListT CoqTerm RocqType CoqTerm
  | ArgumentList ArgListT
  | Hole
  deriving (Eq, Data, Show)

newtype ArgListT = ArgListT [(Id, RocqType)] deriving (Eq, Data, Show)

newtype ArgList = ArgList [CoqTerm] deriving (Eq, Data, Show)

newtype UArgListT = UArgListT [RocqType] deriving (Eq, Data, Show)

newtype UArgList = UArgList [CoqTerm]

-- TODO: remove these functions and the BopArgList operators that are only used for pretty-printing

mkArgListT :: ArgListT -> CoqTerm
mkArgListT (ArgListT xs) =
  foldl (\tlTm (x, t) -> Bop (Binop ConsRT RefOp) (TypeArg t) $ Lambda x t tlTm) (Def "nilRT") (reverse xs)

mkUArgListT :: UArgListT -> CoqTerm
mkUArgListT (UArgListT xs) =
  foldl (\tlTm t -> Bop (Binop ConsUT RefOp) (TypeArg t) tlTm) (Def "nilUT") (reverse xs)

mkArgList :: ArgList -> CoqTerm
mkArgList (ArgList args) = foldl (flip (Bop (Binop ConsR RefOp))) (Def "nilR") args

mkUArgList :: UArgList -> CoqTerm
mkUArgList (UArgList uargs) = foldl (flip (Bop (Binop ConsU RefOp))) (Def "nilU") uargs

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
  | -- | True or False (in Prop)
    PropLit Bool
  | IsTrue CoqTerm
  | -- | represents a function name
    Def Id
  | -- | represents a notation
    Abbr Id
  | -- | represents a constructor name
    Cr Id
  | -- | represents a variable
    Var Id
  | Bop Binop CoqTerm CoqTerm
  | Neg OpKind CoqTerm
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
  | PrfTerm RocqType ProofTerm
  | InlineInstance [(Id, CoqTerm)]
  | TypeArg RocqType
  deriving (Data, Eq, Show)

data Binop = Binop BaseBop OpKind deriving (Data, Eq)

data OpKind = PropOp | RefOp | UnrefOp deriving (Data, Eq, Show)

data BaseBop
  = RocqEq
  | Eq
  | Neq
  | Leq
  | Geq
  | Lt
  | Gt
  | And
  | Or
  | Impl
  | Equiv
  | Plus
  | Minus
  | Times
  | Div
  | Mod
  | ConsRT
  | ConsUT
  | ConsR
  | ConsU
  deriving (Data, Eq)

-- | represents terms of Prop-kinded types in ECoq, in particular refinement witnesses
--
-- > p ::= s ∈ String | e | _ | ⌈e⌉ | conj e e
data ProofTerm
  = CoqProofTerm String
  | TermWitness CoqTerm
  | ProofHole (Maybe Id)
  | ByTac Tactic
  | RefWitness CoqTerm
  deriving (Data, Eq, Show)

-- | represents supported ECoq tactics, both custom tactics and basic Coq tactics (@tac@)
data Tactic
  = Easy
  | Oracle
  | -- In the branches, the Id is the name of the constructor in the branch (useful for reordering in the order needed by Coq)
    -- Like in LH, if destrGenVars is Just, we have an induction
    Destruct {destrExpr :: CoqTerm, destrBranches :: [(Id, (CoqDestrPat, [Tactic]))], destrGenVars :: Maybe [Id]}
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
  | Assert {assHypName :: Id, assClaim :: RocqType, assPrf :: Tactic}
  | AssertTacs Id RocqType [Tactic]
  | Intros [CoqIntroPat]
  | GeneralizeDependent [Id]
  | Clear Id
  | Concat [Tactic]
  | Branches [Tactic]
  | Custom String
  | Exfalso
  deriving (Data, Eq, Show)

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
  deriving (Data, Eq, Show)

data RewriteDir
  = -- | represents the -> rewrite pattern
    RwLR
  | -- | represents the <- rewrite pattern
    RwRL
  deriving (Data, Eq, Show)

data CoqIntroPat = DestrPat CoqDestrPat | RewritePat RewriteDir deriving (Data, Eq, Show)

-- * Constructors

-- | Build Concat [tacs] where [tacs] does not contain another concat
mkConcat :: [Tactic] -> Tactic
mkConcat = Concat . concatMap (\case Concat tacs' -> tacs'; tac -> [tac])

-- | Build Project and simplify the term, removing outer exists and subcasts or converting
-- between refined and unrefined operations
mkProject :: CoqTerm -> CoqTerm
mkProject (Exist _ t _) = t
mkProject (Bop (Binop bop RefOp) s t) = Bop (Binop bop UnrefOp) (mkProject s) (mkProject t)
mkProject (Cr c) | unrefinedConstrName "" `isSuffixOf` c = Cr c
mkProject (Cr c) = Cr $ unrefinedConstrName c
mkProject (App (Cr c) args) = App (Cr c') (map mkProject args)
  where
    c' = if unrefinedConstrName "" `isSuffixOf` c then c else unrefinedConstrName c
mkProject (SubCast _ _ t _) = mkProject t
mkProject tm = Project tm

-- | Syntactic simplification of SubCast to exist
simplifySubCast :: CoqTerm -> CoqTerm
-- TODO: transform into a mkSubCast
simplifySubCast (SubCast (Subset n b need) _ (Exist _ tm ProofHole {}) (ProofHole idO)) =
  Exist (Lambda n b need) tm (ProofHole idO)
simplifySubCast (SubCast (Subset n b need) _ (Exist _ tm CoqProofTerm {}) (ProofHole idO)) =
  Exist (Lambda n b need) tm (ProofHole idO)
simplifySubCast (SubCast Hole _ (Exist _ tm CoqProofTerm {}) (TermWitness TermHole)) =
  Exist TermHole tm (TermWitness TermHole)
simplifySubCast (SubCast Hole _ (Exist _ tm CoqProofTerm {}) (ProofHole idO)) =
  Exist TermHole tm (ProofHole idO)
simplifySubCast (SubCast Hole _ (Exist _ tm ProofHole {}) (TermWitness TermHole)) =
  Exist TermHole tm (TermWitness TermHole)
simplifySubCast (SubCast need have t _) | need == have && need /= Hole = t
simplifySubCast t = t

-- * Destructors

fromSubset :: RocqType -> (Id, RocqType, CoqTerm)
fromSubset (Subset x tpx rx) = (x, tpx, rx)
fromSubset _ = error "Subset expected"

-- * Functions on the grammar

-- | Regroup forall parameters
concatFAType :: RocqType -> ([(Id, RocqType)], RocqType)
concatFAType (FAType arg tp) = first (arg :) $ concatFAType tp
concatFAType tp = ([], tp)

-- | Regroup forall parameters
concatForalls :: CoqTerm -> ([(Id, RocqType)], CoqTerm)
concatForalls (Forall arg tp) = first (arg ++) $ concatForalls tp
concatForalls tp = ([], tp)

-- | Regroup λ parameters
concatLambdas :: CoqTerm -> ([(Id, RocqType)], CoqTerm)
concatLambdas (Lambda x tp r) = first ((x, tp) :) $ concatLambdas r
concatLambdas r = ([], r)

-- | Whether a proposition is trivially equivalent to True
isTrivial :: CoqTerm -> Bool
isTrivial (PropLit b) = b
isTrivial (IsTrue b) = b == btrue
isTrivial _ = False

{- ORMOLU_DISABLE -}
-- * Printer for grammar

-- | Wrap document in (*...*)
rocqComment :: Doc -> Doc
rocqComment doc = "(*" <+> doc <+> "*)"

dot :: Doc -- ^ A '.' character
dot = char '.'

-- ** Precedence levels, from `Print Grammar constr.`

appPrec :: Rational
appPrec = 10

-- For tactics, we use precedence levels to know what character to use at the
-- end of the tactic
nodotPrec :: Rational
concatPrec :: Rational
dotPrec :: Rational
nodotPrec = 0
concatPrec = 1
dotPrec = 2

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

pPrintArg :: (Pretty a) => ((Id, a), Bool) -> Doc
pPrintArg ((x, tp), isImplicit) =
  let delim = if isImplicit then brackets else parens
   in if pPrint tp == "_"
     then maybeBrackets isImplicit (text x)
     else delim (text x <+> colon <+> pPrint tp)

pPrintArgs :: (Pretty a) => [((Id, a), Bool)] -> Doc
pPrintArgs args =
  sep . map (pPrintArg . first (first collapseVars)) $ groupVars args
  where
    collapseVars :: [Id] -> Id
    collapseVars = render . hsep . map text
    -- Group ids with the same value
    groupVars :: (Pretty a) => [((Id, a), Bool)] -> [(([Id], a), Bool)]
    groupVars vars =
      map collapse $ NE.groupBy (\((_, tp1), b1) ((_, tp2), b2) -> pPrint tp1 == pPrint tp2 && b1 == b2) vars
      where
        collapse :: NE.NonEmpty ((Id, a), Bool) -> (([Id], a), Bool)
        collapse xs@(((_, tp), b) NE.:| _) = ((NE.toList $ NE.map (fst . fst) xs, tp), b)

instance Pretty CoqModule where
  pPrint (CoqModule name decls) =
     "module" <+> text name <+> vcat (punctuate "; " (map pPrint decls))

instance Pretty CoqConstr where
  pPrint (Constr c tp) = text c <> colon <+> pPrint tp

instance Pretty Decl where
  pPrint (Definition f args ret body vis) =
    case body of
      ProofBody tacs -> header <> dot
        $$ "Proof."
        $$ nest identNb (sep $ map pPrint tacs)
        $$ (if admitted tacs then "Admitted" else qedSym) <> dot
      TermBody expr -> header <> " :=" $$ nest identNb (pPrint expr <> dot)
    where
      kind = case ret of
        Prop {} | vis == Opaque -> "Theorem"
        _ ->  "Definition"
      header =
        hang (hang (kind <+> text f) identNb (pPrintArgs args <> colon))
        identNb (pPrint ret)
      qedSym = case vis of
        Transparent -> "Defined"
        Opaque -> "Qed"
  pPrint (Fix f args ret tm) =
     hang ("Fixpoint" <+> text f <+> pPrintArgs args <> colon) identNb (pPrint ret <+>  ":=")
    $$ nest identNb (pPrint tm <> dot)
  pPrint (Load m) =  "Load" <+> text m <> dot
  pPrint (CoqNewType t tp) =
     hang ("Global Notation" <+> text t <+> ":=") identNb (pPrintRocqType prettyNormal 200 tp False <> dot)
  pPrint (CoqInductive f args ret constrs) =
    hang ("Inductive" <+> text f <+> pPrintArgs (map (,False) args) <> colon) identNb (pPrint ret <+> ":=")
      $$ nest identNb (sep (map (("|" <+>) . pPrint) constrs) <> dot)
  pPrint (ChangeVisibility f vis) = text (show vis) <+> text f <> char '.'
  pPrint (AddHint kind ax db) =
    "#[global] Hint" <+> pPrint kind <+> text ax <> colon <+> pPrint db <> dot
  pPrint (Instance instName tp opDefs) =
    hang ("#[global] Instance" <+> text instName <> colon <+>
    hsep (map text tp) <+> ":=" <+> lbrace)
    identNb (nest identNb (vcat . punctuate semi $
      map (\(lookupOp, lookupRes) -> text lookupOp <+> ":=" <+> pPrint lookupRes) opDefs)
    <+> rbrace <> dot)
  pPrint (TacInstance instName tp tac) =
    sep [hang ("#[global] Instance" <+> text instName <> colon)
      identNb (pPrint tp <> dot), "Proof.", nest identNb (pPrint tac), "Defined."]

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
pPrintRocqType :: PrettyLevel -> Rational -> RocqType -> Bool -> Doc
pPrintRocqType _ _ (Builtin b) _ = pPrint b
pPrintRocqType _ _ (Sort sort) _ = pPrint sort
pPrintRocqType l p tp@(Subset x tc@(TC tc' []) e) True = case tc' of
  "bool" | isTrivial e -> "Bool"
  "Unit" -> braces (braces (pPrint e))
  _ -> case (e, tc_base) of
    _ | tc `elem` coqBuiltinInductDataTypes -> braces (text x <+> colon <+> pPrint tc <+> "|" <+> pPrint e)
    -- Use the refined name TC for {x: TC_u | wf_TC x /\ True}
    (Bop (Binop And PropOp) (App (Def wf) [Var x']) true, Just tc_ref)
      | x == x' && wf == wfTCName tc_ref && isTrivial true && not (null tc_ref)-> text tc_ref
    _ -> pPrintRocqType l p tp False
    where tc_base = reverse <$> stripPrefix (reverse $ unrefinedTCName "") (reverse tc')
pPrintRocqType _ _ (Subset x tp e) _ =
  braces (text x <> colon <+> pPrint tp <+> "|" <+> pPrint e)
pPrintRocqType _ _ tc@(TC tc' []) _ | tc `elem` coqBuiltinInductDataTypes = text tc'
pPrintRocqType l p (TC typeName tpArgs) b =
  maybeParens (p < appPrec) . hsep $
  text typeName : map (\tp -> pPrintRocqType l (appPrec - 1) tp b) tpArgs
pPrintRocqType l p (Arrow tp1 tp2) b =
  maybeParens (p < 99) $
    sep [pPrintRocqType l 200 tp1 b, "→" <+> pPrintRocqType l 200 tp2 b]
pPrintRocqType l p tp@(FAType {}) _ =
  let (args, ret) = concatFAType tp
   in pPrintForall l p args ret
pPrintRocqType l p (Prop tm) _ = pPrintPrec l p tm
pPrintRocqType l p (UPack uargTps t) _ =
  maybeParens (p < appPrec) $
    sep [text upackName, pPrintPrec l (appPrec - 1) uargTps, pPrintPrec l (appPrec - 1) t]
pPrintRocqType l p (ArgumentList argTps) _ =
  maybeParens (p < appPrec) $ "ArgList" <+> pPrintPrec l (appPrec - 1) argTps
pPrintRocqType l p (Pack argTps uargTps z t tm) _ =
  maybeParens (p < appPrec) $
    sep [text packName, pPrintPrec l (appPrec - 1) argTps, pPrintPrec l (appPrec - 1) uargTps, pPrintPrec l (appPrec - 1) z, pPrintPrec l (appPrec - 1) t, pPrintPrec l (appPrec - 1) tm]
pPrintRocqType _ _ Hole _ = char '_'

-- TODO: we probably want to use Maybe instead of using '_'
pPrintForall :: (Eq a, Pretty a, Pretty b) => PrettyLevel -> Rational -> [(Id, a)] -> b -> Doc
pPrintForall l p [] ret = pPrintPrec l p ret
pPrintForall l p (("_", t) : tl) ret =
  maybeParens (p < 99) $ sep [pPrint t, "→", pPrintForall l 200 tl ret]
pPrintForall _ p args ret = sep [
  if null args then empty
  else maybeParens (p < 10) "∀" <+> pPrintArgs (map (,False) args) <> comma, pPrint ret]

instance Pretty RocqType where
  pPrint tp = pPrintRocqType prettyNormal 200 tp True

instance Pretty BaseSort where
  pPrint PropSort = "Prop"
  pPrint TypeSort = "Type"
  pPrint SetSort = "Set"

-- We inline the precedence levels given by that `Print Grammar constr.`
instance Pretty CoqTerm where
  pPrintPrec l p (IsTrue tm) =
    maybeParens (p < appPrec) $ "is_true" <+> pPrintPrec l (appPrec - 1) tm
  pPrintPrec l p tm@(Forall {}) =
    let (vars, tm') = concatForalls tm
     in pPrintForall l p vars tm'
  pPrintPrec _ p (Exists vars tm) =
     maybeParens (p < 10) . sep $
       ["∃" <+> pPrintArgs (map (,False) vars) <> comma | not (null vars)] ++ [pPrint tm]
  pPrintPrec l p (Neg PropOp (IsTrue (Bop (Binop Eq RefOp) s t))) =
    pPrintPrec l p . IsTrue $ Bop (Binop Neq UnrefOp) s t
  pPrintPrec l p (Neg _ (Neg _ tm)) = pPrintPrec l p tm
  pPrintPrec l p (Neg opKind tm) =
    case opKind of
      PropOp -> maybeParens (p < 75) $ "¬" <+> pPrintPrec l 75 tm
      UnrefOp -> res "negb"
      RefOp -> res "negBool"
    where
      res sym = maybeParens (p < appPrec) $ sym <+> pPrintPrec l (appPrec - 1) tm
  pPrintPrec _ _ (PropLit b) = pPrint b
  pPrintPrec _ _ (Def s) = text s
  pPrintPrec _ _ (Abbr s) = text s
  pPrintPrec _ _ (Cr s) = text s
  pPrintPrec _ _ (Var x) = text x
  pPrintPrec l p (Bop bop s t) =
    case bopSymPrec bop of
    (sym, Just prec) ->
      maybeParens (p < prec) $
        sep [pPrintPrec l (prec - 1) s, text sym <+> pPrintPrec l prec' t]
      where
        -- FIX: defined as right associative in Rocq, but still needs brackets I don't know why
        prec' = case bop of Binop ConsUT _ -> 0; _ -> prec - 1
    (sym, Nothing) ->
      maybeParens (p < appPrec) $
        sep [text sym, pPrintPrec l (appPrec - 1) s, pPrintPrec l (appPrec - 1) t]
  pPrintPrec _ _ (StringLiteral s) = pPrint s
  pPrintPrec _ _ (IntLiteral n) = integer n
  pPrintPrec _ _ (FloatLiteral f) = double f
  pPrintPrec l p (App f ts) =
    maybeParens (p < appPrec)
      $ sep (pPrintPrec l appPrec f : map (pPrintPrec l (appPrec - 1)) ts)
  pPrintPrec _ p tm@(Lambda {}) =
    let (args, tm') = concatLambdas tm
     in maybeParens (p < 10) $ sep ["λ" <+> pPrintArgs (map (,False) args) <> comma, pPrint tm']
  pPrintPrec _ _ (Project t) = char '⌊' <+> pPrint t <+> char '⌋'
  pPrintPrec _ _ (Proj2sig t) = char '⌈' <+> pPrint t <+> char '⌉'
  pPrintPrec l p (SubCast to from t z) =
    maybeParens (p < appPrec) $ case (to, from) of
       (Hole, _) ->
         sep ["subsumptionCast", char '_', char '_', pPrintPrec l (appPrec - 1) t, pPrintPrec l (appPrec - 1) z]
       (Subset n b need, Subset _ a _) | a == b ->
         sep ["subsumptionCast", pPrintPrec l (appPrec - 1) a, pPrintPrec l (appPrec - 1) (Lambda n a need), pPrintPrec l (appPrec - 1) t, pPrintPrec l (appPrec - 1) z]
       _ -> sep ["subCast", pPrintPrec l (appPrec - 1) from, pPrintPrec l (appPrec - 1) to, pPrintPrec l (appPrec - 1) t, pPrintPrec l (appPrec - 1) z]
  pPrintPrec l p (Exist _ t (CoqProofTerm "I")) =
    maybeParens (p < appPrec) $ char '#' <+> pPrintPrec l (appPrec - 1) t
  pPrintPrec l p (Exist tp t z) =
    maybeParens (p < appPrec) $
      "exist" <+> pPrintPrec l (appPrec - 1) tp <+> pPrintPrec l (appPrec - 1) t <+> pPrintPrec l (appPrec - 1) z
  pPrintPrec _ p (Match ts _ cases) =
    maybeParens (p < appPrec) . sep $
      "match" <+> maybeParens (length ts > 1) (hsep $ punctuate comma (map pPrint ts)) <+> "with" :
      map (("|" <+>) . printCase) cases ++ ["end"]
    where
      printCase (pat, tm) =
        maybeParens (length pat > 1)
        (hsep . punctuate comma $ map (\(c, args) -> hsep $ map text (c : args)) pat)
        <+> "=>" <+> pPrint tm
  pPrintPrec _ p (Ite r s t) =
    maybeParens (p < 200) $ "if" <+> pPrint r <+> "then" <+> pPrint s <+> "else" <+> pPrint t
  pPrintPrec _ p (Let x tp s t) =
    maybeParens (p < 200) $ sep [
      "let" <+> maybe (text x) (\tp' -> text x <> colon <+> pPrint tp') tp <+> ":=",
      pPrint s <+> "in", pPrint t]
  pPrintPrec _ _ (InlineInstance fields) =
    sep ["{|", sep . punctuate semi $ map (\(field, val) -> text field <+> ":=" <+> pPrint val) fields, "|}"]
  pPrintPrec l p (TypeArg tp) = pPrintPrec l p tp
  pPrintPrec _ _ TermHole = char '_'
  pPrintPrec l p (PrfTerm _ z) = pPrintPrec l p z

  pPrint = pPrintPrec prettyNormal 200

instance Show Binop where
  show = fst . bopSymPrec

-- | For a given operator, returns its symbol or name
-- For a symbol, also returns its precedence
-- (for a name, we will use the precedence of application)
bopSymPrec :: Binop -> (String, Maybe Rational)
bopSymPrec (Binop RocqEq _) = ("=", Just 70)
bopSymPrec (Binop Eq kind) = case kind of
  PropOp -> ("==", Just 70)
  UnrefOp -> ("==?", Just 70)
  RefOp -> ("==?", Just 70)
bopSymPrec (Binop Neq kind) = case kind of
  PropOp -> ("≠", Just 70)
  UnrefOp -> ("/=?", Just 70)
  RefOp -> ("/=Z", Just 70)
bopSymPrec (Binop Leq kind) = case kind of
  PropOp -> ("<=", Just 70)
  UnrefOp -> ("<=?", Just 70)
  RefOp -> ("<=Z", Just 70)
bopSymPrec (Binop Geq kind) = case kind of
  PropOp -> (">=", Just 70)
  UnrefOp -> (">=?", Just 70)
  RefOp -> (">=Z", Just 70)
bopSymPrec (Binop Lt kind) = case kind of
  PropOp -> ("<", Just 70)
  UnrefOp -> ("<?", Just 70)
  RefOp -> ("<Z", Just 70)
bopSymPrec (Binop Gt kind) = case kind of
  PropOp -> (">", Just 70)
  UnrefOp -> (">?", Just 70)
  RefOp -> (">Z", Just 70)
bopSymPrec (Binop And kind) = case kind of
  PropOp -> ("∧", Just 80)
  UnrefOp -> ("&&", Just 40)
  RefOp -> undefined
bopSymPrec (Binop Or kind) = case kind of
  PropOp -> ("∨", Just 85)
  UnrefOp -> ("||", Just 50)
  RefOp -> undefined
bopSymPrec (Binop Impl kind) = case kind of
  PropOp -> ("→", Just 99)
  UnrefOp -> ("implb", Nothing)
  RefOp -> undefined
bopSymPrec (Binop Equiv kind) = case kind of
  PropOp -> ("↔", Just 95)
  UnrefOp -> undefined
  RefOp -> undefined
bopSymPrec (Binop Plus kind) = case kind of
  PropOp -> undefined
  UnrefOp -> ("+", Just 50)
  RefOp -> ("+Z", Just 50)
bopSymPrec (Binop Minus kind) = case kind of
  PropOp -> undefined
  UnrefOp -> ("-", Just 50)
  RefOp -> ("-Z", Just 50)
bopSymPrec (Binop Times kind) = case kind of
  PropOp -> undefined
  UnrefOp -> ("*", Just 40)
  RefOp -> ("*Z", Just 40)
bopSymPrec (Binop Div kind) = case kind of
  PropOp -> undefined
  UnrefOp -> ("/", Just 40)
  RefOp -> ("/Z", Just 40)
bopSymPrec (Binop Mod kind) = case kind of
  PropOp -> undefined
  UnrefOp -> ("mod", Just 40)
  RefOp -> ("modZ", Just 40)
bopSymPrec (Binop ConsRT _) = ("::RT", Just 60)
bopSymPrec (Binop ConsUT _) = ("::UT", Just 60)
bopSymPrec (Binop ConsR _) = ("::R", Just 60)
bopSymPrec (Binop ConsU _) = ("::U", Just 60)

instance Pretty ProofTerm where
  pPrintPrec _ _ (CoqProofTerm s) = text s
  pPrintPrec _ _ (TermWitness tm) | tm == unitTm = char '_'
  pPrintPrec l p (TermWitness t) = pPrintPrec l p t
  pPrintPrec _ _ (RefWitness tm) = char '⌈' <+> pPrint tm <+> char '⌉'
  pPrintPrec _ _ (ProofHole Nothing) = "ltac:" <> parens (pPrintPrec prettyNormal nodotPrec Oracle)
  pPrintPrec _ _ (ProofHole (Just h)) = "ltac:" <> parens (pPrintPrec prettyNormal nodotPrec (Concat [Try (Clear h), Oracle]))
  pPrintPrec _ _ (ByTac tac) = "ltac:" <> parens (pPrintPrec prettyNormal nodotPrec tac)

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
  pPrint (DestrPat pat) = pPrint pat
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
  pPrintPrec l p (Destruct tm branches genVars) = pPrintPrecMatch l p tm branches genVars
  pPrintPrec l p (Exact t) = case t of
    SubCast _ _ (Exist _ tm (CoqProofTerm prf)) (ProofHole _) | prf == "eq_refl" || prf == "I" ->
      refineOracle (Exist TermHole tm (TermWitness TermHole))
    SubCast _ have tm (ProofHole _) -> refineOracle (SubCast Hole have tm (TermWitness TermHole))
    SubCast _ have tm prf -> dotted p $ "exact" <+> pPrintPrec l (appPrec - 1) (SubCast Hole have tm prf)
    _ -> dotted p $ "refine" <+> pPrintPrec l (appPrec - 1) t
    where refineOracle x = sep ["refine" <+> pPrintPrec l (appPrec - 1) x <> semi, pPrintPrec l p Oracle]
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
  pPrintPrec l p (Refine t) = dotted p $ "refine" <+> pPrintPrec l (appPrec - 1) t
  pPrintPrec _ p (DestructSubsetTerm tm destrPat) =
    dotted p $ "destruct" <+> pPrint tm <+> "as" <+> pPrint destrPat
  pPrintPrec _ p (DestructConj h h1 h2) =
    dotted p $ "destruct" <+> text h <+> "as" <+> brackets (text h1 <+> text h2)
  pPrintPrec l p (Rewrite dir tm hyp) =
    dotted p $ "rewrite" <+> maybe empty pPrint dir <+> pPrintPrec l (appPrec - 1) tm
    <+> maybe empty ((<+>) "in" . text) hyp
  pPrintPrec l p (Pose abbr tm) =
    dotted p $ "pose" <+> pPrintPrec l (appPrec - 1) tm <+> "as" <+> text abbr
  pPrintPrec l p (ProofPose abbr tm) =
    dotted p $ "pose proof" <+> pPrintPrec l (appPrec - 1) tm <+> "as" <+> text abbr
  pPrintPrec l p (Assert n claim prf) =
    dotted p $ "assert" <+> parens (pPrintArg ((n, claim), False)) <+> "by" <+> pPrintPrec l (appPrec - 1) prf
  pPrintPrec _ p (Intros pats) =
    dotted p $ "intros" <+> sep (map pPrint pats)
  pPrintPrec _ p (GeneralizeDependent xs) =
    dotted p $ sep . punctuate semi $ map (\x -> "try revert" <+> text (subsetWitnessNm x) <> semi <+> "generalize dependent" <+> text x) xs
  pPrintPrec _ p (Clear hyp) =
    dotted p $ "clear" <+> text hyp
  pPrintPrec l p (AssertTacs x tp tacs) =
    sep $ dotted p ("assert" <+> pPrintArg ((x, tp), False))
      : [lbrace <+> pPrintPrec l dotPrec (mkConcat tacs) <+> rbrace | not $ null tacs]

-- | Pretty prints destruct or induct
pPrintPrecMatch :: PrettyLevel -> Rational -> CoqTerm -> [(Id, (CoqDestrPat, [Tactic]))] -> Maybe [Id] -> Doc
pPrintPrecMatch l p tm branches genVars =
  let matchTac =
        if isNothing genVars || all (\(_, (pat, tacs)) -> pat == ConjDestrPat [] && null tacs) branches
        then "destruct" else "induction"
      -- destruct or induct
      header0 = matchTac <+> pPrintPrec l (appPrec - 1) tm <+> "as" <+> pPrint (DisjDestrPat $ map fst branchesSorted)
      -- generalize dependent genVars
      gendeps vars =
        sep . punctuate semi $ map (\x -> "try revert" <+> text (subsetWitnessNm x) <> semi <+> "generalize dependent" <+> text x) vars
      -- destruct/induct, induct with generalized variables, or destruct with eqn:E
      -- In the last case, we update the precedence to print the branches with a concatenation
      -- We take max p concatPrec because if p = nodotPrec, we are in nested concat branches
      (header, p') = case (genVars, tm) of
        ((Just [], _); (Nothing, Var _)) -> (header0, max p concatPrec)
        (Just vars, _) -> (sep $ punctuate semi [gendeps vars, header0, "intros"], max p concatPrec)
        (Nothing, _) -> (sep ["let E := fresh \"E\" in", header0 <+> "eqn:E"], concatPrec)
   in if nullBranches then dotted p header
      else dotted p' header $$ printTacBranches p'
  where
    nullBranches = all (nullBranch . snd . snd) branches
    nullBranch = \case ([Concat []]; []) -> True; _ -> False
    branchesSorted = map snd $ sortBy ordFunc branches
    -- The branches of an induct/destruct in a Concat are shown with [branch1 | … | branchn],
    -- and otherwise as - branch1. - … - branchn (with the correct bullet)
    printTacBranches p' =
      if p' == concatPrec
      then dotted p (brackets . sep . punctuate " |" $ map (\(_, tacs) -> pPrintPrec l nodotPrec (mkConcat tacs)) branchesSorted)
      else vcat $ map (\(_, tacs) -> rocqBullet p' <+> sep (map (pPrintPrec l (p' + 1)) tacs)) branchesSorted

-- | comparison operator to alphabetically order branches of Destruct
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
      Destruct _ cases _ -> admitted $ concatMap (snd . snd) cases
      Assert _ _ t -> containsAdmit t
      Concat ts -> admitted ts
      Branches ts -> admitted ts
      _ -> False

instance Pretty ArgListT where
  {- pPrintPrec l p (ArgListT xs) =
    maybeParens (p > consPrec) $ sep
      (map (\(x, t) -> sep [pPrintPrec l (consPrec + 1) t <+> "::RT" <+>
      "λ" <+> pPrintArg ((x,t),True) <> comma]) xs)
      <+> "::RT nilRT" -}
  pPrintPrec l p = pPrintPrec l p . mkArgListT
instance Pretty ArgList where
  pPrintPrec l p = pPrintPrec l p . mkArgList
instance Pretty UArgListT where
  pPrintPrec l p = pPrintPrec l p . mkUArgListT
instance Pretty UArgList where
  pPrintPrec l p = pPrintPrec l p . mkUArgList
