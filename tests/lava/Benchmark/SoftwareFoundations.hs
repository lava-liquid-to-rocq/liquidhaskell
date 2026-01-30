{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--lava" @-}

module Benchmark.SoftwareFoundations where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (pred)

-- * Basics

{-@ data Day where
        Monday :: Day
        Tuesday :: Day
        Wednesday :: Day
        Thursday :: Day
        Friday :: Day
        Saturday :: Day
        Sunday :: Day @-}
data Day where
  Monday :: Day
  Tuesday :: Day
  Wednesday :: Day
  Thursday :: Day
  Friday :: Day
  Saturday :: Day
  Sunday :: Day
  deriving (Eq)

{-@ reflect next_weekday @-}
{-@ next_weekday :: d:Day -> Day @-}
next_weekday :: Day -> Day
next_weekday Monday = Tuesday
next_weekday Tuesday = Wednesday
next_weekday Wednesday = Thursday
next_weekday Thursday = Friday
next_weekday Friday = Monday
next_weekday Saturday = Monday
next_weekday Sunday = Monday

{-@ test_next_weekday :: {next_weekday (next_weekday Saturday) == Tuesday} @-}
test_next_weekday :: Proof
test_next_weekday = trivial

{-@ data SFBool where
        SFTrue :: SFBool
        SFFalse :: SFBool @-}
data SFBool where
  SFTrue :: SFBool
  SFFalse :: SFBool
  deriving (Eq)

{-@ reflect negb @-}
{-@ negb :: SFBool -> SFBool @-}
negb :: SFBool -> SFBool
negb SFTrue = SFFalse
negb SFFalse = SFTrue

-- 42 LoC

{-@ reflect andb @-}
{-@ andb :: b1:SFBool -> b2:SFBool -> SFBool @-}
andb :: SFBool -> SFBool -> SFBool
andb b1 b2 = case b1 of
  SFTrue -> b2
  SFFalse -> SFFalse

{-@ reflect orb @-}
{-@ orb :: b1:SFBool -> b2:SFBool -> SFBool @-}
orb :: SFBool -> SFBool -> SFBool
orb b1 b2 = case b1 of
  SFTrue -> SFTrue
  SFFalse -> b2

{-@ test_orb1 :: {orb SFTrue SFFalse == SFTrue} @-}
test_orb1 = trivial

{-@ test_orb2 :: {orb SFFalse SFFalse == SFFalse} @-}
test_orb2 = trivial

{-@ test_orb3 :: {orb SFFalse SFTrue == SFTrue} @-}
test_orb3 = trivial

{-@ test_orb4 :: {orb SFTrue SFTrue == SFTrue} @-}
test_orb4 = trivial

-- 62 LoC

{- This doesn't quite work:
{-@ (&&):: SFBool -> SFBool -> SFBool @-}
(&&) :: SFBool -> SFBool -> SFBool
x && y = andb x y
{-@ (||):: SFBool -> SFBool -> SFBool @-}
(||) :: SFBool -> SFBool -> SFBool
x || y = orb x y
-}

{-@ test_orb5 :: {orb SFFalse (orb SFFalse SFTrue) = SFTrue} @-}
test_orb5 = trivial

{-@ negb' :: b:SFBool -> SFBool @-}
negb' :: SFBool -> SFBool
negb' b = if b == SFTrue then SFFalse else SFTrue

{-@ andb' :: b1:SFBool -> b2:SFBool -> SFBool @-}
andb' :: SFBool -> SFBool -> SFBool
andb' b1 b2 = if b1 == SFTrue then b2 else SFFalse

{-@ orb' :: b1:SFBool -> b2 : SFBool -> SFBool @-}
orb' :: SFBool -> SFBool -> SFBool
orb' b1 b2 = if b1 == SFTrue then SFTrue else b2

{-@ reflect nandb @-}
{-@ nandb :: b1:SFBool -> b2:SFBool -> SFBool @-}
nandb SFTrue SFTrue = SFFalse
nandb b1 b2 = SFTrue

{-@ test_nandb1 :: {nandb SFTrue SFFalse == SFTrue } @-}
test_nandb1 = trivial

{-@ test_nandb2 :: {nandb SFFalse SFFalse == SFTrue } @-}
test_nandb2 = trivial

{-@ test_nandb3 :: {nandb SFFalse SFTrue == SFTrue } @-}
test_nandb3 = trivial

{-@ test_nandb4 :: {nandb SFTrue SFTrue == SFFalse } @-}
test_nandb4 = trivial

{-@ reflect andb3 @-}
{-@ andb3 :: b1: SFBool -> b2: SFBool -> b3: SFBool -> SFBool @-}
andb3 :: SFBool -> SFBool -> SFBool -> SFBool
andb3 SFTrue SFTrue SFTrue = SFTrue
andb3 _ _ _ = SFFalse

{-@ test_andb31 :: {andb3 SFTrue SFTrue SFTrue == SFTrue } @-}
test_andb31 = trivial

-- 92 LoC

{-@ test_andb32 :: {andb3 SFFalse SFTrue SFTrue == SFFalse } @-}
test_andb32 = trivial

{-@ test_andb33 :: {andb3 SFTrue SFFalse SFTrue == SFFalse } @-}
test_andb33 = trivial

{-@ test_andb34 :: {andb3 SFTrue SFTrue SFFalse == SFFalse } @-}
test_andb34 = trivial

{-@ data RGB where
        Red :: RGB
        Green :: RGB
        Blue :: RGB @-}
data RGB where
  Red :: RGB
  Green :: RGB
  Blue :: RGB
  deriving (Eq)

{-@ data Color where
        Black :: Color
        White :: Color
        Primary :: (p: RGB) -> Color @-}
data Color where
  Black :: Color
  White :: Color
  Primary :: RGB -> Color
  deriving (Eq)

{-@ reflect monochrome @-}
{-@ monochrome :: c:Color -> SFBool @-}
monochrome :: Color -> SFBool
monochrome Black = SFTrue
monochrome White = SFTrue
monochrome (Primary p) = SFFalse

{-@ isred :: c:Color -> SFBool @-}
isred :: Color -> SFBool
isred Black = SFFalse
isred White = SFFalse
isred (Primary Red) = SFTrue
isred (Primary _) = SFFalse

{-@ data SFBit where
        B1 :: SFBit
        B0 :: SFBit @-}
data SFBit where
  B1 :: SFBit
  B0 :: SFBit
  deriving (Eq)

-- 135 LoC

{-@ data Nibble where
        Bits :: (b0:SFBit) -> (b1:SFBit) -> (b2:SFBit) -> (b3:SFBit) -> Nibble @-}
data Nibble where
  Bits :: SFBit -> SFBit -> SFBit -> SFBit -> Nibble
  deriving (Eq)

{-@ allzero :: (nb:Nibble) -> SFBool @-}
allzero :: Nibble -> SFBool
allzero (Bits B0 B0 B0 B0) = SFTrue
allzero (Bits _ _ _ _) = SFFalse

{-@ data MyNat where
        O :: MyNat
        S :: (n:MyNat) -> MyNat @-}
data MyNat where
  O :: MyNat
  S :: MyNat -> MyNat
  deriving (Eq)

{-@ data OtherNat where
        Stop :: OtherNat
        Tick :: (foo:OtherNat) -> OtherNat @-}
data OtherNat where
  Stop :: OtherNat
  Tick :: OtherNat -> OtherNat
  deriving (Eq)

-- 158 LoC

{-@ reflect pred @-}
{-@ pred :: (n:MyNat) -> MyNat @-}
pred :: MyNat -> MyNat
pred O = O
pred (S n') = n'

{-@ minustwo :: (n:MyNat) -> MyNat @-}
minustwo O = O
minustwo (S O) = O
minustwo (S (S n')) = n'

{- {-@ reflect sf_even @-}
{-@ sf_even :: n:MyNat -> SFBool @-}
sf_even :: MyNat -> SFBool
sf_even O = SFTrue
sf_even (S O) = SFFalse
sf_even (S (S n')) = sf_even n'

{-@ sf_odd :: n:MyNat -> SFBool @-}
sf_odd n = negb (sf_even n)

{-@ test_odd1:: {sf_odd (S O) = SFTrue} @-}
test_odd1 = trivial

{-@ test_odd2:: {sf_odd (S ( S (S (S O)))) = SFTrue} @-}
test_odd2 = trivial

-}

{-@ reflect plus @-}
{-@ plus :: n:MyNat -> m:MyNat -> MyNat @-}
plus :: MyNat -> MyNat -> MyNat
plus O m = m
plus (S n') m = S (plus n' m)

{-@ reflect mult @-}
{-@ mult :: n:MyNat -> m:MyNat -> MyNat @-}
mult :: MyNat -> MyNat -> MyNat
mult O _ = O
mult (S n') m = plus m (mult n' m)

{-@ reflect one @-}
{-@ one :: MyNat @-}
one :: MyNat
one = S O

{-@ reflect two @-}
{-@ two :: MyNat @-}
two :: MyNat
two = S one

{-@ reflect three @-}
{-@ three :: MyNat @-}
three :: MyNat
three = S two

{-@ reflect four @-}
{-@ four :: MyNat @-}
four :: MyNat
four = S three

{-@ reflect five @-}
{-@ five :: MyNat @-}
five :: MyNat
five = S four

{-@ reflect six @-}
{-@ six :: MyNat @-}
six :: MyNat
six = S five

{-@ reflect seven @-}
{-@ seven :: MyNat @-}
seven = S six

{-@ reflect eight @-}
{-@ eight :: MyNat @-}
eight :: MyNat
eight = S seven

{-@ reflect nine @-}
{-@ nine :: MyNat @-}
nine = S eight

{-@ reflect ten @-}
{-@ ten :: MyNat @-}
ten = S nine

{-@ reflect eleven @-}
{-@ eleven :: MyNat @-}
eleven = S ten

{-@ reflect twelve @-}
{-@ twelve :: MyNat @-}
twelve = S eleven

-- 220 SLoc

{-@ test_mult1 :: {mult three three = nine} @-}
test_mult1 :: Proof
test_mult1 = trivial

{-@ reflect minus @-}
{-@ minus :: n:MyNat -> m:MyNat -> MyNat @-}
minus :: MyNat -> MyNat -> MyNat
minus O _ = O
minus n@(S _) O = n
minus (S n') (S m') = minus n' m'

{-@ reflect sf_exp @-}
{-@ sf_exp :: base:MyNat -> power:MyNat -> MyNat @-}
sf_exp :: MyNat -> MyNat -> MyNat
sf_exp _ O = S O
sf_exp base (S p) = mult base (sf_exp base p)

{-@ reflect factorial @-}
{-@ factorial :: (n:MyNat) -> MyNat @-}
factorial :: MyNat -> MyNat
factorial O = S O
factorial (S n') = mult (S n') (factorial n')

{-@ test_factorial1:: {factorial three == six} @-}
test_factorial1 = trivial

-- 241 SLoc

{-
-- This certainly works but requires hundreds of inversions (corresponding to computation steps) in Coq to prove, so it's very slow and it therefore commented out for now
{-@ test_factorial2:: {factorial five == mult ten twelve} @-}
test_factorial2 = trivial
-}

{-@ reflect eqb @-}
{-@ eqb :: n:MyNat -> m:MyNat -> SFBool @-}
eqb :: MyNat -> MyNat -> SFBool
eqb O O = SFTrue
eqb O (S m') = SFFalse
eqb (S n') O = SFFalse
eqb (S n') (S m') = eqb n' m'

{-@ reflect leb @-}
{-@ leb :: n:MyNat -> m:MyNat -> SFBool @-}
leb :: MyNat -> MyNat -> SFBool
leb O _ = SFTrue
leb (S n') O = SFFalse
leb (S n') (S m') = leb n' m'

{-@ test_leb1 :: {leb two two = SFTrue} @-}
test_leb1 = trivial

{-@ test_leb2 :: {leb two four = SFTrue} @-}
test_leb2 = trivial

{-@ test_leb3 :: {leb four two = SFFalse} @-}
test_leb3 = trivial

-- 260 SLoc

{-@ reflect ltb @-}
{-@ ltb :: n:MyNat -> m:MyNat -> SFBool @-}
ltb :: MyNat -> MyNat -> SFBool
ltb O O = SFFalse
ltb O (S m') = SFTrue
ltb (S n') O = SFFalse
ltb (S n') (S m') = ltb n' m'

{-@ test_ltb1 :: {ltb two two = SFFalse} @-}
test_ltb1 = trivial

{-@ test_ltb2 :: {ltb two four = SFTrue} @-}
test_ltb2 = trivial

{-@ test_ltb3 :: {ltb four two = SFFalse} @-}
test_ltb3 = trivial

{-@ plus_O_n :: n: MyNat -> {plus O n = n} @-}
plus_O_n :: MyNat -> Proof
plus_O_n n = trivial

-- 276 SLoc

{-@ plus_1_1 :: n:MyNat -> {plus one n = S n} @-}
plus_1_1 :: MyNat -> Proof
plus_1_1 n = trivial

{-@ mult_0_1 :: n:MyNat -> {mult O n = O} @-}
mult_0_1 :: MyNat -> Proof
mult_0_1 n = trivial

{-@ plus_id_example :: n:MyNat -> m:MyNat -> z:{n = m} -> {plus n n = plus m m} @-}
plus_id_example :: MyNat -> MyNat -> Proof -> Proof
plus_id_example n m z = trivial

{-@ plus_id_exercise :: n:MyNat -> m:MyNat -> o:MyNat -> p:{n = m} -> q:{m = o} -> {plus n m = plus m o} @-}
plus_id_exercise :: MyNat -> MyNat -> MyNat -> Proof -> Proof -> Proof
plus_id_exercise n m o p q = trivial

{-@ mult_n_O:: n:MyNat -> {O = mult n O} @-}
mult_n_O :: MyNat -> Proof
mult_n_O O = trivial
mult_n_O (S n') = mult_n_O n'

{-@ mult_n_0_m_0 :: p:MyNat -> q:MyNat -> {plus (mult p O) (mult q O) = O} @-}
mult_n_0_m_0 :: MyNat -> MyNat -> Proof
mult_n_0_m_0 p q = mult_n_O p ? mult_n_O q

{-@ add_succ_r:: n:MyNat -> m:MyNat -> {plus n (S m) = S (plus n m)} @-}
add_succ_r :: MyNat -> MyNat -> Proof
add_succ_r O _ = trivial
add_succ_r (S n') m = add_succ_r n' m

-- 299 SLoc

{-@ add_assoc:: n:MyNat -> m:MyNat -> p:MyNat -> {plus n (plus m p) = plus (plus n m) p} @-}
add_assoc :: MyNat -> MyNat -> MyNat -> Proof
add_assoc O _ _ = trivial
add_assoc (S n') m p = add_assoc n' m p

{-@ mult_n_Sm:: n:MyNat -> m:MyNat -> {plus (mult n m) n = mult n (S m)} @-}
mult_n_Sm :: MyNat -> MyNat -> Proof
mult_n_Sm O _ = trivial
mult_n_Sm (S n') m = mult_n_Sm n' m ? add_succ_r (plus m (mult n' m)) n' ? add_assoc m (mult n' m) n'

-- 307 LoC

{-@ mult_n_1 :: p:MyNat -> {mult p one = p} @-}
mult_n_1 p = mult_n_Sm p O ? mult_n_O p

{-@ plus_1_neq_0:: n:MyNat -> {(plus n one) /= O} @-}
plus_1_neq_0 O = trivial
plus_1_neq_0 (S _) = trivial

{-@ negb_involutive :: b:SFBool -> {negb (negb b) = b} @-}
negb_involutive SFTrue = trivial
negb_involutive SFFalse = trivial

{-@ andb_commutative:: b:SFBool -> c:SFBool -> {andb b c = andb c b} @-}
andb_commutative SFTrue SFTrue = trivial
andb_commutative SFTrue SFFalse = trivial
andb_commutative SFFalse SFTrue = trivial
andb_commutative SFFalse SFFalse = trivial

-- 320 SLoc

{-@ andb_true_elim2 :: b:SFBool -> c:SFBool -> p:{andb b c = SFTrue} -> {c = SFTrue} @-}
andb_true_elim2 :: SFBool -> SFBool -> Proof -> Proof
andb_true_elim2 SFTrue SFTrue _ = trivial
andb_true_elim2 SFTrue SFFalse _ = trivial
andb_true_elim2 SFFalse SFTrue _ = trivial
andb_true_elim2 SFFalse SFFalse _ = trivial

{-@ zero_nbeq_plus_1 :: n:MyNat -> {(eqb O (plus n one)) = SFFalse} @-}
zero_nbeq_plus_1 O = trivial
zero_nbeq_plus_1 (S n') = trivial

{-@ identity_fn_applied_twice :: f: (SFBool -> SFBool) -> h:(x:SFBool -> {f x = x}) -> b:SFBool -> {f (f b) = b} @-}
identity_fn_applied_twice :: (SFBool -> SFBool) -> (SFBool -> Proof) -> SFBool -> Proof
identity_fn_applied_twice f h b =
  trivial
    ? ( f (f b)
          ? h (f b)
          === f b
          ? h b
          === b
          *** QED
      )

-- 340 SLoc

{-@ andb_eq_orb :: b: SFBool -> c: SFBool -> h:{andb b c = orb b c} -> {b = c} @-}
andb_eq_orb :: SFBool -> SFBool -> Proof -> Proof
andb_eq_orb SFTrue SFTrue _ = trivial
andb_eq_orb SFTrue SFFalse _ = trivial
andb_eq_orb SFFalse SFTrue _ = trivial
andb_eq_orb SFFalse SFFalse _ = trivial

{-@ data Letter where
        A :: Letter
        B :: Letter
        C :: Letter
        D :: Letter
        F :: Letter @-}
data Letter where
  A :: Letter
  B :: Letter
  C :: Letter
  D :: Letter
  F :: Letter
  deriving (Eq)

-- 359 SLoc

{-@ data Modifier where
        Plus :: Modifier
        Natural :: Modifier
        Minus :: Modifier @-}
data Modifier where
  Plus :: Modifier
  Natural :: Modifier
  Minus :: Modifier
  deriving (Eq)

{-@ data Grades where
        Grade :: (l:Letter) -> (m:Modifier) -> Grades @-}
data Grades where
  Grade :: Letter -> Modifier -> Grades

{-@ data Comparison where
        Eq :: Comparison
        Lt :: Comparison
        Gt :: Comparison @-}
data Comparison where
  -- | Equal
  Eq :: Comparison
  -- | Less than
  Lt :: Comparison
  -- | Greater than
  Gt :: Comparison
  deriving (Eq)

-- 281 SLoc

{-@ reflect letter_comparison @-}
{-@ letter_comparison :: l1 : Letter -> l2 : Letter -> Comparison @-}
letter_comparison :: Letter -> Letter -> Comparison
letter_comparison A A = Eq
letter_comparison A _ = Gt
letter_comparison B A = Lt
letter_comparison B B = Eq
letter_comparison B _ = Gt
letter_comparison C A = Lt
letter_comparison C B = Lt
letter_comparison C C = Eq
letter_comparison C _ = Gt
letter_comparison D D = Eq
letter_comparison D F = Gt
letter_comparison D _ = Lt
letter_comparison F F = Eq
letter_comparison F _ = Lt

{-@ letter_comparison_eq :: l:Letter -> {letter_comparison l l = Eq} @-}
letter_comparison_eq :: Letter -> Proof
letter_comparison_eq A = trivial
letter_comparison_eq B = trivial
letter_comparison_eq C = trivial
letter_comparison_eq D = trivial
letter_comparison_eq F = trivial

-- 305 SLoc

{-@ reflect modifier_comparison @-}
{-@ modifier_comparison :: m1 : Modifier -> m2 : Modifier -> Comparison @-}
modifier_comparison :: Modifier -> Modifier -> Comparison
modifier_comparison Plus Plus = Eq
modifier_comparison Plus _ = Gt
modifier_comparison Natural Plus = Lt
modifier_comparison Natural Natural = Eq
modifier_comparison Natural _ = Gt
modifier_comparison Minus Plus = Lt
modifier_comparison Minus Natural = Lt
modifier_comparison Minus Minus = Eq

-- 316 SLoc

-- | the issue with this example is the match on the result of letter_comparison which isn't currently supported in reflected functions (separateBranches can't handle it)

{-
{-@ reflect grade_comparison @-}
{-@ grade_comparison :: g1: Grades -> g2: Grades -> Comparison @-}
grade_comparison :: Grades -> Grades -> Comparison
grade_comparison (Grade l1 m1) (Grade l2 m2) = case letter_comparison l1 l2 of
  Gt -> Gt
  Eq -> modifier_comparison m1 m2
  Lt -> Lt

{-@ test_grade_comparison1:: {grade_comparison (Grade A Minus) (Grade B Plus) = Gt} @-}
test_grade_comparison1 = trivial

{-@ test_grade_comparison2:: {grade_comparison (Grade A Minus) (Grade A Plus) = Lt} @-}
test_grade_comparison2 = trivial

{-@ test_grade_comparison3:: {grade_comparison (Grade F Plus) (Grade F Plus) = Eq} @-}
test_grade_comparison3 = trivial

{-@ test_grade_comparison4:: {grade_comparison (Grade B Minus) (Grade C Plus) = Gt} @-}
test_grade_comparison4 = trivial
-}

{-@ reflect lower_letter @-}
{-@ lower_letter :: l: Letter -> Letter @-}
lower_letter :: Letter -> Letter
lower_letter A = B
lower_letter B = C
lower_letter C = D
lower_letter D = F
lower_letter F = F

{-@ lower_letter_F_is_F:: {lower_letter F = F} @-}
lower_letter_F_is_F :: Proof
lower_letter_F_is_F = trivial

{-@ lower_letter_lowers:: l: Letter -> p:{letter_comparison F l = Lt} -> {letter_comparison (lower_letter l) l = Lt} @-}
lower_letter_lowers :: Letter -> Proof -> Proof
lower_letter_lowers l p = case l of
  F -> p
  _ -> trivial

{-@ reflect lower_grade @-}
{-@ lower_grade:: g:Grades -> Grades @-}
lower_grade :: Grades -> Grades
lower_grade (Grade l m) = case m of
  Minus -> case l of
    F -> Grade l m
    _ -> Grade (lower_letter l) Plus
  Natural -> Grade l Minus
  Plus -> Grade l Natural

-- 341 SLoc

{-Example lower_grade_A_Plus :
  lower_grade (Grade A Plus) = (Grade A Natural).
Proof. reflexivity. Qed.

Example lower_grade_A_Natural :
  lower_grade (Grade A Natural) = (Grade A Minus).
Proof. reflexivity. Qed.

Example lower_grade_A_Minus :
  lower_grade (Grade A Minus) = (Grade B Plus).
Proof. reflexivity. Qed.

Example lower_grade_B_Plus :
  lower_grade (Grade B Plus) = (Grade B Natural).
Proof. reflexivity. Qed.

Example lower_grade_F_Natural :
  lower_grade (Grade F Natural) = (Grade F Minus).
Proof. reflexivity. Qed.
-}

{-@ lower_grade_twice:: {lower_grade (lower_grade (Grade B Minus)) = Grade C Natural} @-}
lower_grade_twice = trivial

{-@ lower_grade_thrice:: {lower_grade (lower_grade (lower_grade (Grade B Minus))) = Grade C Minus} @-}
lower_grade_thrice = trivial

{-@ lower_grade_F_Minus:: {lower_grade (Grade F Minus) = (Grade F Minus)} @-}
lower_grade_F_Minus :: Proof
lower_grade_F_Minus = trivial

{-
{-@ lower_grade_lowers:: g:Grade -> h:{grade_comparison (Grade F Minus) g = Lt} -> {grade_comparison (lower_grade g) g = Lt} @-}
lower_grade_lowers:: Grade -> Proof -> Proof
lower_grade_lowers (Grade l Plus) _ = letter_comparison_eq l
lower_grade_lowers (Grade l Natural) _ = letter_comparison_eq l
lower_grade_lowers (Grade F Minus) h = h
lower_grade_lowers (Grade l Minus) _ = trivial
-}

-- | Presumeable translated correctly, but LH gets confused about not being able to match types with SMT types

-- 348 SLoc

{-@ reflect apply_late_policy @-}
{-@ apply_late_policy::late_days:Int -> g:Grades -> Grades @-}
apply_late_policy :: Int -> Grades -> Grades
apply_late_policy late_days g =
  if late_days < 9
    then g
    else
      if late_days < 17
        then lower_grade g
        else
          if late_days < 21
            then lower_grade (lower_grade g)
            else
              lower_grade (lower_grade (lower_grade g))

{-@ no_penalty_for_mostly_on_time:: late_days:Int -> g:Grades -> h:{late_days < 9} -> {apply_late_policy late_days g = g} @-}
no_penalty_for_mostly_on_time :: Int -> Grades -> Proof -> Proof
no_penalty_for_mostly_on_time late_days g h = if late_days < 9 then trivial else h

-- 365 SLoc

{-
{-@ grade_lowered_once:: late_days:Int -> g:Grades -> h:{not (late_days < 9)} -> k:{late_days < 17} -> l:{grade_comparison (Grade F Minus) g = Lt} -> {apply_late_policy late_days g = lower_grade g} @-}
grade_lowered_once:: Int -> Grades -> Proof -> Proof -> Proof -> Proof
grade_lowered_once late_days g h k l = if late_days < 9 then h else (if late_days < 17 then trivial else k)
-}

{-@ data SFBin where
        Z :: SFBin
        Bin0 :: n:SFBin -> SFBin
        Bin1 :: n:SFBin -> SFBin @-}
data SFBin where
  Z :: SFBin
  Bin0 :: SFBin -> SFBin
  Bin1 :: SFBin -> SFBin
  deriving (Eq)

{-@ reflect incr @-}
{-@ incr:: m:SFBin -> SFBin @-}
incr :: SFBin -> SFBin
incr Z = Bin1 Z
incr (Bin0 m') = Bin1 m'
incr (Bin1 m') = Bin0 (incr m')

-- 380 SLoc

{-@ reflect bin_to_nat @-}
{-@ bin_to_nat:: m:SFBin -> Int @-}
bin_to_nat :: SFBin -> Int
bin_to_nat Z = 0
bin_to_nat (Bin0 m') = 2 * (bin_to_nat m')
bin_to_nat (Bin1 m') = 1 + 2 * (bin_to_nat m')

{-@ test_bin_incr1:: {incr (Bin1 Z) = Bin0 (Bin1 Z)} @-}
test_bin_incr1 = trivial

{-@ test_bin_incr2:: {incr (Bin0 (Bin1 Z)) = Bin1 (Bin1 Z)} @-}
test_bin_incr2 = trivial

{-@ test_bin_incr3:: {incr (Bin1 (Bin1 Z)) = Bin0 (Bin0 (Bin1 Z))} @-}
test_bin_incr3 = trivial

{-@ test_bin_incr4:: {bin_to_nat (Bin0 (Bin1 Z)) = 2} @-}
test_bin_incr4 = trivial

{-@ test_bin_incr5:: {bin_to_nat (incr (Bin1 Z)) = 1 + bin_to_nat (Bin1 Z)} @-}
test_bin_incr5 = trivial

{-@ test_bin_incr6:: {bin_to_nat (incr (incr (Bin1 Z))) = 2 + bin_to_nat (Bin1 Z)} @-}
test_bin_incr6 = trivial

-- 398 SLoc

-- * Induction

{-@ add_0_r:: n:MyNat -> {plus n O = n} @-}
add_0_r O = trivial
add_0_r (S n') = add_0_r n'

{-@ minus_n_n:: n:MyNat -> {minus n n = O} @-}
minus_n_n O = trivial
minus_n_n (S n') = minus_n_n n'

{-@ mul_0_r:: n:MyNat -> {mult n O = O} @-}
mul_0_r O = trivial
mul_0_r (S n') = mul_0_r n'

{-@ plus_n_Sm:: n:MyNat -> m:MyNat -> {S (plus n m) = plus n (S m)} @-}
plus_n_Sm :: MyNat -> MyNat -> Proof
plus_n_Sm O m = trivial
plus_n_Sm (S n') m = plus_n_Sm n' m

{-@ add_comm:: n:MyNat -> m:MyNat -> {plus n m = plus m n} @-}
add_comm O m = add_0_r m
add_comm (S n') m = plus_n_Sm m n' ? add_comm n' m

-- + 16 SLoc
-- 414 SLoc

-- * Lists

{-@ data Natprod where
        Pair :: n1:MyNat -> n2:MyNat -> Natprod @-}
data Natprod where
  Pair :: MyNat -> MyNat -> Natprod
  deriving (Eq)

{-@ reflect fstSF @-}
{-@ fstSF:: p:Natprod -> MyNat @-}
fstSF :: Natprod -> MyNat
fstSF (Pair n1 n2) = n1

{-@ reflect sndSF @-}
{-@ sndSF:: p:Natprod -> MyNat @-}
sndSF :: Natprod -> MyNat
sndSF (Pair n1 n2) = n2

{-@ reflect swap_pair @-}
{-@ swap_pair:: p:Natprod ->Natprod @-}
swap_pair :: Natprod -> Natprod
swap_pair (Pair x y) = Pair y x

-- 431 LoC

{-@ surjective_pairing':: n:MyNat -> m:MyNat -> {Pair n m = Pair (fstSF (Pair n m)) (sndSF (Pair n m))} @-}
surjective_pairing' :: MyNat -> MyNat -> Proof
surjective_pairing' n m = trivial

{-@ surjective_pairing:: p:Natprod -> {p = Pair (fstSF p) (sndSF p)} @-}
surjective_pairing :: Natprod -> Proof
surjective_pairing (Pair n m) = trivial

-- 437 SLoc
