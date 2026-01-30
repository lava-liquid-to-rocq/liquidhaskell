{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--lava" @-}

module Benchmark.GradeExample where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (pred)

-- * Grade example

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

{-@ reflect letterComparison @-}
{-@ letterComparison :: l1 : Letter -> l2 : Letter -> Comparison @-}
letterComparison :: Letter -> Letter -> Comparison
letterComparison A A = Eq
letterComparison A _ = Gt
letterComparison B A = Lt
letterComparison B B = Eq
letterComparison B _ = Gt
letterComparison C A = Lt
letterComparison C B = Lt
letterComparison C C = Eq
letterComparison C _ = Gt
letterComparison D D = Eq
letterComparison D F = Gt
letterComparison D _ = Lt
letterComparison F F = Eq
letterComparison F _ = Lt

{-@ letterComparisonEq :: l:Letter -> {letterComparison l l = Eq} @-}
letterComparisonEq :: Letter -> Proof
letterComparisonEq A = trivial
letterComparisonEq B = trivial
letterComparisonEq C = trivial
letterComparisonEq D = trivial
letterComparisonEq F = trivial

{-@ reflect modifierComparison @-}
{-@ modifierComparison :: m1 : Modifier -> m2 : Modifier -> Comparison @-}
modifierComparison :: Modifier -> Modifier -> Comparison
modifierComparison Plus Plus = Eq
modifierComparison Plus _ = Gt
modifierComparison Natural Plus = Lt
modifierComparison Natural Natural = Eq
modifierComparison Natural _ = Gt
modifierComparison Minus Plus = Lt
modifierComparison Minus Natural = Lt
modifierComparison Minus Minus = Eq

-- | the issue with this example is the match on the result of letterComparison which isn't currently supported in reflected functions (separateBranches can't handle it)

{-
{-@ reflect grade_comparison @-}
{-@ grade_comparison :: g1: Grades -> g2: Grades -> Comparison @-}
grade_comparison :: Grades -> Grades -> Comparison
grade_comparison (Grade l1 m1) (Grade l2 m2) = case letterComparison l1 l2 of
  Gt -> Gt
  Eq -> modifierComparison m1 m2
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

{-@ reflect lowerLetter @-}
{-@ lowerLetter :: l: Letter -> Letter @-}
lowerLetter :: Letter -> Letter
lowerLetter A = B
lowerLetter B = C
lowerLetter C = D
lowerLetter D = F
lowerLetter F = F

{-@ lowerLetterFIsF:: {lowerLetter F = F} @-}
lowerLetterFIsF :: Proof
lowerLetterFIsF = trivial

{-@ lowerLetterLowers:: l: Letter -> p:{letterComparison F l = Lt} -> {letterComparison (lowerLetter l) l = Lt} @-}
lowerLetterLowers :: Letter -> Proof -> Proof
lowerLetterLowers l p = case l of
  F -> p
  _ -> trivial

{-@ reflect lowerGrade @-}
{-@ lowerGrade:: g:Grades -> Grades @-}
lowerGrade :: Grades -> Grades
lowerGrade (Grade l m) = case m of
  Minus -> case l of
    F -> Grade l m
    _ -> Grade (lowerLetter l) Plus
  Natural -> Grade l Minus
  Plus -> Grade l Natural

{-Example lowerGrade_A_Plus :
  lowerGrade (Grade A Plus) = (Grade A Natural).
Proof. reflexivity. Qed.

Example lowerGrade_A_Natural :
  lowerGrade (Grade A Natural) = (Grade A Minus).
Proof. reflexivity. Qed.

Example lowerGrade_A_Minus :
  lowerGrade (Grade A Minus) = (Grade B Plus).
Proof. reflexivity. Qed.

Example lowerGrade_B_Plus :
  lowerGrade (Grade B Plus) = (Grade B Natural).
Proof. reflexivity. Qed.

Example lowerGrade_F_Natural :
  lowerGrade (Grade F Natural) = (Grade F Minus).
Proof. reflexivity. Qed.
-}

{-@ lowerGradeTwice:: {lowerGrade (lowerGrade (Grade B Minus)) = Grade C Natural} @-}
lowerGradeTwice = trivial

{-@ lowerGradeThrice:: {lowerGrade (lowerGrade (lowerGrade (Grade B Minus))) = Grade C Minus} @-}
lowerGradeThrice = trivial

{-@ lowerGradeFMinus:: {lowerGrade (Grade F Minus) = (Grade F Minus)} @-}
lowerGradeFMinus :: Proof
lowerGradeFMinus = trivial

{-
{-@ lowerGrade_lowers:: g:Grade -> h:{grade_comparison (Grade F Minus) g = Lt} -> {grade_comparison (lowerGrade g) g = Lt} @-}
lowerGrade_lowers:: Grade -> Proof -> Proof
lowerGrade_lowers (Grade l Plus) _ = letterComparisonEq l
lowerGrade_lowers (Grade l Natural) _ = letterComparisonEq l
lowerGrade_lowers (Grade F Minus) h = h
lowerGrade_lowers (Grade l Minus) _ = trivial
-}

-- | Presumeable translated correctly, but LH gets confused about not being able to match types with SMT types

{-@ reflect applyLatePolicy @-}
{-@ applyLatePolicy::lateDays:Int -> g:Grades -> Grades @-}
applyLatePolicy :: Int -> Grades -> Grades
applyLatePolicy lateDays g
  | lateDays < 9 = g
  | lateDays < 17 = lowerGrade g
  | lateDays < 21 = lowerGrade (lowerGrade g)
  | otherwise = lowerGrade (lowerGrade (lowerGrade g))

{-@ noPenaltyForMostlyOnTime:: lateDays:Int -> g:Grades -> h:{lateDays < 9} -> {applyLatePolicy lateDays g = g} @-}
noPenaltyForMostlyOnTime :: Int -> Grades -> Proof -> Proof
noPenaltyForMostlyOnTime lateDays g h = if lateDays < 9 then trivial else h

{-
{-@ grade_lowered_once:: lateDays:Int -> g:Grades -> h:{not (lateDays < 9)} -> k:{lateDays < 17} -> l:{grade_comparison (Grade F Minus) g = Lt} -> {applyLatePolicy lateDays g = lowerGrade g} @-}
grade_lowered_once:: Int -> Grades -> Proof -> Proof -> Proof -> Proof
grade_lowered_once lateDays g h k l = if lateDays < 9 then h else (if lateDays < 17 then trivial else k)
-}
