Load PairLists.
Load Equality.
Require Export Notations.
Require Export Logic.
Require Export Specif.

Require Export Program.Subset.
Require Export Init.Tactics.

Require Export Arith.
Require Export Program.
Require Export omega.OmegaLemmas.
(* From Equations Require Export Equations. *)

Require Export Lia.

Require Init.Peano.
Require Arith.PeanoNat.
(* Require Export Bool.BoolEq. *)
Require Export Classes.RelationClasses.

Require Export ZArith Int.
Open Scope Z_scope.
Open Scope Int_scope.
Require Export Floats.

Notation "# x" := (exist (fun _ => True) x I) (at level 60).
Global Notation Bool := {_:bool | True}.
Global Notation "⌊ x -⌋" := (proj1_sig x) (at level 1).

Definition addZ (m n: {_:Z | True}): {_:Z|True} := exist _ (proj1_sig m + proj1_sig n) I.
Infix "+Z" := addZ (at level 70).
Inductive addZ_rel: Z -> Z -> Z -> Prop :=
  addZ_def: forall (m n:Z), addZ_rel m n (m + n).
#[global] Hint Constructors addZ_rel : core_hint_db.

Definition lebZ (m n: {_:Z | True}): {_:bool|True} := # (proj1_sig m <=? proj1_sig n).
Infix "<=Z" := lebZ (at level 70).
Inductive lebZ_rel: Z -> Z -> bool -> Prop :=
  lebZ_def: forall (m n:Z), lebZ_rel m n (Z.leb m n).
#[global] Hint Constructors lebZ_rel : core_hint_db.

Definition ltbZ (m n: {_:Z | True}): {_:bool|True} := # (proj1_sig m <? proj1_sig n).
Infix "<Z" := ltbZ (at level 70).
Inductive ltbZ_rel: Z -> Z -> bool -> Prop :=
  ltbZ_def: forall (m n:Z), ltbZ_rel m n (Z.ltb m n).
#[global] Hint Constructors ltbZ_rel : core_hint_db.

Definition gebZ (m n: {_:Z | True}): {_:bool|True} := # (proj1_sig m >=? proj1_sig n).
Infix ">=Z" := gebZ (at level 70).
Inductive gebZ_rel: Z -> Z -> bool -> Prop :=
  gebZ_def: forall (m n:Z), gebZ_rel m n (Z.geb m n).
#[global] Hint Constructors gebZ_rel : core_hint_db.

Definition gtbZ (m n: {_:Z | True}): {_:bool|True} := # (proj1_sig m >? proj1_sig n).
Infix ">Z" := gtbZ (at level 70).
Inductive gtbZ_rel: Z -> Z -> bool -> Prop :=
  gtbZ_def: forall (m n:Z), gtbZ_rel m n (Z.gtb m n).
#[global] Hint Constructors gtbZ_rel : core_hint_db.

Definition eqbZ (m n: {_:Z | True}): {_:bool|True} := # (Z.eqb (proj1_sig m) (proj1_sig n)).
Infix "=?Z" := eqbZ (at level 70).
Inductive eqbZ_rel: Z -> Z -> bool -> Prop :=
  eqbZ_def: forall (m n:Z), eqbZ_rel m n (m =? n).
#[global] Hint Constructors eqbZ_rel : core_hint_db.

Definition subZ (m n : {_:Z | True}): {_:Z|True} := exist _ (proj1_sig m - proj1_sig n) I.
Infix "-Z" := subZ (at level 35).
Inductive subZ_rel: Z -> Z -> Z -> Prop :=
  subZ_def: forall (m n:Z), subZ_rel m n (m - n).
#[global] Hint Constructors subZ_rel : core_hint_db.

Definition multZ (m n: {_:Z | True}): {_:Z|True} := exist _ (proj1_sig m * proj1_sig n) I.
Infix "*Z" := multZ (at level 40).
Inductive multZ_rel: Z -> Z -> Z -> Prop :=
  multZ_def: forall (m n:Z), multZ_rel m n (m * n).
#[global] Hint Constructors multZ_rel : core_hint_db.

Definition divZ (m : {_:Z | True}) (n: {n:Z | n <> 0}) := exist (fun v => True) (proj1_sig m / proj1_sig n) I.
Infix "/Z" := divZ (at level 40).
Inductive divZ_rel: Z -> Z -> Z -> Prop :=
  divZ_def: forall (m n:Z), divZ_rel m n (m / n).
#[global] Hint Constructors divZ_rel : core_hint_db.

Definition negBool (b : Bool) := exist (fun v => True) (negb (proj1_sig b)) I.
Inductive negBool_rel: bool -> bool -> Prop :=
  negBool_def: forall (b:bool), negBool_rel b (negb b).
#[global] Hint Constructors negBool_rel : core_hint_db.
