Require Export Setoid.
(** to rewrite using <-> *)
Require Export Classes.Morphisms_Prop.

Require Import ZArith.
Require Export Psatz.
Require Import Coq.Program.Basics.

Require Import Extraction.
Require Import ExtrHaskellBasic.
Require Import Bool.
Require Export Bool.Bool.
Require Export Relation_Definitions.

Class LeibnitzEqB {A: Type} := {
  equalB' : A -> A -> bool;
  refl' : forall (x:A), is_true (equalB' x x);
  eqb_eq': forall (s t: A), is_true (equalB' s t) -> s = t
}.

Definition equalB (A:Type) {instance : LeibnitzEqB}: A -> A -> bool := (@equalB' A) instance.

Notation "x ==? y" := (equalB _ x y) (at level 70).
Notation "x /=? y" := (negb (equalB _ x y)) (at level 70).

Definition equal (A:Type) {instance : LeibnitzEqB} (x y : A): Prop := (x ==? y) = true.
Notation "x == y" := (equal _ x y) (at level 70).
Notation "x /= y" := (x ==? y = false) (at level 70).

Lemma eq_eqb: forall [A: Type] {instance : LeibnitzEqB} (s: A) (t: A), s = t -> s == t. 
Proof.
  intros A instance s t ->. 
  apply refl'.
Qed.

Lemma eqb_eq : forall [A: Type] {instance : LeibnitzEqB} (s: A) (t: A), s = t <-> s == t. 
Proof.
  intros. split; [apply eq_eqb | apply eqb_eq'].
Qed.

(* to use in contexts, where eqb_eq clashes with other lemmata *)
Definition generic_equalb_eq := eqb_eq.

Lemma equal_refl (A:Type) {instance : LeibnitzEqB} (x:A) : x == x. 
Proof. exact (refl' x). Qed.
Lemma equal_sym (A:Type) {instance : LeibnitzEqB} (x y:A) : x == y -> y == x.
Proof.
  intros. rewrite <- eqb_eq in *. symmetry. assumption.
Qed. 

Lemma equal_trans (A:Type) {instance : LeibnitzEqB} (x y z:A) : x == y -> y == z ->  x == z.
Proof.
  intros. rewrite <- eqb_eq in *. transitivity y; assumption.
Qed.

#[global] Instance leibnitz_eq_bool : LeibnitzEqB := { 
	equalB' := Bool.eqb;
  refl' := Bool.eqb_reflx;
  eqb_eq' := Bool.eqb_prop
}.

#[global] Instance leibnitz_eq_Z : LeibnitzEqB := { 
	equalB' := Z.eqb;
  refl' := Z.eqb_refl;
  eqb_eq' := (ltac:(apply Z.eqb_eq)) (* exact wouldn't work here *)
}.

Add Parametric Relation (A:Type) {instance : LeibnitzEqB} : A (equal A) 
  reflexivity proved by (@equal_refl A instance)
  symmetry proved by (@equal_sym A instance)
  transitivity proved by (@equal_trans A instance)
as equal_equivalence.

Add Parametric Morphism (A:Type) {instance : LeibnitzEqB} : (@eq A) with
  signature (equal A) ==> (equal A) ==> (@eq Prop) as eq_mor.
Proof.
  intros. unfold equal in *. pose proof (@eqb_eq' A instance) as K.
  apply (K x y) in H.
  apply (K x0 y0) in H0.
  clear K. subst x. subst x0.
  reflexivity.
Qed.