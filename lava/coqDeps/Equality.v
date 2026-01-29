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

Definition pr1: forall [A B : Prop], A /\ B -> A.
Proof.
  intros A B [p _].
  exact p.
Defined.
Definition pr2: forall [A B : Prop], A /\ B -> B.
Proof.
  intros A B [_ q].
  exact q.
Defined.

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

Lemma neq_rw : forall [A: Type] {instance : LeibnitzEqB} (s t: A), s /= t <-> s ==? t = false. 
Proof.
  intros. unfold not, equal.
  split; intros H; destruct (s ==? t) eqn:E; try easy.
Qed.
Lemma irreflexive_contra : forall [A: Type] {instance : LeibnitzEqB} (s: A), s /= s -> False.
Proof.
  intros. 
  assert (s == s) as K by reflexivity.
  unfold equal in K.
  rewrite K in H.
  discriminate H.
Qed.

Lemma eq_neq_contra : forall [A: Type] {instance : LeibnitzEqB} (s t: A), s == t -> s /= t -> False.
Proof.
  intros A ? s t. rewrite <- eqb_eq. intros ->. apply irreflexive_contra.
Qed.
#[global] Hint Resolve eq_neq_contra:core_hint_db. 

Lemma eqb_ineq: forall [A: Type] {instance : LeibnitzEqB} (s: A) (t: A), s <> t <-> s ==? t = false. 
Proof.
  intros. rewrite eqb_eq. unfold not. 
  destruct (s ==? t) eqn:E; split; intros H; try easy; intros; try (apply H in E; exfalso; apply E). 
  now eapply (eq_neq_contra s t). 
Qed.

(*
Lemma eqb_true: forall [A: Type] {instance : LeibnitzEqB} (s: A) (t: A), (s = t) <-> (s ==? t) = true.
Proof.
  intros A s t.
  split.
  - intros ->. 
  - intros H. apply eqb_eq in H. apply H.
Qed. *)

Lemma istrue_neqb: forall [A:Type] {instance : LeibnitzEqB} (s:A) (t: A), is_true (s /=? t) <-> s <> t.
Proof.
  intros. rewrite eqb_ineq. split; destruct (s ==? t) eqn:E; try rewrite E; easy.
Qed.

Local Lemma true_eqb: forall [A: Type] {instance : LeibnitzEqB} (s: A) (t: A), (s = t) <-> true = (s ==? t).
Proof.
  intros.
  rewrite eqb_eq. 
  assert (sym: (true = (s ==? t)) <-> ((s ==? t) = true)) by (split; intros; now symmetry).
  rewrite sym. clear sym.
  unfold equal, is_true. reflexivity.
Qed.

Lemma eqb_true: forall [A: Type] {instance : LeibnitzEqB} (s: A) (t: A), (s = t) <-> (s ==? t) = true.
Proof.
  intros. 
  assert ((s ==? t) = true <-> true = (s ==? t)) by (split; symmetry; assumption).
  rewrite H.
  apply true_eqb.
Qed.

Local Ltac eqb_reflexivity :=
  solve [repeat progress first [reflexivity | 
    now first [apply true_eqb | apply eqb_ineq | rewrite <- true_eqb | apply eqb_eq | rewrite <- eqb_eq] | 
    simpl; now first [apply true_eqb | apply eqb_ineq | rewrite <- true_eqb | apply eqb_eq | rewrite <- eqb_eq]]].

Local Lemma eqb_symm: forall [A: Type] {instance : LeibnitzEqB} (s t: A), (s ==? t) = (t ==? s).
Proof.
  intros A ? s t. destruct (s ==? t) eqn:E.
  - replace ((s ==? t) = true) with (s == t) in E by reflexivity. rewrite <- (eqb_eq s t) in E. subst s. 
    pose proof (equal_refl A t) as H. now rewrite H.
  - rewrite <- eqb_ineq in E. 
    destruct (t ==? s) eqn:F; [replace ((t ==? s) = true) with (t == s) in F by reflexivity|reflexivity]. 
    apply eqb_eq in F. subst t. exfalso. exact (E eq_refl).
Qed.

Lemma eqb_inject: forall [A B:Type] {instanceA : @LeibnitzEqB A} {instanceB : @LeibnitzEqB B} (s t: A) (c: A -> B), (forall (x y:A), c x = c y -> x = y) -> ((c s ==? c t) = (s ==? t)).
Proof.
  intros A B ? ? s t c inj. 
  destruct (s ==? t) eqn:E; [replace ((s ==? t) = true) with (s == t) in E by reflexivity; rewrite <- (eqb_eq s t) in E|].
  - subst s. apply equal_refl.
  - rewrite <- eqb_ineq in *. unfold not in *; intros.
    apply (E (inj s t H)).
Qed.
Ltac eqb_inject_s := first [apply eqb_inject| apply eq_sym; apply eqb_inject].
Ltac eqb_inject_ind :=
  let x' := fresh "x" in
  let y' := fresh "y" in
  let H' := fresh "H" in
  tryif eqb_inject_s
    then 
      (tryif intros x' y' H'; now injection H'
       then intros x' y' H'; now injection H' else fail "Not an inductive constructor")
    else fail "wrong shape".

(* tries to solve s ==? t = s' ==? t' by case distinctions on the ==?s on both sides *)  
Ltac double_match_eqb s t s' t' :=
  destruct (s ==? t) eqn:lEq; [rewrite <- eqb_eq in lEq; try first [rewrite lEq in * | rewrite <- lEq in *] |rewrite <- eqb_ineq in lEq];
  [ destruct (s' ==? t') eqn:rEq; [
    eqb_reflexivity
    | rewrite <- eqb_ineq in rEq; exfalso; now (first [apply rEq | apply rEq; try first [apply eqb_eq | apply eqb_symm; apply eqb_eq]])]
  | destruct (s' ==? t') eqn:rEq; (unfold s' in rEq; unfold t' in rEq); 
    [ rewrite <- eqb_eq in rEq; try first [rewrite rEq in * | rewrite <- rEq in *]; exfalso; first [ now apply lEq | now (apply lEq; try first [apply eqb_eq | apply eqb_symm; apply eqb_eq])]
    | first [eqb_reflexivity | first [rewrite rEq | simpl in rEq; rewrite rEq]; eqb_reflexivity]]
  ].

Lemma andb_true : forall b c, (b && c) = true <-> b = true /\ c = true.
Proof.
  intros b c. split; intros H. 
  - destruct b; try easy.
  - destruct H as [-> ->]. easy.
Qed.

(* matches on goal and tries to apply double_match_eqb if possible *) 
Ltac eqb_eqb := match goal with
  | [|- ?s ==? ?t = ?u ==? ?v] => 
    let s' := fresh "s'" in 
    let t' := fresh "t'" in 
    pose u as s'; pose v as t'; double_match_eqb s t s' t'
  | [|- ?s ==? ?t = ?s ==? ?v] => 
    let s' := fresh "s'" in 
    let t' := fresh "t'" in 
    pose s as s'; pose v as t'; double_match_eqb s t s' t'
  | [|- ?s ==? ?t = ?u ==? ?t] => 
    let s' := fresh "s'" in 
    let t' := fresh "t'" in 
    pose t as t'; pose u as s'; double_match_eqb s t s' t'
  | [|- ?s ==? ?t = ?s ==? ?t] => 
    let s' := fresh "s'" in 
    let t' := fresh "t'" in 
    pose s as s'; pose t as t'; double_match_eqb s t s' t'
  | |- (?l && ?r) = true => rewrite andb_true
  | _ => idtac "not an equality of bool-valued equalities"
  end.

Lemma eqb_eqb': forall [A: Type] {instance : LeibnitzEqB} (s t s' t': A), s = s' -> t = t' -> (s ==? t) = (s' ==? t').
Proof.
  intros A ? s t s' t' -> ->.
  reflexivity.
Qed.

Lemma eqb_false: forall [A: Type] {instance : LeibnitzEqB} (s t: A), (s <> t) <-> (s ==? t) = false.
Proof.
  intros A s t.
  split.
  - intros H. now apply eqb_ineq. 
  - intros H. apply eqb_ineq in H. apply H.
Qed.
Lemma false_eqb: forall [A: Type] {instance : LeibnitzEqB} (s t: A), (s <> t) <-> false = (s ==? t).
Proof.
  intros A s t. split.
  - intros H. apply eq_sym. now apply eqb_ineq.
  - intros H. apply eq_sym in H. now apply eqb_ineq in H. 
Qed.

Lemma eq_eqb_ante: forall [A: Type] {instance : LeibnitzEqB} (s t: A) (b: bool) (H: bool) (z: s = t <-> is_true H), b = (s ==? t) -> b = H.
Proof.
  intros A ? s t b H z K.
  destruct b eqn:E.
  - apply true_eqb in K. rewrite K in *. destruct z as [z _]. specialize (z (eq_refl t)). easy.
  - apply false_eqb in K. destruct H.
    + destruct z as [_ z]. specialize (z eq_refl). rewrite z in K. exfalso. now apply K.
    + reflexivity.
Qed.

Lemma isTrue_neg: forall (b: bool), is_true (negb b) <-> b = false.
  intros b. split.
  - intro H. unfold is_true in H. unfold negb in H. destruct b; [inversion H|reflexivity].
  - intros ->. reflexivity.
Qed.