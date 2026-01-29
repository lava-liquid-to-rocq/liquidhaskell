(** to enable rewriting using other relations not just = *)
Require Export Setoid.
(** to rewrite using <-> *)
Require Export Classes.Morphisms_Prop.

Require Import ZArith.
Require Export Psatz.
Require Import Coq.Program.Basics.

Require Import Extraction.
Require Import ExtrHaskellBasic.
Require Import Bool.

Class EqB {A: Type} := {
  equalB' : A -> A -> bool
}.

Definition equalB {A:Type} {instance : EqB}: A -> A -> bool := (@equalB' A) instance.

#[global] Instance eqb_Z : EqB := { 
	equalB' := Z.eqb
}.
#[global] Instance eqb_bool : EqB := { 
	equalB' := Bool.eqb
}.

(*
TODO: get rid of the nonsense below and use the above class instead, 
  rather add reflexivity, symmetry and transivitity lemmata for all instances and set up setoid rewrite for them
*)

Local Definition neqb (p q:Z) : bool := negb (Z.eqb p q).
Infix "!=?" := neqb (at level 70).

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

(* ToDo: Can we come up with a better way to define this *)
Local Axiom Equalb: forall [A: Type] (s: A) (t: A), bool.
(* Local Axiom eqb_refl: forall [A: Type] (s: A), @Equalb A s s = true. *)
Local Axiom eqb_eq: forall [A: Type] (s: A) (t: A), s = t <-> @Equalb A s t = true. 

(* ToDo: Add necessary lemmata and extend shape_based tactic to better handle this equality *)
Local Axiom EquivB: forall (s: Prop) (t: Prop), bool.
Local Axiom equivb_equiv: forall (s t: Prop), (s <-> t) <-> EquivB s t = true. 

Local Lemma eqb_ineq: forall [A: Type] (s: A) (t: A), s <> t <-> @Equalb A s t = false. 
Proof.
  intros. split; intro H.
  - unfold not in H. 
    assert (K: @Equalb A s t = true -> False).
    { intro K. apply H. apply eqb_eq. apply K. }
    destruct (Equalb s t).
    + exfalso. now apply K.
    + reflexivity.
  - unfold not. intro K.
    destruct (Equalb s t) as [] eqn: E.
    + discriminate H. 
    + apply eqb_eq in K. rewrite E in K.
      discriminate K.
Qed.
Local Lemma eqb_refl: forall [A: Type] (s: A), @Equalb A s s = true.
Proof.
  intros. apply (pr1 (eqb_eq s s)). exact eq_refl.
Qed. 
Notation "s ==? t" := (Equalb s t) (at level 70).
Notation "s <=>? t" := (EquivB s t) (at level 70).
Notation "s /=? t" := (negb (s ==? t)) (at level 70).

Local Lemma eqb_true: forall [A: Type] (s: A) (t: A), (s = t) <-> (s ==? t) = true.
Proof.
  intros A s t.
  split.
  - intros ->. apply eqb_refl.
  - intros H. apply eqb_eq in H. apply H.
Qed.

Local Lemma istrue_neqb: forall [A:Type] (s:A) (t: A), is_true (s /=? t) <-> s <> t.
Proof.
  intros. unfold is_true. unfold negb. destruct (s ==? t) eqn:E.
  - rewrite <- eqb_true in E. easy.
  - rewrite <- eqb_ineq in E. easy.
Qed.

Local Lemma true_eqb: forall [A: Type] (s: A) (t: A), (s = t) <-> true = (s ==? t).
Proof.
  intros A s t. split.
  - intros ->. apply eq_sym. apply eqb_refl.
  - intros H. apply eq_sym in H. apply eqb_eq in H. apply H.
Qed.
Local Ltac eqb_reflexivity :=
  first [reflexivity | now first [apply true_eqb | (rewrite <- true_eqb) | apply eqb_true | (rewrite <- eqb_true)] | simpl; now first [apply true_eqb | (rewrite <- true_eqb) | apply eqb_true | (rewrite <- eqb_true)]].

Local Lemma eqb_symm: forall [A: Type] (s t: A), @Equalb A s t = @Equalb A t s.
Proof.
  intros A s t. 
  destruct (s ==? t) eqn:lEq; [rewrite <- eqb_true in lEq; rewrite lEq in *|rewrite <- eqb_ineq in lEq].
  - destruct (t ==? t) eqn:rEq; [reflexivity| rewrite <- eqb_ineq in rEq]. exfalso. now apply rEq.
  - destruct (t ==? s) eqn:rEq; [rewrite <- eqb_true in rEq; rewrite rEq in *|reflexivity]. exfalso. now apply lEq.
Qed.

Local Lemma eqb_inject: forall [A B:Type] (s t: A) (c: A -> B), (forall (x y:A), c x = c y -> x = y) -> ((c s ==? c t) = (s ==? t)).
Proof.
  intros A B s t c inj. apply eqb_true.
  destruct (c s ==? c t) eqn:E; rewrite eqb_symm; rewrite <- eqb_true. 
  - rewrite <- eqb_true.
    rewrite <- eqb_true in E. apply inj. apply E.
  - apply eqb_ineq. apply eqb_ineq in E. intro.
    apply E. f_equal. apply H. 
Qed.
Local Ltac eqb_inject_s := first [apply eqb_inject| apply eq_sym; apply eqb_inject].
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
  destruct (s ==? t) eqn:lEq; [rewrite <- eqb_true in lEq; try first [rewrite lEq in * | rewrite <- lEq in *] |rewrite <- eqb_ineq in lEq];
  [ destruct (s' ==? t') eqn:rEq; [
    eqb_reflexivity
    | rewrite <- eqb_ineq in rEq; exfalso; now (first [apply rEq | apply rEq; try first [apply eqb_true | apply eqb_symm; apply eqb_true]])]
  | destruct (s' ==? t') eqn:rEq; (unfold s' in rEq; unfold t' in rEq); 
    [ rewrite <- eqb_true in rEq; try first [rewrite rEq in * | rewrite <- rEq in *]; exfalso; first [ now apply lEq | now (apply lEq; try first [apply eqb_true | apply eqb_symm; apply eqb_true])]
    | first [eqb_reflexivity | first [rewrite rEq | simpl in rEq; rewrite rEq]; eqb_reflexivity]]
  ].

(* matches on goal and tries to apply double_match_eqb if possible *) 
Ltac eqb_eqb := match goal with
  | [|- @Equalb ?A ?s ?t = @Equalb ?A ?u ?v] => 
    let s' := fresh "s'" in 
    let t' := fresh "t'" in 
    pose u as s'; pose v as t'; double_match_eqb s t s' t'
  | [|- @Equalb ?A ?s ?t = @Equalb ?A ?s ?v] => 
    let s' := fresh "s'" in 
    let t' := fresh "t'" in 
    pose s as s'; pose v as t'; double_match_eqb s t s' t'
  | [|- @Equalb ?A ?s ?t = @Equalb ?A ?u ?t] => 
    let s' := fresh "s'" in 
    let t' := fresh "t'" in 
    pose t as t'; pose u as s'; double_match_eqb s t s' t'
  | [|- @Equalb ?A ?s ?t = @Equalb ?A ?s ?t] => 
    let s' := fresh "s'" in 
    let t' := fresh "t'" in 
    pose s as s'; pose t as t'; double_match_eqb s t s' t'
  | _ => idtac "not an equality of bool-valued equalities"
  end.

Local Lemma eqb_eqb': forall [A: Type] (s t s' t': A), s = s' -> t = t' -> @Equalb A s t = @Equalb A s' t'.
Proof.
  intros A s t s' t' -> ->.
  reflexivity.
Qed.


Local Lemma eqb_false: forall [A: Type] (s t: A), (s <> t) <-> (s ==? t) = false.
Proof.
  intros A s t.
  split.
  - intros H. now apply eqb_ineq. 
  - intros H. apply eqb_ineq in H. apply H.
Qed.
Local Lemma false_eqb: forall [A: Type] (s t: A), (s <> t) <-> false = (s ==? t).
Proof.
  intros A s t. split.
  - intros H. apply eq_sym. now apply eqb_ineq.
  - intros H. apply eq_sym in H. now apply eqb_ineq in H. 
Qed.

Lemma eq_eqb_ante: forall [A: Type] (s t: A) (b: bool) (H: bool) (z: s = t <-> is_true H), b = (s ==? t) -> b = H.
Proof.
  intros A s t b H z K.
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