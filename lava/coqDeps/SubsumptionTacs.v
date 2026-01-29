Load LiquidPrelude.

(* Needed to allow packs to occur as type arguments to other packs *)
Class GeneralizedProjection {A A':Type} := {
  proj: A' -> A; (* the projection operator itself *)
  po: forall (x y:A'), proj x = proj y -> x = y (* "proof irrelevance" for the "refined" type w.r.t. proj *)
}.
Global Notation "⌊ x ⌋" := (proj x) (at level 1).

#[global] Instance refinement_proj {A:Type} {p:A -> Prop} : @GeneralizedProjection A {x:A | p x} := { 
	proj := @proj1_sig A p;
  po := ltac:(destruct x as [x xp], y as [y yp]; simpl in *; intros ->; f_equal; apply proof_irrelevance)
}.
Global Notation "A' ⤖ A" := (@GeneralizedProjection A A') (at level 1).

Notation "⌊ tm _⌋" := (let (a, _) := tm in a) (at level 1).

Definition refWitness (A:Type) (p: A -> Prop) (x: {x' : A | p x'}): p (` x).
Proof.
  destruct x as [x' xp]. 
  exact xp.
Defined.
Notation "⌈ x ⌉" := (refWitness _ _ x) (at level 1).

Inductive sub : Type -> Type -> Type :=
| sub_refl : forall A: Type, sub A A
| sub_ref : forall (T:Type) (G:T->Prop) (H:T->Prop), (forall x, G x -> H x) -> sub {x:T | G x} {x:T | H x}
| sub_fun : forall (A1 B1 A2 B2:Type), sub A2 A1 -> sub B1 B2 -> sub (A1 -> B1) (A2 -> B2)
(* for constructors of inductive data types which return unrefined terms*)
| sub_triv: forall (A:Type) (H:A->Prop), (forall x, H x) -> sub A {x:A | H x}.
Notation "A <: B" := (sub A B) (at level 40). 

Ltac sub_simpl := match goal with
  | [ |- ?t <: ?t'] => 
    first [apply sub_refl  | apply sub_triv | apply sub_ref  | apply sub_fun]
  | _ => fail "not a subsumption goal"
end.

Definition subCast : forall (A A':Type), A -> (A <: A') -> A'.
Proof.
  intros A A' x p. 
  induction p.
  - exact x.
  - destruct x as [x Gx]. exact (exist _ x (h x Gx)).
  - exact (IHp2 ∘ (x ∘ IHp1)).
  - exact (exist _ x (h x)).
Defined. 
Notation "x ↪ A'" := (subCast _ A' x _) (at level 40). 

Definition app_sub : forall (A B A':Type), (A -> B) -> A' -> (A' <: A) -> B.
Proof.
  intros A B A' f x p.
  exact (f (subCast A' A x p)).
Defined.
Notation "f _@_ x" := (app_sub _ _ _ f x _) (at level 60).

(*
(* equality on subset types with proof irrelevance *)
Notation "x `= y" := (@eq _ (` x) (` y)) (at level 70).*)

(* Simplified version of subsequent definition
Definition subCast1' (A:Type) (G:A -> Prop) (H: A -> Prop) (p: forall x, G x -> H x) (x: {x: A | G x}): {y:A | H y}.
Proof.
  destruct x as [x Gx]. exact (exist x (p x Gx)). 
Defined.*)

Definition subCast' (A:Type) (G:A -> Prop) (H: A -> Prop) (x: {x: A | G x}) (p: G (` x) -> H (` x)) : {x': A | G x' /\ x' = ` x} <: {y:A | H y}.
Proof.
  apply sub_ref. intro y. intro K. destruct K as [K ->]. apply (p K). 
Defined. 

Definition subsumptionCast (A:Type) [G:A -> Prop] (H: A -> Prop) (x: {x: A | G x}) (p: G (` x) -> H (` x)) : {y:A | H y}.
Proof.
  (* apply (subCast {x': A | G x' /\ x' = ` x} {y:A | H y} (exist _ (` x) (conj ⌈ x ⌉ eq_refl)) (subCast' A G H x p)). *)
  exact (exist H (` x) (p ⌈ x ⌉)).
Defined. 

(* Defined by Loïc, injections and subsumption with two arguments only to be closer to paper *)
Definition injCastP {A:Type} {G:A -> Prop} (x: A) (p: G x) : {y: A | G y} :=
  exist G x p.
Definition subCastP {A:Type} {G:A -> Prop} {H: A -> Prop}
(x: {x: A | G x}) (p: G (` x) -> H (` x)) : {y:A | H y} :=
  exist H (` x) (p ⌈ x ⌉).
Definition subsumptionTrue {A:Type} {G:A -> Prop} (x: {x: A | G x}) : {y:A | True} :=
  subsumptionCast A (fun _ => True) x (fun _ => I).

Definition injectionCast (A:Type) (H: A -> Prop) (x: A) (p: H x) : {y:A | H y}.
Proof.
  assert (eqRes: x = x) by (exact eq_refl).
  assert (Hsubs: forall y:A, y = x -> H y) by (now now intros y <-).
  exact (subCast {y:A| y = x} {y:A | H y} (exist _ x eqRes) (sub_ref A (fun y:A => y = x) H Hsubs)).
Defined.

Definition injectionCast' (A:Type) (H: A -> Prop) (x: A) (p: H x) : {y:A | y = x /\ H y}.
Proof.
  assert (eqRes: x = x) by (exact eq_refl).
  assert (Hsubs: forall y:A, y = x -> y = x /\ H y) by (now intros y ->). 
  exact (subCast {y:A| y = x} {y:A | y = x /\ H y} (exist _ x eqRes) (sub_ref A (fun y:A => y = x) (fun y:A => y = x /\ H y) Hsubs)).
Defined.

Definition injectionCast'' (A:Type) (H: A -> Prop) (x: A) (p: H x) : {y:A | H y}.
Proof.
  exact (exist _ x p).
Defined.

Class GeneralizedSubsumptionCast {A X:Type} (Y:Type) {prX: X ⤖ A}  {prY: Y ⤖ A} (x: X) := {
  genSubCast: Y; (*the subsumption cast itself *)
  cast_pr: prY.(proj) genSubCast = prX.(proj) x
}.
Global Notation "Y ↼ x" := (GeneralizedSubsumptionCast Y x) (at level 1).
#[global] Instance subRef {A: Type} [G:A -> Prop] (H: A -> Prop) (x: {x: A | G x}) (p: G (` x) -> H (` x)): 
  @GeneralizedSubsumptionCast A {v:A | G v} {v:A | H v} refinement_proj refinement_proj x := { 
	genSubCast := subsumptionCast A H x p;
  cast_pr := (ltac:(reflexivity))
}.