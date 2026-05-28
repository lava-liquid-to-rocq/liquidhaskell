From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Set Universe Polymorphism.
From Coq Require Import Unicode.Utf8.

Inductive Nats_u: Type :=
  | Suc_u: Nats_u → Nats_u | Zero_u: Nats_u.

Fixpoint Nats_eq (x y : Nats_u): bool :=
  match (x, y) with
  | (Suc_u n, Suc_u n') => true && Nats_eq n n'
  | (Zero_u, Zero_u) => true
  | (_, _) => false
  end.

Theorem Nats_eq_refl : ∀ (x : Nats_u), is_true (Nats_eq x x).
Proof.
  eq_refl_rec.
Qed.

#[global] Hint Resolve Nats_eq_refl: eq_hint_db.

Theorem Nats_eqb_eq : ∀ (s t : Nats_u), is_true (Nats_eq s t) → s = t.
Proof.
  eqb_eq_lem.
Qed.

#[global] Hint Resolve Nats_eqb_eq: eq_hint_db.

#[global] Instance leibnitz_eq_Nats: LeibnitzEqB := {
    equalB' := Nats_eq;
    refl' := Nats_eq_refl;
    eqb_eq' := Nats_eqb_eq }.

Fixpoint Nats_wf (x : Nats_u): Prop :=
  match x with | Suc_u n => Nats_wf n ∧ True | Zero_u => True end.

Theorem Nats_wf_ref [p : Nats_u → Prop] (tm : {v: Nats_u | Nats_wf v ∧ p v}): Nats_wf ⌊ tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation Nats := {x: Nats_u | Nats_wf x ∧ True}.

Definition Suc_lem (n : Nats): Nats_wf (Suc_u ⌊ n -⌋) ∧ True.
Proof.
  repeat first [split | solver].
Defined.

Definition Suc (n : Nats): Nats :=
  exist _ (Suc_u ⌊ n -⌋) (Suc_lem n).

Definition Zero_lem : Nats_wf Zero_u ∧ True.
Proof.
  repeat first [split | solver].
Defined.

Definition Zero : Nats :=
  exist _ Zero_u Zero_lem.

Definition wf_Suc_n [n : Nats_u] (p : Nats_wf (Suc_u n)): Nats_wf n.
Proof.
  quicksolve.
Defined.

#[global] Hint Resolve wf_Suc_n: ref_constr_db.

#[global] Hint Resolve Nats_wf_ref: wf_constr_db.

#[global] Hint Unfold Nats_wf: wf_constr_db.

#[global] Hint Resolve Nats_eq: ref_constr_db.

#[global] Hint Unfold Suc: ref_constr_db.

#[global] Hint Unfold Zero: ref_constr_db.

Definition even_spec (ds_d1Za : Nats): Type :=
  Bool.

#[global] Hint Unfold even_spec: lia_unfold.

Definition even (ds_d1Za : Nats): even_spec ds_d1Za.
Proof.
  destruct ds_d1Za as [ds_d1Za ds_d1Za_p].
  induction ds_d1Za as [n IH_n|].
  - refine (subsumptionCast
            bool
            (λ (VV : bool), True)
            (negBool (IH_n ltac:(try clear IH_n; solver)))
            ltac:(solver)).
  - refine (# true).
Defined.

Inductive even_rel: Nats_u → bool → Prop :=
  | even_Suc: ∀ n (even_res : bool), even_rel n even_res → even_rel (Suc_u n) (negb even_res)
  | even_Zero: even_rel Zero_u true.

#[global] Hint Constructors even_rel: core_hint_db.

#[global] Instance even_lookup_rel: dictionary rel even := { lookup' := even_rel }.

#[global] Instance even_getF: getFunc even_rel := { getF' := even }.

Theorem even_rel_funct [ds_d1Za : Nats_u]:
  ∀ (VV VV' : bool), even_rel ds_d1Za VV → (even_rel ds_d1Za VV' → VV = VV').
Proof.
  induction ds_d1Za as [n IH_n|]; rel_functionhood_body.
Qed.

#[global] Hint Resolve even_rel_funct: f_rel_funct_db.

#[global] Instance even_lookup_funct: dictionary functionhood even := {
    lookup' := even_rel_funct }.

Theorem even_Suc_lem n even_Suc_lem_res:
  even_rel (Suc_u n) even_Suc_lem_res
  ↔ ∃ (even_res : bool), even_rel n even_res ∧ even_Suc_lem_res == negb even_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite even_Suc_lem: f_rel_back.

Theorem even_Zero_lem even_Zero_lem_res:
  even_rel Zero_u even_Zero_lem_res ↔ even_Zero_lem_res == true.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite even_Zero_lem: f_rel_back.

Theorem even_rel_ex (ds_d1Za : Nats_u) (ds_d1Za_p : Nats_wf ds_d1Za ∧ True):
  even_rel ds_d1Za ⌊ even (exist _ ds_d1Za ds_d1Za_p) -⌋.
Proof.
  Opaque even.
  existence_lemma_pre even;
  induction ds_d1Za as [n IH_n|];
  [fix_notations; pose proof (IH_n ltac:(try clear IH_n; solver)) as IH_60635587; try clear IH_n |
   fix_notations];
  simpl in *.
  Transparent even.
  all: (existence_lemma_quicksolve even; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve even_rel_ex: rel_ax_db.

#[global] Opaque even.

Theorem even__even_rel_rw (ds_d1Za : Nats_u) (ds_d1Za_p : Nats_wf ds_d1Za ∧ True) (VV : bool):
  ⌊ even (exist _ ds_d1Za ds_d1Za_p) -⌋ = VV ↔ even_rel ds_d1Za VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite even__even_rel_rw: f_rel_funct_db.

#[global] Hint Resolve even__even_rel_rw: rel_ax_db.

#[global] Instance even_lookup_rw: dictionary rwLem even := { lookup' := even__even_rel_rw }.

Theorem even__even_rel (ds_d1Za : Nats) (VV : bool):
  ⌊ even ds_d1Za -⌋ = VV ↔ even_rel ⌊ ds_d1Za ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite even__even_rel: f_rel_funct_db.

Theorem even__even_rel' (ds_d1Za_u : Nats_u) (ds_d1Za : Nats) (VV : bool):
  ds_d1Za_u = ⌊ ds_d1Za ⌋ → ⌊ even ds_d1Za -⌋ = VV ↔ even_rel ds_d1Za_u VV.
Proof.
  intros ->. refine (even__even_rel ds_d1Za VV).
Qed.

#[global] Hint Resolve even__even_rel': f_rel_funct_db.

Theorem even_rel_mk (ds_d1Za : Nats_u) (ds_d1Za_p : Nats_wf ds_d1Za ∧ True):
  {VV: _ | even_rel ds_d1Za VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, even_rel ds_d1Za VV) (even (exist _ ds_d1Za ds_d1Za_p)) _);
  rewrite <- even__even_rel';
  quicksolve.
Qed.

#[global] Hint Resolve even_rel_mk: f_rel_funct_db.

#[global] Instance even_pack:
  @Pack
  (Nats ::RT λ (ds_d1Za : Nats), nilRT)
  (Nats_u ::UT nilUT)
  ltac:(mkProjectsArgListTG (Nats ::RT λ (ds_d1Za : Nats), nilRT) ((Nats_u ::UT nilUT)))
  bool
  (λ (x_18566717 : ArgList (Nats ::RT λ (ds_d1Za : Nats), nilRT)) (v_x_18566717 : bool),
   ltac:(flattenP (λ (ds_d1Za : Nats) (VV : bool), True) x_18566717 v_x_18566717)).
Proof.
  buildPackG even even_rel even__even_rel even_rel_funct.
Defined.

#[global] Instance even_upack: @uPack (Nats_u ::UT nilUT) bool.
Proof.
  buildUPackG even_rel even_rel_funct.
Defined.
