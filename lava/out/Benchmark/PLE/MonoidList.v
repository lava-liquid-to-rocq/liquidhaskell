From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Set Universe Polymorphism.
From Coq Require Import Unicode.Utf8.

Inductive L_u: Type :=
  | C_u: Z → L_u → L_u | Emp_u: L_u.

Fixpoint L_eq (x y : L_u): bool :=
  match (x, y) with
  | (C_u VV VV_, C_u VV' VV_') => (true && (VV ==? VV')) && L_eq VV_ VV_'
  | (Emp_u, Emp_u) => true
  | (_, _) => false
  end.

Theorem L_eq_refl : ∀ (x : L_u), is_true (L_eq x x).
Proof.
  eq_refl_rec.
Qed.

#[global] Hint Resolve L_eq_refl: eq_hint_db.

Theorem L_eqb_eq : ∀ (s t : L_u), is_true (L_eq s t) → s = t.
Proof.
  eqb_eq_lem.
Qed.

#[global] Hint Resolve L_eqb_eq: eq_hint_db.

#[global] Instance leibnitz_eq_L: LeibnitzEqB := {
    equalB' := L_eq;
    refl' := L_eq_refl;
    eqb_eq' := L_eqb_eq }.

Fixpoint L_wf (x : L_u): Prop :=
  match x with | C_u VV VV_ => L_wf VV_ ∧ True | Emp_u => True end.

Theorem L_wf_ref [p : L_u → Prop] (tm : {v: L_u | L_wf v ∧ p v}): L_wf ⌊ tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation L := {x: L_u | L_wf x ∧ True}.

Definition C_lem (VV : {VV: Z | True}) (VV_ : L): L_wf (C_u ⌊ VV -⌋ ⌊ VV_ -⌋) ∧ True.
Proof.
  repeat first [split | solver].
Defined.

Definition C (VV : {VV: Z | True}) (VV_ : L): L :=
  exist _ (C_u ⌊ VV -⌋ ⌊ VV_ -⌋) (C_lem VV VV_).

Definition Emp_lem : L_wf Emp_u ∧ True.
Proof.
  repeat first [split | solver].
Defined.

Definition Emp : L :=
  exist _ Emp_u Emp_lem.

Definition wf_C_VV_ [VV : Z] [VV_ : L_u] (p : L_wf (C_u VV VV_)): L_wf VV_.
Proof.
  quicksolve.
Defined.

#[global] Hint Resolve wf_C_VV_: ref_constr_db.

#[global] Hint Resolve L_wf_ref: wf_constr_db.

#[global] Hint Unfold L_wf: wf_constr_db.

#[global] Hint Resolve L_eq: ref_constr_db.

#[global] Hint Unfold C: ref_constr_db.

#[global] Hint Unfold Emp: ref_constr_db.

Definition mappend_spec (ds_d3ZP ys : L): Type :=
  L.

#[global] Hint Unfold mappend_spec: lia_unfold.

Definition mappend (ds_d3ZP ys : L): mappend_spec ds_d3ZP ys.
Proof.
  destruct ds_d3ZP as [ds_d3ZP ds_d3ZP_p].
  destruct ys as [ys ys_p].
  try revert ys_p; generalize dependent ys; induction ds_d3ZP as [x xs IH_xs|]; intros.
  - refine (C (# x) (IH_xs ltac:(try clear IH_xs; solver) ys ltac:(try clear IH_xs; solver))).
  - refine (exist (λ (ys : L_u), L_wf ys ∧ True) ys ltac:(solver)).
Defined.

Inductive mappend_rel: L_u → L_u → L_u → Prop :=
  | mappend_C_x: ∀ x xs ys (mappend_res : L_u),
                 mappend_rel xs ys mappend_res → mappend_rel (C_u x xs) ys (C_u x mappend_res)
  | mappend_Emp_x: ∀ ys, mappend_rel Emp_u ys ys.

#[global] Hint Constructors mappend_rel: core_hint_db.

#[global] Instance mappend_lookup_rel: dictionary rel mappend := { lookup' := mappend_rel }.

#[global] Instance mappend_getF: getFunc mappend_rel := { getF' := mappend }.

Theorem mappend_rel_funct [ds_d3ZP ys : L_u]:
  ∀ (VV VV' : L_u), mappend_rel ds_d3ZP ys VV → (mappend_rel ds_d3ZP ys VV' → VV = VV').
Proof.
  try revert ys_p; generalize dependent ys; induction ds_d3ZP as [x xs IH_xs|]; intros;
  rel_functionhood_body.
Qed.

#[global] Hint Resolve mappend_rel_funct: f_rel_funct_db.

#[global] Instance mappend_lookup_funct: dictionary functionhood mappend := {
    lookup' := mappend_rel_funct }.

Theorem mappend_C_x_lem x xs ys mappend_C_x_lem_res:
  mappend_rel (C_u x xs) ys mappend_C_x_lem_res
  ↔ ∃ (mappend_res : L_u), mappend_rel xs ys mappend_res ∧ mappend_C_x_lem_res == C_u x mappend_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite mappend_C_x_lem: f_rel_back.

Theorem mappend_Emp_x_lem ys mappend_Emp_x_lem_res:
  mappend_rel Emp_u ys mappend_Emp_x_lem_res ↔ mappend_Emp_x_lem_res == ys.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite mappend_Emp_x_lem: f_rel_back.

Theorem mappend_rel_ex
  (ds_d3ZP : L_u) (ds_d3ZP_p : L_wf ds_d3ZP ∧ True) (ys : L_u) (ys_p : L_wf ys ∧ True):
  mappend_rel ds_d3ZP ys ⌊ mappend (exist _ ds_d3ZP ds_d3ZP_p) (exist _ ys ys_p) -⌋.
Proof.
  Opaque mappend.
  existence_lemma_pre mappend;
  try revert ys_p; generalize dependent ys; induction ds_d3ZP as [x xs IH_xs|]; intros;
  [fix_notations;
   pose proof (IH_xs ltac:(try clear IH_xs; solver) ys ltac:(try clear IH_xs; solver)) as IH_47088561;
   try clear IH_xs |
   fix_notations];
  simpl in *.
  Transparent mappend.
  all: (existence_lemma_quicksolve mappend; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve mappend_rel_ex: rel_ax_db.

#[global] Opaque mappend.

Theorem mappend__mappend_rel_rw
  (ds_d3ZP : L_u) (ds_d3ZP_p : L_wf ds_d3ZP ∧ True) (ys : L_u) (ys_p : L_wf ys ∧ True) (VV : L_u):
  ⌊ mappend (exist _ ds_d3ZP ds_d3ZP_p) (exist _ ys ys_p) -⌋ = VV ↔ mappend_rel ds_d3ZP ys VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite mappend__mappend_rel_rw: f_rel_funct_db.

#[global] Hint Resolve mappend__mappend_rel_rw: rel_ax_db.

#[global] Instance mappend_lookup_rw: dictionary rwLem mappend := {
    lookup' := mappend__mappend_rel_rw }.

Theorem mappend__mappend_rel (ds_d3ZP ys : L) (VV : L_u):
  ⌊ mappend ds_d3ZP ys -⌋ = VV ↔ mappend_rel ⌊ ds_d3ZP ⌋ ⌊ ys ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite mappend__mappend_rel: f_rel_funct_db.

Theorem mappend__mappend_rel' (ds_d3ZP_u ys_u : L_u) (ds_d3ZP ys : L) (VV : L_u):
  ds_d3ZP_u = ⌊ ds_d3ZP ⌋
  → (ys_u = ⌊ ys ⌋ → ⌊ mappend ds_d3ZP ys -⌋ = VV ↔ mappend_rel ds_d3ZP_u ys_u VV).
Proof.
  intros -> ->. refine (mappend__mappend_rel ds_d3ZP ys VV).
Qed.

#[global] Hint Resolve mappend__mappend_rel': f_rel_funct_db.

Theorem mappend_rel_mk
  (ds_d3ZP : L_u) (ds_d3ZP_p : L_wf ds_d3ZP ∧ True) (ys : L_u) (ys_p : L_wf ys ∧ True):
  {VV: _ | mappend_rel ds_d3ZP ys VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, mappend_rel ds_d3ZP ys VV)
          (mappend (exist _ ds_d3ZP ds_d3ZP_p) (exist _ ys ys_p))
          _);
  rewrite <- mappend__mappend_rel';
  quicksolve.
Qed.

#[global] Hint Resolve mappend_rel_mk: f_rel_funct_db.

#[global] Instance mappend_pack:
  @Pack
  (L ::RT λ (ds_d3ZP : L), L ::RT λ (ys : L), nilRT)
  (L_u ::UT (L_u ::UT nilUT))
  ltac:(mkProjectsArgListTG (L ::RT λ (ds_d3ZP : L), L ::RT λ (ys : L), nilRT) ((L_u ::UT (L_u ::UT nilUT))))
  L_u
  (λ (x_83637771 : ArgList (L ::RT λ (ds_d3ZP : L), L ::RT λ (ys : L), nilRT)) (v_x_83637771 : L_u),
   ltac:(flattenP (λ (ds_d3ZP ys : L) (VV : L_u), L_wf VV ∧ True) x_83637771 v_x_83637771)).
Proof.
  buildPackG mappend mappend_rel mappend__mappend_rel mappend_rel_funct.
Defined.

#[global] Instance mappend_upack: @uPack (L_u ::UT (L_u ::UT nilUT)) L_u.
Proof.
  buildUPackG mappend_rel mappend_rel_funct.
Defined.

Definition mappend_assoc_spec (ds_d3ZN ys zs : L): Type :=
  {{∃ (mappend_res : L_u),
    mappend_rel ⌊ ds_d3ZN -⌋ ⌊ ys -⌋ mappend_res
    ∧ ∃ (mappend_res_2 : L_u),
      mappend_rel mappend_res ⌊ zs -⌋ mappend_res_2
      ∧ ∃ (mappend_res_3 : L_u),
        mappend_rel ⌊ ys -⌋ ⌊ zs -⌋ mappend_res_3
        ∧ ∃ (mappend_res_4 : L_u),
          mappend_rel ⌊ ds_d3ZN -⌋ mappend_res_3 mappend_res_4 ∧ mappend_res_2 == mappend_res_4}}.

#[global] Hint Unfold mappend_assoc_spec: lia_unfold.

Theorem mappend_assoc (ds_d3ZN ys zs : L): mappend_assoc_spec ds_d3ZN ys zs.
Proof.
  destruct ds_d3ZN as [ds_d3ZN ds_d3ZN_p].
  destruct ys as [ys ys_p].
  destruct zs as [zs zs_p].
  try revert zs_p; generalize dependent zs; try revert ys_p; generalize dependent ys;
  induction ds_d3ZN as [x xs IH_xs|];
  intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (mappend_res : L_u),
             mappend_rel (C_u x xs) ys mappend_res
             ∧ ∃ (mappend_res_2 : L_u),
               mappend_rel mappend_res zs mappend_res_2
               ∧ ∃ (mappend_res_3 : L_u),
                 mappend_rel ys zs mappend_res_3
                 ∧ ∃ (mappend_res_4 : L_u),
                   mappend_rel (C_u x xs) mappend_res_3 mappend_res_4 ∧ mappend_res_2 == mappend_res_4)
            (IH_xs
             ltac:(try clear IH_xs; solver)
             ys
             ltac:(try clear IH_xs; solver)
             zs
             ltac:(try clear IH_xs; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (mappend_res : L_u),
             mappend_rel Emp_u ys mappend_res
             ∧ ∃ (mappend_res_2 : L_u),
               mappend_rel mappend_res zs mappend_res_2
               ∧ ∃ (mappend_res_3 : L_u),
                 mappend_rel ys zs mappend_res_3
                 ∧ ∃ (mappend_res_4 : L_u),
                   mappend_rel Emp_u mappend_res_3 mappend_res_4 ∧ mappend_res_2 == mappend_res_4)
            (# unit)
            ltac:(solver)).
Qed.

Definition mempty_spec : Type :=
  L.

#[global] Hint Unfold mempty_spec: lia_unfold.

Definition mempty : mempty_spec.
Proof.
  refine Emp.
Defined.

Definition mempty_left_spec (xs : L): Type :=
  {{∃ (mappend_res : L_u), mappend_rel ⌊ mempty -⌋ ⌊ xs -⌋ mappend_res ∧ mappend_res == ⌊ xs -⌋}}.

#[global] Hint Unfold mempty_left_spec: lia_unfold.

Theorem mempty_left (xs : L): mempty_left_spec xs.
Proof.
  destruct xs as [xs xs_p].
  refine (subsumptionCast
          Unit
          (λ (VV : Unit), ∃ (mappend_res : L_u), mappend_rel ⌊ mempty -⌋ xs mappend_res ∧ mappend_res == xs)
          (# unit)
          ltac:(solver)).
Qed.

Definition mempty_right_spec (ds_d3ZO : L): Type :=
  {{∃ (mappend_res : L_u),
    mappend_rel ⌊ ds_d3ZO -⌋ ⌊ mempty -⌋ mappend_res ∧ mappend_res == ⌊ ds_d3ZO -⌋}}.

#[global] Hint Unfold mempty_right_spec: lia_unfold.

Theorem mempty_right (ds_d3ZO : L): mempty_right_spec ds_d3ZO.
Proof.
  destruct ds_d3ZO as [ds_d3ZO ds_d3ZO_p].
  induction ds_d3ZO as [x xs IH_xs|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (mappend_res : L_u), mappend_rel (C_u x xs) ⌊ mempty -⌋ mappend_res ∧ mappend_res == C_u x xs)
            (IH_xs ltac:(try clear IH_xs; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (mappend_res : L_u), mappend_rel Emp_u ⌊ mempty -⌋ mappend_res ∧ mappend_res == Emp_u)
            (# unit)
            ltac:(solver)).
Qed.
