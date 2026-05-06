From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Set Universe Polymorphism.
From Coq Require Import Unicode.Utf8.
Ltac solver := quicksolve.

Inductive L_u: Set :=
  | C_u: Z → L_u → L_u | Emp_u: L_u.

Fixpoint L_eq (x y : L_u): bool :=
  match (x, y) with
  | (C_u VV VV_, C_u VV' VV_') => (true && (VV ==? VV')) && L_eq VV_ VV_'
  | (Emp_u, Emp_u) => true
  | (_, _) => false
  end.

Definition L_eq_refl : ∀ (x : L_u), is_true (L_eq x x).
Proof.
  eq_refl_rec.
Qed.

#[global] Hint Resolve L_eq_refl: eq_hint_db.

Definition L_eqb_eq : ∀ (s t : L_u), is_true (L_eq s t) → s = t.
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

Theorem L_wf_ref [p : L_u → Prop] (tm : {v: L_u | L_wf v ∧ p v}): L_wf ⌊ tm ⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation L := {x: L_u | L_wf x ∧ True}.

Definition C_lem (VV : {VV: Z | True}) (VV_ : L): L_wf (C_u ⌊ VV ⌋ ⌊ VV_ ⌋) ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition C (VV : {VV: Z | True}) (VV_ : L): L :=
  exist _ (C_u ⌊ VV ⌋ ⌊ VV_ ⌋) (C_lem VV VV_).

Definition Emp_lem : L_wf Emp_u ∧ True.
Proof.
  repeat first [split; solver].
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

Definition mappend (lq_tmp0 lq_tmp1 : L): L.
Proof.
  destruct lq_tmp0 as [lq_tmp0 lq_tmp0_p].
  destruct lq_tmp1 as [lq_tmp1 lq_tmp1_p].
  try revert lq_tmp1_p; generalize dependent lq_tmp1; induction lq_tmp0 as [x xs IH_xs|]; intros.
  - refine (C (# x) (IH_xs ltac:(try clear IH_xs; solver) lq_tmp1 ltac:(try clear IH_xs; solver))).
  - refine (exist (λ (lq_tmp1 : L_u), L_wf lq_tmp1 ∧ True) lq_tmp1 ltac:(solver)).
Defined.

Inductive mappend_rel: L_u → L_u → L_u → Prop :=
  | mappend_Emp_x: ∀ lq_tmp1, mappend_rel Emp_u lq_tmp1 lq_tmp1
  | mappend_C_x: ∀ x xs lq_tmp1 mappend_res,
                 mappend_rel xs lq_tmp1 mappend_res → mappend_rel (C_u x xs) lq_tmp1 (C_u x mappend_res).

#[global] Hint Constructors mappend_rel: core_hint_db.

#[global] Instance mappend_lookup_rel: dictionary rel mappend := { lookup' := mappend_rel }.

#[global] Instance mappend_getF: getFunc mappend_rel := { getF' := mappend }.

Definition mappend_rel_funct [lq_tmp0 lq_tmp1 : L_u]:
  ∀ (VV VV' : L_u), mappend_rel lq_tmp0 lq_tmp1 VV → (mappend_rel lq_tmp0 lq_tmp1 VV' → VV = VV').
Proof.
  try revert lq_tmp1_p; generalize dependent lq_tmp1; induction lq_tmp0 as [x xs IH_xs|]; intros;
  rel_functionhood_body.
Qed.

#[global] Hint Resolve mappend_rel_funct: f_rel_funct_db.

Theorem mappend_Emp_x_lem lq_tmp1 mappend_Emp_x_lem_res:
  mappend_rel Emp_u lq_tmp1 mappend_Emp_x_lem_res ↔ mappend_Emp_x_lem_res == lq_tmp1.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite mappend_Emp_x_lem: f_rel_back.

Theorem mappend_C_x_lem lq_tmp1 x xs mappend_C_x_lem_res:
  mappend_rel (C_u x xs) lq_tmp1 mappend_C_x_lem_res
  ↔ ∃ mappend_res, mappend_rel xs lq_tmp1 mappend_res ∧ mappend_C_x_lem_res == C_u x mappend_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite mappend_C_x_lem: f_rel_back.

Theorem mappend_rel_ex
  (lq_tmp0 : L_u) (lq_tmp0_p : L_wf lq_tmp0 ∧ True) (lq_tmp1 : L_u) (lq_tmp1_p : L_wf lq_tmp1 ∧ True):
  mappend_rel lq_tmp0 lq_tmp1 ⌊ mappend (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p) ⌋.
Proof.
  existence_lemma_pre mappend;
  try revert lq_tmp1_p; generalize dependent lq_tmp1; induction lq_tmp0 as [x xs IH_xs|]; intros;
  [fix_notations | fix_notations];
  existence_lemma_quicksolve mappend;
  f__f_rel_ex_body;
  f_rel_finish.
Qed.

#[global] Hint Resolve mappend_rel_ex: rel_ax_db.

Opaque mappend.

Theorem mappend__mappend_rel_rw
  (lq_tmp0 : L_u)
  (lq_tmp0_p : L_wf lq_tmp0 ∧ True)
  (lq_tmp1 : L_u)
  (lq_tmp1_p : L_wf lq_tmp1 ∧ True)
  (VV : L_u):
  ⌊ mappend (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p) ⌋ = VV
  ↔ mappend_rel lq_tmp0 lq_tmp1 VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite mappend__mappend_rel_rw: f_rel_funct_db.

#[global] Hint Resolve mappend__mappend_rel_rw: rel_ax_db.

#[global] Instance mappend_lookup_rw: dictionary rwLem mappend := {
    lookup' := mappend__mappend_rel_rw }.

Theorem mappend__mappend_rel (lq_tmp0 lq_tmp1 : L) (VV : L_u):
  ⌊ mappend lq_tmp0 lq_tmp1 ⌋ = VV ↔ mappend_rel ⌊ lq_tmp0 ⌋ ⌊ lq_tmp1 ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite mappend__mappend_rel: f_rel_funct_db.

Theorem mappend__mappend_rel' (lq_tmp0_u lq_tmp1_u : L_u) (lq_tmp0 lq_tmp1 : L) (VV : L_u):
  lq_tmp0_u = ⌊ lq_tmp0 ⌋
  → (lq_tmp1_u = ⌊ lq_tmp1 ⌋ → ⌊ mappend lq_tmp0 lq_tmp1 ⌋ = VV ↔ mappend_rel lq_tmp0_u lq_tmp1_u VV).
Proof.
  intros -> ->. refine (mappend__mappend_rel lq_tmp0 lq_tmp1 VV).
Qed.

#[global] Hint Resolve mappend__mappend_rel': f_rel_funct_db.

Definition mappend_rel_mk
  (lq_tmp0 : L_u) (lq_tmp0_p : L_wf lq_tmp0 ∧ True) (lq_tmp1 : L_u) (lq_tmp1_p : L_wf lq_tmp1 ∧ True):
  {VV: _ | mappend_rel lq_tmp0 lq_tmp1 VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, mappend_rel lq_tmp0 lq_tmp1 VV)
          (mappend (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p))
          _);
  rewrite <- mappend__mappend_rel';
  quicksolve.
Qed.

#[global] Hint Resolve mappend_rel_mk: f_rel_funct_db.

#[global] Instance mappend_pack:
  @Pack
  (L ::RT λ (lq_tmp0 : L), L ::RT λ (lq_tmp1 : L), nilRT)
  (L_u ::UT (L_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((L ::RT λ (lq_tmp0 : L), L ::RT λ (lq_tmp1 : L), nilRT)) ((L_u ::UT (L_u ::UT nilUT))))
  L_u
  (λ (x_59358093 : ArgList (L ::RT λ (lq_tmp0 : L), L ::RT λ (lq_tmp1 : L), nilRT))
     (v_x_59358093 : L_u),
   ltac:(flattenP (λ (lq_tmp0 lq_tmp1 : L) (VV : L_u), L_wf VV ∧ True) x_59358093 v_x_59358093)).
Proof.
  buildPackG mappend mappend_rel mappend__mappend_rel mappend_rel_funct.
Defined.

#[global] Instance mappend_upack: @uPack (L_u ::UT (L_u ::UT nilUT)) L_u.
Proof.
  buildUPackG mappend_rel mappend_rel_funct.
Defined.

Definition mappend_assoc (xs ys zs : L):
  {{∀ mappend_res,
    mappend_rel ⌊ xs ⌋ ⌊ ys ⌋ mappend_res
    → ∀ mappend_res_2,
      mappend_rel mappend_res ⌊ zs ⌋ mappend_res_2
      → ∀ mappend_res_3,
        mappend_rel ⌊ ys ⌋ ⌊ zs ⌋ mappend_res_3
        → ∀ mappend_res_4,
          mappend_rel ⌊ xs ⌋ mappend_res_3 mappend_res_4 → mappend_res_2 == mappend_res_4}}.
Proof.
  destruct xs as [xs xs_p].
  destruct ys as [ys ys_p].
  destruct zs as [zs zs_p].
  try revert zs_p; generalize dependent zs; try revert ys_p; generalize dependent ys;
  induction xs as [x xs IH_xs|];
  intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∀ mappend_res,
             mappend_rel ⌊ xs ⌋ ⌊ ys ⌋ mappend_res
             → ∀ mappend_res_2,
               mappend_rel mappend_res ⌊ zs ⌋ mappend_res_2
               → ∀ mappend_res_3,
                 mappend_rel ⌊ ys ⌋ ⌊ zs ⌋ mappend_res_3
                 → ∀ mappend_res_4, mappend_rel ⌊ xs ⌋ mappend_res_3 mappend_res_4 → mappend_res_2 == mappend_res_4)
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
             ∀ mappend_res,
             mappend_rel ⌊ xs ⌋ ⌊ ys ⌋ mappend_res
             → ∀ mappend_res_2,
               mappend_rel mappend_res ⌊ zs ⌋ mappend_res_2
               → ∀ mappend_res_3,
                 mappend_rel ⌊ ys ⌋ ⌊ zs ⌋ mappend_res_3
                 → ∀ mappend_res_4, mappend_rel ⌊ xs ⌋ mappend_res_3 mappend_res_4 → mappend_res_2 == mappend_res_4)
            (# unit)
            ltac:(solver)).
Defined.

Definition mempty : L.
Proof.
  refine Emp.
Defined.

Inductive mempty_rel: L_u → Prop :=
  | mempty_Constr: mempty_rel Emp_u.

#[global] Hint Constructors mempty_rel: core_hint_db.

#[global] Instance mempty_lookup_rel: dictionary rel mempty := { lookup' := mempty_rel }.

#[global] Instance mempty_getF: getFunc mempty_rel := { getF' := mempty }.

Definition mempty_rel_funct : ∀ (VV VV' : L_u), mempty_rel VV → (mempty_rel VV' → VV = VV').
Proof.
  rel_functionhood_body.
Qed.

#[global] Hint Resolve mempty_rel_funct: f_rel_funct_db.

Theorem mempty_inv_lem mempty_inv_lem_res:
  mempty_rel mempty_inv_lem_res ↔ mempty_inv_lem_res == Emp_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite mempty_inv_lem: f_rel_back.

Theorem mempty_rel_ex : mempty_rel ⌊ mempty ⌋.
Proof.
  existence_lemma_pre mempty;
  fix_notations;
  existence_lemma_quicksolve mempty;
  f__f_rel_ex_body;
  f_rel_finish.
Qed.

#[global] Hint Resolve mempty_rel_ex: rel_ax_db.

Opaque mempty.

Theorem mempty__mempty_rel_rw (VV : L_u): ⌊ mempty ⌋ = VV ↔ mempty_rel VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite mempty__mempty_rel_rw: f_rel_funct_db.

#[global] Hint Resolve mempty__mempty_rel_rw: rel_ax_db.

#[global] Instance mempty_lookup_rw: dictionary rwLem mempty := {
    lookup' := mempty__mempty_rel_rw }.

Theorem mempty__mempty_rel (VV : L_u): ⌊ mempty ⌋ = VV ↔ mempty_rel VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite mempty__mempty_rel: f_rel_funct_db.

Theorem mempty__mempty_rel' (VV : L_u): ⌊ mempty ⌋ = VV ↔ mempty_rel VV.
Proof.
  intros. refine (mempty__mempty_rel VV).
Qed.

#[global] Hint Resolve mempty__mempty_rel': f_rel_funct_db.

Definition mempty_rel_mk : {VV: _ | mempty_rel VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, mempty_rel VV) mempty _);
  rewrite <- mempty__mempty_rel';
  quicksolve.
Qed.

#[global] Hint Resolve mempty_rel_mk: f_rel_funct_db.

Definition mempty_left (x : L):
  {{∀ mempty_res,
    mempty_rel mempty_res
    → ∀ mappend_res, mappend_rel mempty_res ⌊ x ⌋ mappend_res → mappend_res == ⌊ x ⌋}}.
Proof.
  destruct x as [x x_p].
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∀ mempty_res,
           mempty_rel mempty_res
           → ∀ mappend_res, mappend_rel mempty_res ⌊ x ⌋ mappend_res → mappend_res == ⌊ x ⌋)
          (# unit)
          ltac:(solver)).
Defined.

Definition mempty_right (x : L):
  {{∀ mempty_res,
    mempty_rel mempty_res
    → ∀ mappend_res, mappend_rel ⌊ x ⌋ mempty_res mappend_res → mappend_res == ⌊ x ⌋}}.
Proof.
  destruct x as [x x_p].
  induction x as [x xs IH_xs|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∀ mempty_res,
             mempty_rel mempty_res
             → ∀ mappend_res, mappend_rel ⌊ x ⌋ mempty_res mappend_res → mappend_res == ⌊ x ⌋)
            (IH_xs ltac:(try clear IH_xs; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∀ mempty_res,
             mempty_rel mempty_res
             → ∀ mappend_res, mappend_rel ⌊ x ⌋ mempty_res mappend_res → mappend_res == ⌊ x ⌋)
            (# unit)
            ltac:(solver)).
Defined.
