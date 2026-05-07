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

Definition append_spec (lq_tmp0 lq_tmp1 : L): Type :=
  L.

#[global] Hint Unfold append_spec: lia_unfold.

Definition append (lq_tmp0 lq_tmp1 : L): append_spec lq_tmp0 lq_tmp1.
Proof.
  destruct lq_tmp0 as [lq_tmp0 lq_tmp0_p].
  destruct lq_tmp1 as [lq_tmp1 lq_tmp1_p].
  try revert lq_tmp1_p; generalize dependent lq_tmp1; induction lq_tmp0 as [x xs IH_xs|]; intros.
  - refine (C (# x) (IH_xs ltac:(try clear IH_xs; solver) lq_tmp1 ltac:(try clear IH_xs; solver))).
  - refine (exist (λ (lq_tmp1 : L_u), L_wf lq_tmp1 ∧ True) lq_tmp1 ltac:(solver)).
Defined.

Inductive append_rel: L_u → L_u → L_u → Prop :=
  | append_Emp_x: ∀ lq_tmp1, append_rel Emp_u lq_tmp1 lq_tmp1
  | append_C_x: ∀ x xs lq_tmp1 append_res,
                append_rel xs lq_tmp1 append_res → append_rel (C_u x xs) lq_tmp1 (C_u x append_res).

#[global] Hint Constructors append_rel: core_hint_db.

#[global] Instance append_lookup_rel: dictionary rel append := { lookup' := append_rel }.

#[global] Instance append_getF: getFunc append_rel := { getF' := append }.

Theorem append_rel_funct [lq_tmp0 lq_tmp1 : L_u]:
  ∀ (VV VV' : L_u), append_rel lq_tmp0 lq_tmp1 VV → (append_rel lq_tmp0 lq_tmp1 VV' → VV = VV').
Proof.
  try revert lq_tmp1_p; generalize dependent lq_tmp1; induction lq_tmp0 as [x xs IH_xs|]; intros;
  rel_functionhood_body.
Qed.

#[global] Hint Resolve append_rel_funct: f_rel_funct_db.

Theorem append_Emp_x_lem lq_tmp1 append_Emp_x_lem_res:
  append_rel Emp_u lq_tmp1 append_Emp_x_lem_res ↔ append_Emp_x_lem_res == lq_tmp1.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite append_Emp_x_lem: f_rel_back.

Theorem append_C_x_lem lq_tmp1 x xs append_C_x_lem_res:
  append_rel (C_u x xs) lq_tmp1 append_C_x_lem_res
  ↔ ∃ append_res, append_rel xs lq_tmp1 append_res ∧ append_C_x_lem_res == C_u x append_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite append_C_x_lem: f_rel_back.

Theorem append_rel_ex
  (lq_tmp0 : L_u) (lq_tmp0_p : L_wf lq_tmp0 ∧ True) (lq_tmp1 : L_u) (lq_tmp1_p : L_wf lq_tmp1 ∧ True):
  append_rel lq_tmp0 lq_tmp1 ⌊ append (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p) ⌋.
Proof.
  Opaque append.
  existence_lemma_pre append;
  try revert lq_tmp1_p; generalize dependent lq_tmp1; induction lq_tmp0 as [x xs IH_xs|]; intros;
  [fix_notations | fix_notations];
  simpl in *.
  Transparent append.
  all: existence_lemma_quicksolve append; f__f_rel_ex_body; f_rel_finish.
Qed.

#[global] Hint Resolve append_rel_ex: rel_ax_db.

#[global] Opaque append.

Theorem append__append_rel_rw
  (lq_tmp0 : L_u)
  (lq_tmp0_p : L_wf lq_tmp0 ∧ True)
  (lq_tmp1 : L_u)
  (lq_tmp1_p : L_wf lq_tmp1 ∧ True)
  (VV : L_u):
  ⌊ append (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p) ⌋ = VV
  ↔ append_rel lq_tmp0 lq_tmp1 VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite append__append_rel_rw: f_rel_funct_db.

#[global] Hint Resolve append__append_rel_rw: rel_ax_db.

#[global] Instance append_lookup_rw: dictionary rwLem append := {
    lookup' := append__append_rel_rw }.

Theorem append__append_rel (lq_tmp0 lq_tmp1 : L) (VV : L_u):
  ⌊ append lq_tmp0 lq_tmp1 ⌋ = VV ↔ append_rel ⌊ lq_tmp0 ⌋ ⌊ lq_tmp1 ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite append__append_rel: f_rel_funct_db.

Theorem append__append_rel' (lq_tmp0_u lq_tmp1_u : L_u) (lq_tmp0 lq_tmp1 : L) (VV : L_u):
  lq_tmp0_u = ⌊ lq_tmp0 ⌋
  → (lq_tmp1_u = ⌊ lq_tmp1 ⌋ → ⌊ append lq_tmp0 lq_tmp1 ⌋ = VV ↔ append_rel lq_tmp0_u lq_tmp1_u VV).
Proof.
  intros -> ->. refine (append__append_rel lq_tmp0 lq_tmp1 VV).
Qed.

#[global] Hint Resolve append__append_rel': f_rel_funct_db.

Theorem append_rel_mk
  (lq_tmp0 : L_u) (lq_tmp0_p : L_wf lq_tmp0 ∧ True) (lq_tmp1 : L_u) (lq_tmp1_p : L_wf lq_tmp1 ∧ True):
  {VV: _ | append_rel lq_tmp0 lq_tmp1 VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, append_rel lq_tmp0 lq_tmp1 VV)
          (append (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p))
          _);
  rewrite <- append__append_rel';
  quicksolve.
Qed.

#[global] Hint Resolve append_rel_mk: f_rel_funct_db.

#[global] Instance append_pack:
  @Pack
  (L ::RT λ (lq_tmp0 : L), L ::RT λ (lq_tmp1 : L), nilRT)
  (L_u ::UT (L_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((L ::RT λ (lq_tmp0 : L), L ::RT λ (lq_tmp1 : L), nilRT)) ((L_u ::UT (L_u ::UT nilUT))))
  L_u
  (λ (x_59358093 : ArgList (L ::RT λ (lq_tmp0 : L), L ::RT λ (lq_tmp1 : L), nilRT))
     (v_x_59358093 : L_u),
   ltac:(flattenP (λ (lq_tmp0 lq_tmp1 : L) (VV : L_u), L_wf VV ∧ True) x_59358093 v_x_59358093)).
Proof.
  buildPackG append append_rel append__append_rel append_rel_funct.
Defined.

#[global] Instance append_upack: @uPack (L_u ::UT (L_u ::UT nilUT)) L_u.
Proof.
  buildUPackG append_rel append_rel_funct.
Defined.

Definition bind_spec
  (lq_tmp0 : L)
  (lq_tmp2 : @Pack
             ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
             L_u
             (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
                (v_x_10329927 : L_u),
              ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : L_u), L_wf VV ∧ True) x_10329927 v_x_10329927))):
  Type :=
  L.

#[global] Hint Unfold bind_spec: lia_unfold.

Definition bind
  (lq_tmp0 : L)
  (lq_tmp2 : @Pack
             ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
             L_u
             (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
                (v_x_10329927 : L_u),
              ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : L_u), L_wf VV ∧ True) x_10329927 v_x_10329927))):
  bind_spec lq_tmp0 lq_tmp2.
Proof.
  destruct lq_tmp0 as [lq_tmp0 lq_tmp0_p].
  try revert lq_tmp2_p; generalize dependent lq_tmp2; induction lq_tmp0 as [x xs IH_xs|]; intros.
  - refine (append (getPackF lq_tmp2 (# x)) (IH_xs ltac:(try clear IH_xs; solver) lq_tmp2)).
  - refine Emp.
Defined.

Inductive bind_rel: L_u → @uPack (Z ::UT nilUT) L_u → L_u → Prop :=
  | bind_Emp_x: ∀ (lq_tmp2 : @uPack (Z ::UT nilUT) L_u), bind_rel Emp_u lq_tmp2 Emp_u
  | bind_C_x: ∀ x xs (lq_tmp2 : @uPack (Z ::UT nilUT) L_u) bind_res,
              bind_rel xs lq_tmp2 bind_res
              → ∀ lq_tmp2_res,
                getUPackRel lq_tmp2 x lq_tmp2_res
                → ∀ append_res,
                  append_rel lq_tmp2_res bind_res append_res → bind_rel (C_u x xs) lq_tmp2 append_res.

#[global] Hint Constructors bind_rel: core_hint_db.

#[global] Instance bind_lookup_rel: dictionary rel bind := { lookup' := bind_rel }.

#[global] Instance bind_getF: getFunc bind_rel := { getF' := bind }.

Theorem bind_rel_funct [lq_tmp0 : L_u] [lq_tmp2 : @uPack (Z ::UT nilUT) L_u]:
  ∀ (VV VV' : L_u), bind_rel lq_tmp0 lq_tmp2 VV → (bind_rel lq_tmp0 lq_tmp2 VV' → VV = VV').
Proof.
  try revert lq_tmp2_p; generalize dependent lq_tmp2; induction lq_tmp0 as [x xs IH_xs|]; intros;
  rel_functionhood_body.
Qed.

#[global] Hint Resolve bind_rel_funct: f_rel_funct_db.

Theorem bind_Emp_x_lem lq_tmp2 bind_Emp_x_lem_res:
  bind_rel Emp_u lq_tmp2 bind_Emp_x_lem_res ↔ bind_Emp_x_lem_res == Emp_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite bind_Emp_x_lem: f_rel_back.

Theorem bind_C_x_lem lq_tmp2 x xs bind_C_x_lem_res:
  bind_rel (C_u x xs) lq_tmp2 bind_C_x_lem_res
  ↔ ∃ bind_res,
    bind_rel xs lq_tmp2 bind_res
    ∧ ∃ lq_tmp2_res,
      getUPackRel lq_tmp2 x lq_tmp2_res
      ∧ ∃ append_res, append_rel lq_tmp2_res bind_res append_res ∧ bind_C_x_lem_res == append_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite bind_C_x_lem: f_rel_back.

Theorem bind_rel_ex
  (lq_tmp0 : L_u)
  (lq_tmp0_p : L_wf lq_tmp0 ∧ True)
  (lq_tmp2 : @Pack
             ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
             L_u
             (λ (x_82647028 : ArgList ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
                (v_x_82647028 : L_u),
              ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : L_u), L_wf VV ∧ True) x_82647028 v_x_82647028))):
  bind_rel lq_tmp0 ⌊ lq_tmp2 ⌋ ⌊ bind (exist _ lq_tmp0 lq_tmp0_p) lq_tmp2 ⌋.
Proof.
  Opaque bind.
  existence_lemma_pre bind;
  try revert lq_tmp2_p; generalize dependent lq_tmp2; induction lq_tmp0 as [x xs IH_xs|]; intros;
  [fix_notations | fix_notations];
  simpl in *.
  Transparent bind.
  all: existence_lemma_quicksolve bind; f__f_rel_ex_body; f_rel_finish.
Qed.

#[global] Hint Resolve bind_rel_ex: rel_ax_db.

#[global] Opaque bind.

Theorem bind__bind_rel_rw
  (lq_tmp0 : L_u)
  (lq_tmp0_p : L_wf lq_tmp0 ∧ True)
  (lq_tmp2 : @Pack
             ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
             L_u
             (λ (x_82647028 : ArgList ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
                (v_x_82647028 : L_u),
              ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : L_u), L_wf VV ∧ True) x_82647028 v_x_82647028)))
  (VV : L_u):
  ⌊ bind (exist _ lq_tmp0 lq_tmp0_p) lq_tmp2 ⌋ = VV ↔ bind_rel lq_tmp0 ⌊ lq_tmp2 ⌋ VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite bind__bind_rel_rw: f_rel_funct_db.

#[global] Hint Resolve bind__bind_rel_rw: rel_ax_db.

#[global] Instance bind_lookup_rw: dictionary rwLem bind := { lookup' := bind__bind_rel_rw }.

Theorem bind__bind_rel
  (lq_tmp0 : L)
  (lq_tmp2 : @Pack
             ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
             L_u
             (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
                (v_x_10329927 : L_u),
              ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : L_u), L_wf VV ∧ True) x_10329927 v_x_10329927)))
  (VV : L_u):
  ⌊ bind lq_tmp0 lq_tmp2 ⌋ = VV ↔ bind_rel ⌊ lq_tmp0 ⌋ ⌊ lq_tmp2 ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite bind__bind_rel: f_rel_funct_db.

Theorem bind__bind_rel'
  (lq_tmp0_u : L_u)
  (lq_tmp2_u : @uPack (Z ::UT nilUT) L_u)
  (lq_tmp0 : L)
  (lq_tmp2 : @Pack
             ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
             L_u
             (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
                (v_x_10329927 : L_u),
              ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : L_u), L_wf VV ∧ True) x_10329927 v_x_10329927)))
  (VV : L_u):
  lq_tmp0_u = ⌊ lq_tmp0 ⌋
  → (lq_tmp2_u = ⌊ lq_tmp2 ⌋ → ⌊ bind lq_tmp0 lq_tmp2 ⌋ = VV ↔ bind_rel lq_tmp0_u lq_tmp2_u VV).
Proof.
  intros -> ->. refine (bind__bind_rel lq_tmp0 lq_tmp2 VV).
Qed.

#[global] Hint Resolve bind__bind_rel': f_rel_funct_db.

Theorem bind_rel_mk
  (lq_tmp0 : L_u)
  (lq_tmp0_p : L_wf lq_tmp0 ∧ True)
  (lq_tmp2 : @Pack
             ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
             L_u
             (λ (x_82647028 : ArgList ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
                (v_x_82647028 : L_u),
              ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : L_u), L_wf VV ∧ True) x_82647028 v_x_82647028))):
  {VV: _ | bind_rel lq_tmp0 (packProj lq_tmp2) VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, bind_rel lq_tmp0 (packProj lq_tmp2) VV)
          (bind (exist _ lq_tmp0 lq_tmp0_p) lq_tmp2)
          _);
  rewrite <- bind__bind_rel';
  quicksolve.
Qed.

#[global] Hint Resolve bind_rel_mk: f_rel_funct_db.

Definition prop_append_neutral_spec (xs : L): Type :=
  {{∃ append_res, append_rel ⌊ xs ⌋ Emp_u append_res ∧ append_res == ⌊ xs ⌋}}.

#[global] Hint Unfold prop_append_neutral_spec: lia_unfold.

Theorem prop_append_neutral (xs : L): prop_append_neutral_spec xs.
Proof.
  destruct xs as [xs xs_p].
  induction xs as [x xs IH_xs|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ append_res, append_rel ⌊ xs ⌋ Emp_u append_res ∧ append_res == ⌊ xs ⌋)
            (IH_xs ltac:(try clear IH_xs; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ append_res, append_rel ⌊ xs ⌋ Emp_u append_res ∧ append_res == ⌊ xs ⌋)
            (# unit)
            ltac:(solver)).
Qed.

Definition retrn_spec (lq_tmp0 : {lq_tmp0: Z | True}): Type :=
  L.

#[global] Hint Unfold retrn_spec: lia_unfold.

Definition retrn (lq_tmp0 : {lq_tmp0: Z | True}): retrn_spec lq_tmp0.
Proof.
  destruct lq_tmp0 as [lq_tmp0 lq_tmp0_p]. refine (C (# lq_tmp0) Emp).
Defined.

Inductive retrn_rel: Z → L_u → Prop :=
  | retrn_Constr: ∀ lq_tmp0, retrn_rel lq_tmp0 (C_u lq_tmp0 Emp_u).

#[global] Hint Constructors retrn_rel: core_hint_db.

#[global] Instance retrn_lookup_rel: dictionary rel retrn := { lookup' := retrn_rel }.

#[global] Instance retrn_getF: getFunc retrn_rel := { getF' := retrn }.

Theorem retrn_rel_funct [lq_tmp0 : Z]:
  ∀ (VV VV' : L_u), retrn_rel lq_tmp0 VV → (retrn_rel lq_tmp0 VV' → VV = VV').
Proof.
  rel_functionhood_body.
Qed.

#[global] Hint Resolve retrn_rel_funct: f_rel_funct_db.

Theorem retrn_inv_lem lq_tmp0 retrn_inv_lem_res:
  retrn_rel lq_tmp0 retrn_inv_lem_res ↔ retrn_inv_lem_res == C_u lq_tmp0 Emp_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite retrn_inv_lem: f_rel_back.

Theorem retrn_rel_ex (lq_tmp0 : Z) (lq_tmp0_p : True):
  retrn_rel lq_tmp0 ⌊ retrn (exist _ lq_tmp0 lq_tmp0_p) ⌋.
Proof.
  Opaque retrn.
  existence_lemma_pre retrn; fix_notations; simpl in *.
  Transparent retrn.
  all: existence_lemma_quicksolve retrn; f__f_rel_ex_body; f_rel_finish.
Qed.

#[global] Hint Resolve retrn_rel_ex: rel_ax_db.

#[global] Opaque retrn.

Theorem retrn__retrn_rel_rw (lq_tmp0 : Z) (lq_tmp0_p : True) (VV : L_u):
  ⌊ retrn (exist _ lq_tmp0 lq_tmp0_p) ⌋ = VV ↔ retrn_rel lq_tmp0 VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite retrn__retrn_rel_rw: f_rel_funct_db.

#[global] Hint Resolve retrn__retrn_rel_rw: rel_ax_db.

#[global] Instance retrn_lookup_rw: dictionary rwLem retrn := { lookup' := retrn__retrn_rel_rw }.

Theorem retrn__retrn_rel (lq_tmp0 : {lq_tmp0: Z | True}) (VV : L_u):
  ⌊ retrn lq_tmp0 ⌋ = VV ↔ retrn_rel ⌊ lq_tmp0 ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite retrn__retrn_rel: f_rel_funct_db.

Theorem retrn__retrn_rel' (lq_tmp0_u : Z) (lq_tmp0 : {lq_tmp0: Z | True}) (VV : L_u):
  lq_tmp0_u = ⌊ lq_tmp0 ⌋ → ⌊ retrn lq_tmp0 ⌋ = VV ↔ retrn_rel lq_tmp0_u VV.
Proof.
  intros ->. refine (retrn__retrn_rel lq_tmp0 VV).
Qed.

#[global] Hint Resolve retrn__retrn_rel': f_rel_funct_db.

Theorem retrn_rel_mk (lq_tmp0 : Z) (lq_tmp0_p : True): {VV: _ | retrn_rel lq_tmp0 VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, retrn_rel lq_tmp0 VV) (retrn (exist _ lq_tmp0 lq_tmp0_p)) _);
  rewrite <- retrn__retrn_rel';
  quicksolve.
Qed.

#[global] Hint Resolve retrn_rel_mk: f_rel_funct_db.

#[global] Instance retrn_pack:
  @Pack
  ({lq_tmp0: Z | True} ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT)
  (Z ::UT nilUT)
  ltac:(mkProjectsArgListTG (({lq_tmp0: Z | True}
  ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT)) ((Z ::UT nilUT)))
  L_u
  (λ (x_49697850 : ArgList ({lq_tmp0: Z | True} ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT))
     (v_x_49697850 : L_u),
   ltac:(flattenP (λ (lq_tmp0 : {lq_tmp0: Z | True}) (VV : L_u), L_wf VV ∧ True) x_49697850 v_x_49697850)).
Proof.
  buildPackG retrn retrn_rel retrn__retrn_rel retrn_rel_funct.
Defined.

#[global] Instance retrn_upack: @uPack (Z ::UT nilUT) L_u.
Proof.
  buildUPackG retrn_rel retrn_rel_funct.
Defined.

Definition left_identity_spec
  (x : {x: Z | True})
  (f : @Pack
       ({VV: Z | True} ::RT λ (f : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (f : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       L_u
       (λ (x_46517173 : ArgList ({VV: Z | True} ::RT λ (f : {VV: Z | True}), nilRT)) (v_x_46517173 : L_u),
        ltac:(flattenP (λ (f : {VV: Z | True}) (VV : L_u), L_wf VV ∧ True) x_46517173 v_x_46517173))):
  Type :=
  {{∃ retrn_res,
    retrn_rel ⌊ x ⌋ retrn_res
    ∧ ∃ bind_res,
      bind_rel retrn_res ⌊ f ⌋ bind_res ∧ ∃ f_res, getPackRel f ⌊ x ⌋ f_res ∧ bind_res == f_res}}.

#[global] Hint Unfold left_identity_spec: lia_unfold.

Theorem left_identity
  (x : {x: Z | True})
  (f : @Pack
       ({VV: Z | True} ::RT λ (f : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (f : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       L_u
       (λ (x_46517173 : ArgList ({VV: Z | True} ::RT λ (f : {VV: Z | True}), nilRT)) (v_x_46517173 : L_u),
        ltac:(flattenP (λ (f : {VV: Z | True}) (VV : L_u), L_wf VV ∧ True) x_46517173 v_x_46517173))):
  left_identity_spec x f.
Proof.
  destruct x as [x x_p].
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ retrn_res,
           retrn_rel ⌊ x ⌋ retrn_res
           ∧ ∃ bind_res,
             bind_rel retrn_res ⌊ f ⌋ bind_res ∧ ∃ f_res, getPackRel f ⌊ x ⌋ f_res ∧ bind_res == f_res)
          (prop_append_neutral (getPackF f (# x)))
          ltac:(solver)).
Qed.

Definition right_identity_spec (x : L): Type :=
  {{∃ bind_res, bind_rel ⌊ x ⌋ retrn_upack bind_res ∧ bind_res == ⌊ x ⌋}}.

#[global] Hint Unfold right_identity_spec: lia_unfold.

Theorem right_identity (x : L): right_identity_spec x.
Proof.
  destruct x as [x x_p].
  induction x as [x xs IH_xs|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ bind_res, bind_rel ⌊ x ⌋ retrn_upack bind_res ∧ bind_res == ⌊ x ⌋)
            (IH_xs ltac:(try clear IH_xs; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ bind_res, bind_rel ⌊ x ⌋ retrn_upack bind_res ∧ bind_res == ⌊ x ⌋)
            (# unit)
            ltac:(solver)).
Qed.
