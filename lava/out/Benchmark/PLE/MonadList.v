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
  append_rel lq_tmp0 lq_tmp1 ⌊ append (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p) -⌋.
Proof.
  Opaque append.
  existence_lemma_pre append;
  try revert lq_tmp1_p; generalize dependent lq_tmp1; induction lq_tmp0 as [x xs IH_xs|]; intros;
  [fix_notations;
   pose proof (IH_xs
               ltac:(try clear IH_xs; solver)
               lq_tmp1
               ltac:(try clear IH_xs; solver)) as IH_26846909;
   try clear IH_xs |
   fix_notations];
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
  ⌊ append (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p) -⌋ = VV
  ↔ append_rel lq_tmp0 lq_tmp1 VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite append__append_rel_rw: f_rel_funct_db.

#[global] Hint Resolve append__append_rel_rw: rel_ax_db.

#[global] Instance append_lookup_rw: dictionary rwLem append := {
    lookup' := append__append_rel_rw }.

Theorem append__append_rel (lq_tmp0 lq_tmp1 : L) (VV : L_u):
  ⌊ append lq_tmp0 lq_tmp1 -⌋ = VV ↔ append_rel ⌊ lq_tmp0 ⌋ ⌊ lq_tmp1 ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite append__append_rel: f_rel_funct_db.

Theorem append__append_rel' (lq_tmp0_u lq_tmp1_u : L_u) (lq_tmp0 lq_tmp1 : L) (VV : L_u):
  lq_tmp0_u = ⌊ lq_tmp0 ⌋
  → (lq_tmp1_u = ⌊ lq_tmp1 ⌋ → ⌊ append lq_tmp0 lq_tmp1 -⌋ = VV ↔ append_rel lq_tmp0_u lq_tmp1_u VV).
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
  bind_rel lq_tmp0 ⌊ lq_tmp2 ⌋ ⌊ bind (exist _ lq_tmp0 lq_tmp0_p) lq_tmp2 -⌋.
Proof.
  Opaque bind.
  existence_lemma_pre bind;
  try revert lq_tmp2_p; generalize dependent lq_tmp2; induction lq_tmp0 as [x xs IH_xs|]; intros;
  [fix_notations;
   pose proof (IH_xs ltac:(try clear IH_xs; solver) lq_tmp2) as IH_88514239;
   try clear IH_xs |
   fix_notations];
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
  ⌊ bind (exist _ lq_tmp0 lq_tmp0_p) lq_tmp2 -⌋ = VV ↔ bind_rel lq_tmp0 ⌊ lq_tmp2 ⌋ VV.
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
  ⌊ bind lq_tmp0 lq_tmp2 -⌋ = VV ↔ bind_rel ⌊ lq_tmp0 ⌋ ⌊ lq_tmp2 ⌋ VV.
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
  → (lq_tmp2_u = ⌊ lq_tmp2 ⌋ → ⌊ bind lq_tmp0 lq_tmp2 -⌋ = VV ↔ bind_rel lq_tmp0_u lq_tmp2_u VV).
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
            (λ (VV : Unit), ∃ append_res, append_rel (C_u x xs) Emp_u append_res ∧ append_res == (C_u x xs))
            (IH_xs ltac:(try clear IH_xs; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ append_res, append_rel Emp_u Emp_u append_res ∧ append_res == Emp_u)
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
  retrn_rel lq_tmp0 ⌊ retrn (exist _ lq_tmp0 lq_tmp0_p) -⌋.
Proof.
  Opaque retrn.
  existence_lemma_pre retrn; fix_notations; simpl in *.
  Transparent retrn.
  all: existence_lemma_quicksolve retrn; f__f_rel_ex_body; f_rel_finish.
Qed.

#[global] Hint Resolve retrn_rel_ex: rel_ax_db.

#[global] Opaque retrn.

Theorem retrn__retrn_rel_rw (lq_tmp0 : Z) (lq_tmp0_p : True) (VV : L_u):
  ⌊ retrn (exist _ lq_tmp0 lq_tmp0_p) -⌋ = VV ↔ retrn_rel lq_tmp0 VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite retrn__retrn_rel_rw: f_rel_funct_db.

#[global] Hint Resolve retrn__retrn_rel_rw: rel_ax_db.

#[global] Instance retrn_lookup_rw: dictionary rwLem retrn := { lookup' := retrn__retrn_rel_rw }.

Theorem retrn__retrn_rel (lq_tmp0 : {lq_tmp0: Z | True}) (VV : L_u):
  ⌊ retrn lq_tmp0 -⌋ = VV ↔ retrn_rel ⌊ lq_tmp0 ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite retrn__retrn_rel: f_rel_funct_db.

Theorem retrn__retrn_rel' (lq_tmp0_u : Z) (lq_tmp0 : {lq_tmp0: Z | True}) (VV : L_u):
  lq_tmp0_u = ⌊ lq_tmp0 ⌋ → ⌊ retrn lq_tmp0 -⌋ = VV ↔ retrn_rel lq_tmp0_u VV.
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
           retrn_rel x retrn_res
           ∧ ∃ bind_res,
             bind_rel retrn_res ⌊ f ⌋ bind_res ∧ ∃ f_res, getPackRel f x f_res ∧ bind_res == f_res)
          (prop_append_neutral (getPackF f (# x)))
          _).
  preInstExist.
  repeat instExistGoal.
  try (specialize_hyps; try unify_vars).

  (* forward reasoning *)
  try cleanup_pack_stuff;
  try quick_simple_cleanup_steps;
  repeat reconstruct_ref.
  (* backwards reasoning *)
    (* backwards reasoning in hypotheses *)
    try nonbranching_inversion_specialization.
    (* backwards reasoning in goal *)
    try (unshelve constructor; timeout 3 quicksolve). 
    try (autorewrite with f_rel_back; autorewrite with int_rel_back).
        (* forwards reasoning in goal *)
    try (timeout 60 instExistGoal).

    let vRefl := fresh "vRefl" in
    pose proof (eq_refl lq_tmp2_res) as vRefl.
    let pred := fresh "dom_ref" in
    get_dom_ref append pred;
    (* idtac "get_dom_ref" f dom_ref "returned"; *)

    let wit_name := fresh "wit_" in
    (*assert_wit lq_tmp2_res dom_ref wit_name.*)


    tryif (
    match lq_tmp2_res with
    | ⌊ ?tm -⌋ => pose ⌈ tm ⌉ as wit_name
    end) then idtac else (
    tryif 
      (match goal with
      | [h:_ |- _] => assert (pred lq_tmp2_res) as wit_name by (subst pred; exact h); clear wit_name; pose h as wit_name
      end) then idtac else (
    idtac "assert_wit lq_tmp2_res" pred wit_name;
    match goal with
    | [h: ?f_rel_ap lq_tmp2_res |- _] => idtac h;
      isRelAppl f_rel_ap; idtac h; (* idtac "case in assert_wit for unrefined variable axiomatized using the following application of a graph relation: " f_rel_ap; *)

      (* fetch f and the values ts to which f_rel is applied in f_rel_ap *)
      let f_ts := fresh "f_ts" in
      get_f_ts f_rel_ap f_ts; 
      
      let tempEq := fresh "tempEq" in
      assRefl f_ts as tempEq;
      match type of tempEq with
      | (?f, ?ts) = _ => clear tempEq;
        let fApp := fresh "fApp" in
        let fApp' := fresh "fApp'" in
        let tl := fresh "tsTail" in
        let tlEq := fresh "tsTailEq" in
        pose f as fApp;
        pose ts as tl;
        (* recursively assert the refinements of the ts and apply f to them *)
        repeat (
          assRefl tl as tlEq; 
          match type of tlEq with
          | _nil = _ => fail
          | ?t _::_ ?tail = _ => idtac "running main loop in assert_wit with tail " t " _::_ " tail; 
            pose fApp as fApp'; subst fApp;
            
            let dom_ref := fresh "t_dom_ref" in
            get_dom_ref fApp' dom_ref;
            let arg_wit_name := fresh "arg_wit_name_" in

            first [
              assert_wit t dom_ref arg_wit_name
            | let claim := fresh "claim" in
              let claimRefl := fresh "claimRefl" in
              pose (dom_ref t) as claim;
              assRefl claim as claimRefl; 
              unfold dom_ref in claimRefl; simpl in claimRefl; 
              match type of claimRefl with
              | ?tp = _ => clear claimRefl; idtac tp;
                match tp with
                | (?wf ?x /\ ?p) /\ ?q => 
                  first [
                    assert_wit x (fun x => wf x /\ p /\ q) arg_wit_name
                  | match goal with
                    | [h: ?relAp x |- _] => 
                      isRelAppl relAp; (* idtac "case in assert_wit for unrefined variable axiomatized using the following application of a graph relation: " f_rel_ap; *)

                      (* fetch f and the values ts to which f_rel is applied in f_rel_ap *)
                      let g_ts := fresh "g_ts" in
                      get_f_ts relAp g_ts; 
                      let tempEq := fresh "tempEq" in
                      assRefl g_ts as tempEq;
                      let g := fresh "g" in
                      match type of tempEq with
                      | (?g, ?ts) = _ => clear tempEq;
                        let gdomRef := fresh "gdomRef" in
                        let x_wit := fresh "x_wit_" in
                        get_dom_ref g gdomRef;
                        assert_wit x gdomRef x_wit;
                        assert tp as arg_wit_name by (try split_hyps; try unify_vars; quicksolve)
                      end
                    end
                  ]
                end
              end
            ];
            let arg_wit_tp := type of arg_wit_name in
            (* idtac "recursive call created witness " arg_wit_name " : " arg_wit_tp ". "; *)
            pose (fApp' (exist _ t arg_wit_name)) as fApp;
            try subst arg_wit_name; subst fApp'; simpl_proj;
            pose tail as tl
          end; clear tlEq
        ); idtac "finish main loop"; clear tl;
        (* we now have a fully applied version of f in fApp, we destruct it to get the refinement witness for it *)
        let appl_wit := fresh "appl_wit_" in
        pose proof (⌈ fApp ⌉) as appl_wit; subst fApp; simpl_proj; 
        
        let fApplTp := type of appl_wit in
        try axProjTm fApplTp;
        (* tryif destruct fApp as [_ appl_wit] then idtac else idtac "failed to extract the refinement witness from " fApp; *)
        match type of h with
        | f_rel_ap ?w => 
        assert (pred w) as wit_name by (unfold pred; simpl; try 
          first [clear pred | subst pred]; first [exact appl_wit; clear appl_wit | quick_wff_wit | 
            quick_simpl; unify_vars; try split_hyps; try (specialize_hyps; try unify_vars); try quicksolve; (*print_proof_state;*) timeout 10 (unshelve eauto 50 with solver_db)])
        end
      end
    end)); subst pred; try simpl in wit_name.

    match type of vRefl with
    | ?w = _ => clear vRefl;
    (* idtac "assert_wit" v dom_ref wit_name "returned"; *)
      pose (Res := (f (exist _ w wit_name))); try subst wit_name (*; simpl_proj*)
    end 

    let app1 := fresh "app1" in
    let wff_lem := fresh "wit_" in
    mk_ref_arg append lq_tmp2_res wff_lem app1.
    mkRefAppl append (lq_tmp2_res _::_ Emp_u _::_ _nil) res.
    recreate_var (append_rel lq_tmp2_res Emp_u) append_res'.
    match goal with
    | [ h: ?relAp ?w |- ?rel ?s ?t] => isRelAppl relAp;
      tryif (eq_fail s w) then idtac else eq_fail t w;
      non_branching_inversion h
    | [ h: ?relAp ?w |- ?rel ?s ?t] => isRelAppl relAp;
      tryif (eq_fail s w) then idtac else eq_fail t w;
      idtac h ":" relAp w;
      tryif (match goal with
      | [def_rw: ⌊ ?Res -⌋ = w |- _] => idtac
      end
      ) then idtac "no need" else (
        let v' := fresh "v'" in
        recreate_var relAp v'; subst v'
      );
      match goal with
      | [def_rw: ⌊ ?Res -⌋ = ?v |- _] => match goal with
        | [k: relAp v |- _] => 
          assert (v = w) as -> by (now try unify_vars);
          rewrite <- def_rw
        end
      end;
      timeout 30 quicksolve
  end.



try instantiate_goals.
     try quick_simple_cleanup_steps
    )); try simple_cleanup_steps.
  inversion_cleanup.
  solver.

  mkRefAppl bind (v_ _::_ (packPr_proj {| f := f0; frel := frel; f_frel := f_frel; funct := funct |}) _::_ _nil) res.
  mk_ref_arg bind v_ wff_lem temp_.
  mk_ref_arg temp_ (packPr_proj {| f := f0; frel := frel; f_frel := f_frel; funct := funct |}) wff_lem2 temp_2.
  subst temp_.

  recreate_var (bind_rel v_ (packPr_proj {| f := f0; frel := frel; f_frel := f_frel; funct := funct |})) bind_res.
  instExistGoal.*)
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
