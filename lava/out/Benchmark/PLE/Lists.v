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
  repeat first [split | solver].
Defined.

Definition C (VV : {VV: Z | True}) (VV_ : L): L :=
  exist _ (C_u ⌊ VV ⌋ ⌊ VV_ ⌋) (C_lem VV VV_).

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

Definition append_spec (ds_d3vS ys : L): Type :=
  L.

#[global] Hint Unfold append_spec: lia_unfold.

Definition append (ds_d3vS ys : L): append_spec ds_d3vS ys.
Proof.
  destruct ds_d3vS as [ds_d3vS ds_d3vS_p].
  destruct ys as [ys ys_p].
  try revert ys_p; generalize dependent ys; induction ds_d3vS as [x xs IH_xs|]; intros.
  - refine (C (# x) (IH_xs ltac:(try clear IH_xs; solver) ys ltac:(try clear IH_xs; solver))).
  - refine (exist (λ (ys : L_u), L_wf ys ∧ True) ys ltac:(solver)).
Defined.

Inductive append_rel: L_u → L_u → L_u → Prop :=
  | append_C_x: ∀ x xs ys (append_res : L_u),
                append_rel xs ys append_res → append_rel (C_u x xs) ys (C_u x append_res)
  | append_Emp_x: ∀ ys, append_rel Emp_u ys ys.

#[global] Hint Constructors append_rel: core_hint_db.

#[global] Instance append_lookup_rel: dictionary rel append := { lookup' := append_rel }.

#[global] Instance append_getF: getFunc append_rel := { getF' := append }.

Theorem append_rel_funct [ds_d3vS ys : L_u]:
  ∀ (VV VV' : L_u), append_rel ds_d3vS ys VV → (append_rel ds_d3vS ys VV' → VV = VV').
Proof.
  try revert ys_p; generalize dependent ys; induction ds_d3vS as [x xs IH_xs|]; intros;
  rel_functionhood_body.
Qed.

#[global] Hint Resolve append_rel_funct: f_rel_funct_db.

Theorem append_C_x_lem x xs ys append_C_x_lem_res:
  append_rel (C_u x xs) ys append_C_x_lem_res
  ↔ ∃ (append_res : L_u), append_rel xs ys append_res ∧ append_C_x_lem_res == C_u x append_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite append_C_x_lem: f_rel_back.

Theorem append_Emp_x_lem ys append_Emp_x_lem_res:
  append_rel Emp_u ys append_Emp_x_lem_res ↔ append_Emp_x_lem_res == ys.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite append_Emp_x_lem: f_rel_back.

Theorem append_rel_ex
  (ds_d3vS : L_u) (ds_d3vS_p : L_wf ds_d3vS ∧ True) (ys : L_u) (ys_p : L_wf ys ∧ True):
  append_rel ds_d3vS ys ⌊ append (exist _ ds_d3vS ds_d3vS_p) (exist _ ys ys_p) -⌋.
Proof.
  Opaque append.
  existence_lemma_pre append;
  try revert ys_p; generalize dependent ys; induction ds_d3vS as [x xs IH_xs|]; intros;
  [fix_notations;
   pose proof (IH_xs ltac:(try clear IH_xs; solver) ys ltac:(try clear IH_xs; solver)) as IH_47088561;
   try clear IH_xs |
   fix_notations];
  simpl in *.
  Transparent append.
  all: (existence_lemma_quicksolve append; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve append_rel_ex: rel_ax_db.

#[global] Opaque append.

Theorem append__append_rel_rw
  (ds_d3vS : L_u) (ds_d3vS_p : L_wf ds_d3vS ∧ True) (ys : L_u) (ys_p : L_wf ys ∧ True) (VV : L_u):
  ⌊ append (exist _ ds_d3vS ds_d3vS_p) (exist _ ys ys_p) -⌋ = VV ↔ append_rel ds_d3vS ys VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite append__append_rel_rw: f_rel_funct_db.

#[global] Hint Resolve append__append_rel_rw: rel_ax_db.

#[global] Instance append_lookup_rw: dictionary rwLem append := {
    lookup' := append__append_rel_rw }.

Theorem append__append_rel (ds_d3vS ys : L) (VV : L_u):
  ⌊ append ds_d3vS ys -⌋ = VV ↔ append_rel ⌊ ds_d3vS ⌋ ⌊ ys ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite append__append_rel: f_rel_funct_db.

Theorem append__append_rel' (ds_d3vS_u ys_u : L_u) (ds_d3vS ys : L) (VV : L_u):
  ds_d3vS_u = ⌊ ds_d3vS ⌋
  → (ys_u = ⌊ ys ⌋ → ⌊ append ds_d3vS ys -⌋ = VV ↔ append_rel ds_d3vS_u ys_u VV).
Proof.
  intros -> ->. refine (append__append_rel ds_d3vS ys VV).
Qed.

#[global] Hint Resolve append__append_rel': f_rel_funct_db.

Theorem append_rel_mk
  (ds_d3vS : L_u) (ds_d3vS_p : L_wf ds_d3vS ∧ True) (ys : L_u) (ys_p : L_wf ys ∧ True):
  {VV: _ | append_rel ds_d3vS ys VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, append_rel ds_d3vS ys VV)
          (append (exist _ ds_d3vS ds_d3vS_p) (exist _ ys ys_p))
          _);
  rewrite <- append__append_rel';
  quicksolve.
Qed.

#[global] Hint Resolve append_rel_mk: f_rel_funct_db.

#[global] Instance append_pack:
  @Pack
  (L ::RT λ (ds_d3vS : L), L ::RT λ (ys : L), nilRT)
  (L_u ::UT (L_u ::UT nilUT))
  ltac:(mkProjectsArgListTG (L ::RT λ (ds_d3vS : L), L ::RT λ (ys : L), nilRT) ((L_u ::UT (L_u ::UT nilUT))))
  L_u
  (λ (x_10954234 : ArgList (L ::RT λ (ds_d3vS : L), L ::RT λ (ys : L), nilRT)) (v_x_10954234 : L_u),
   ltac:(flattenP (λ (ds_d3vS ys : L) (VV : L_u), L_wf VV ∧ True) x_10954234 v_x_10954234)).
Proof.
  buildPackG append append_rel append__append_rel append_rel_funct.
Defined.

#[global] Instance append_upack: @uPack (L_u ::UT (L_u ::UT nilUT)) L_u.
Proof.
  buildUPackG append_rel append_rel_funct.
Defined.

Definition propConst1_spec (ds_d3vZ : {{True}}): Type :=
  {{∃ (append_res : L_u),
    append_rel (C_u 1 Emp_u) Emp_u append_res
    ∧ ∃ (append_res_2 : L_u), append_rel append_res Emp_u append_res_2 ∧ append_res_2 == C_u 1 Emp_u}}.

#[global] Hint Unfold propConst1_spec: lia_unfold.

Theorem propConst1 (ds_d3vZ : {{True}}): propConst1_spec ds_d3vZ.
Proof.
  destruct ds_d3vZ as [ds_d3vZ ds_d3vZ_p].
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (append_res : L_u),
           append_rel (C_u 1 Emp_u) Emp_u append_res
           ∧ ∃ (append_res_2 : L_u), append_rel append_res Emp_u append_res_2 ∧ append_res_2 == C_u 1 Emp_u)
          (# unit)
          ltac:(solver)).
Qed.

Definition propConst2_spec (ds_d3vY : {{True}}): Type :=
  {{∃ (append_res : L_u),
    append_rel (C_u 1 (C_u 2 Emp_u)) Emp_u append_res
    ∧ ∃ (append_res_2 : L_u),
      append_rel append_res Emp_u append_res_2 ∧ append_res_2 == C_u 1 (C_u 2 Emp_u)}}.

#[global] Hint Unfold propConst2_spec: lia_unfold.

Theorem propConst2 (ds_d3vY : {{True}}): propConst2_spec ds_d3vY.
Proof.
  destruct ds_d3vY as [ds_d3vY ds_d3vY_p].
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (append_res : L_u),
           append_rel (C_u 1 (C_u 2 Emp_u)) Emp_u append_res
           ∧ ∃ (append_res_2 : L_u),
             append_rel append_res Emp_u append_res_2 ∧ append_res_2 == C_u 1 (C_u 2 Emp_u))
          (# unit)
          ltac:(solver)).
Qed.

Definition propConst3_spec (ds_d3vX : {{True}}): Type :=
  {{∃ (append_res : L_u),
    append_rel (C_u 1 (C_u 2 (C_u 3 Emp_u))) Emp_u append_res
    ∧ ∃ (append_res_2 : L_u),
      append_rel append_res Emp_u append_res_2 ∧ append_res_2 == C_u 1 (C_u 2 (C_u 3 Emp_u))}}.

#[global] Hint Unfold propConst3_spec: lia_unfold.

Theorem propConst3 (ds_d3vX : {{True}}): propConst3_spec ds_d3vX.
Proof.
  destruct ds_d3vX as [ds_d3vX ds_d3vX_p].
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (append_res : L_u),
           append_rel (C_u 1 (C_u 2 (C_u 3 Emp_u))) Emp_u append_res
           ∧ ∃ (append_res_2 : L_u),
             append_rel append_res Emp_u append_res_2 ∧ append_res_2 == C_u 1 (C_u 2 (C_u 3 Emp_u)))
          (# unit)
          ltac:(solver)).
Qed.

Definition length_spec (ds_d3vV : L): Type :=
  {VV: Z | gebZ_rel VV 0 true}.

#[global] Hint Unfold length_spec: lia_unfold.

Definition length (ds_d3vV : L): length_spec ds_d3vV.
Proof.
  destruct ds_d3vV as [ds_d3vV ds_d3vV_p].
  induction ds_d3vV as [ds_d3vW xs IH_xs|].
  - refine (subsumptionCast
            Z
            (λ (VV : Z), gebZ_rel VV 0 true)
            (subsumptionCast Z (λ (x_1 : Z), True) (exist (λ (VV : Z), VV == 1) 1 ltac:(solver)) ltac:(solver)
             +Z subsumptionCast Z (λ (x_2 : Z), True) (IH_xs ltac:(try clear IH_xs; solver)) ltac:(solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Z
            (λ (VV : Z), gebZ_rel VV 0 true)
            (exist (λ (VV : Z), VV == 0) 0 ltac:(solver))
            ltac:(solver)).
Defined.

Inductive length_rel: L_u → Z → Prop :=
  | length_C: ∀ ds_d3vW xs (length_res : Z),
              length_rel xs length_res
              → ∀ (addZ_res : Z), addZ_rel 1 length_res addZ_res → length_rel (C_u ds_d3vW xs) addZ_res
  | length_Emp: length_rel Emp_u 0.

#[global] Hint Constructors length_rel: core_hint_db.

#[global] Instance length_lookup_rel: dictionary rel length := { lookup' := length_rel }.

#[global] Instance length_getF: getFunc length_rel := { getF' := length }.

Theorem length_rel_funct [ds_d3vV : L_u]:
  ∀ (VV VV' : Z), length_rel ds_d3vV VV → (length_rel ds_d3vV VV' → VV = VV').
Proof.
  induction ds_d3vV as [ds_d3vW xs IH_xs|]; rel_functionhood_body.
Qed.

#[global] Hint Resolve length_rel_funct: f_rel_funct_db.

Theorem length_C_lem ds_d3vW xs length_C_lem_res:
  length_rel (C_u ds_d3vW xs) length_C_lem_res
  ↔ ∃ (length_res : Z),
    length_rel xs length_res
    ∧ ∃ (addZ_res : Z), addZ_rel 1 length_res addZ_res ∧ length_C_lem_res == addZ_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite length_C_lem: f_rel_back.

Theorem length_Emp_lem length_Emp_lem_res:
  length_rel Emp_u length_Emp_lem_res ↔ length_Emp_lem_res == 0.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite length_Emp_lem: f_rel_back.

Theorem length_rel_ex (ds_d3vV : L_u) (ds_d3vV_p : L_wf ds_d3vV ∧ True):
  length_rel ds_d3vV ⌊ length (exist _ ds_d3vV ds_d3vV_p) -⌋.
Proof.
  Opaque length.
  existence_lemma_pre length;
  induction ds_d3vV as [ds_d3vW xs IH_xs|];
  [fix_notations; pose proof (IH_xs ltac:(try clear IH_xs; solver)) as IH_67415571; try clear IH_xs |
   fix_notations];
  simpl in *.
  Transparent length.
  all: (existence_lemma_quicksolve length; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve length_rel_ex: rel_ax_db.

#[global] Opaque length.

Theorem length__length_rel_rw (ds_d3vV : L_u) (ds_d3vV_p : L_wf ds_d3vV ∧ True) (VV : Z):
  ⌊ length (exist _ ds_d3vV ds_d3vV_p) -⌋ = VV ↔ length_rel ds_d3vV VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite length__length_rel_rw: f_rel_funct_db.

#[global] Hint Resolve length__length_rel_rw: rel_ax_db.

#[global] Instance length_lookup_rw: dictionary rwLem length := {
    lookup' := length__length_rel_rw }.

Theorem length__length_rel (ds_d3vV : L) (VV : Z):
  ⌊ length ds_d3vV -⌋ = VV ↔ length_rel ⌊ ds_d3vV ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite length__length_rel: f_rel_funct_db.

Theorem length__length_rel' (ds_d3vV_u : L_u) (ds_d3vV : L) (VV : Z):
  ds_d3vV_u = ⌊ ds_d3vV ⌋ → ⌊ length ds_d3vV -⌋ = VV ↔ length_rel ds_d3vV_u VV.
Proof.
  intros ->. refine (length__length_rel ds_d3vV VV).
Qed.

#[global] Hint Resolve length__length_rel': f_rel_funct_db.

Theorem length_rel_mk (ds_d3vV : L_u) (ds_d3vV_p : L_wf ds_d3vV ∧ True):
  {VV: _ | length_rel ds_d3vV VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, length_rel ds_d3vV VV) (length (exist _ ds_d3vV ds_d3vV_p)) _);
  rewrite <- length__length_rel';
  quicksolve.
Qed.

#[global] Hint Resolve length_rel_mk: f_rel_funct_db.

#[global] Instance length_pack:
  @Pack
  (L ::RT λ (ds_d3vV : L), nilRT)
  (L_u ::UT nilUT)
  ltac:(mkProjectsArgListTG (L ::RT λ (ds_d3vV : L), nilRT) ((L_u ::UT nilUT)))
  Z
  (λ (x_34509900 : ArgList (L ::RT λ (ds_d3vV : L), nilRT)) (v_x_34509900 : Z),
   ltac:(flattenP (λ (ds_d3vV : L) (VV : Z), gebZ_rel VV 0 true) x_34509900 v_x_34509900)).
Proof.
  buildPackG length length_rel length__length_rel length_rel_funct.
Defined.

#[global] Instance length_upack: @uPack (L_u ::UT nilUT) Z.
Proof.
  buildUPackG length_rel length_rel_funct.
Defined.

Definition prop_spec (x : {x: Z | True}) (xs ys zs : L): Type :=
  {{∃ (append_res : L_u),
    append_rel (C_u ⌊ x ⌋ ⌊ xs ⌋) ⌊ ys ⌋ append_res
    ∧ ∃ (append_res_2 : L_u),
      append_rel append_res ⌊ zs ⌋ append_res_2
      ∧ ∃ (append_res_3 : L_u),
        append_rel ⌊ xs ⌋ ⌊ ys ⌋ append_res_3
        ∧ ∃ (append_res_4 : L_u),
          append_rel append_res_3 ⌊ zs ⌋ append_res_4 ∧ append_res_2 == C_u ⌊ x ⌋ append_res_4}}.

#[global] Hint Unfold prop_spec: lia_unfold.

Theorem prop (x : {x: Z | True}) (xs ys zs : L): prop_spec x xs ys zs.
Proof.
  destruct x as [x x_p].
  destruct xs as [xs xs_p].
  destruct ys as [ys ys_p].
  destruct zs as [zs zs_p].
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (append_res : L_u),
           append_rel (C_u x xs) ys append_res
           ∧ ∃ (append_res_2 : L_u),
             append_rel append_res zs append_res_2
             ∧ ∃ (append_res_3 : L_u),
               append_rel xs ys append_res_3
               ∧ ∃ (append_res_4 : L_u),
                 append_rel append_res_3 zs append_res_4 ∧ append_res_2 == C_u x append_res_4)
          (# unit)
          ltac:(solver)).
Qed.
