From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Set Universe Polymorphism.
From Coq Require Import Unicode.Utf8.

Inductive MaybeInt_u: Type :=
  | Just_u: Z → MaybeInt_u | Nothing_u: MaybeInt_u.

Fixpoint MaybeInt_eq (x y : MaybeInt_u): bool :=
  match (x, y) with
  | (Just_u VV, Just_u VV') => true && (VV ==? VV')
  | (Nothing_u, Nothing_u) => true
  | (_, _) => false
  end.

Theorem MaybeInt_eq_refl : ∀ (x : MaybeInt_u), is_true (MaybeInt_eq x x).
Proof.
  eq_refl_rec.
Qed.

#[global] Hint Resolve MaybeInt_eq_refl: eq_hint_db.

Theorem MaybeInt_eqb_eq : ∀ (s t : MaybeInt_u), is_true (MaybeInt_eq s t) → s = t.
Proof.
  eqb_eq_lem.
Qed.

#[global] Hint Resolve MaybeInt_eqb_eq: eq_hint_db.

#[global] Instance leibnitz_eq_MaybeInt: LeibnitzEqB := {
    equalB' := MaybeInt_eq;
    refl' := MaybeInt_eq_refl;
    eqb_eq' := MaybeInt_eqb_eq }.

Fixpoint MaybeInt_wf (x : MaybeInt_u): Prop :=
  match x with | Just_u VV => True | Nothing_u => True end.

Theorem MaybeInt_wf_ref [p : MaybeInt_u → Prop] (tm : {v: MaybeInt_u | MaybeInt_wf v ∧ p v}):
  MaybeInt_wf ⌊ tm ⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation MaybeInt := {x: MaybeInt_u | MaybeInt_wf x ∧ True}.

Definition Just_lem (VV : {VV: Z | True}): MaybeInt_wf (Just_u ⌊ VV ⌋) ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Just (VV : {VV: Z | True}): MaybeInt :=
  exist _ (Just_u ⌊ VV ⌋) (Just_lem VV).

Definition Nothing_lem : MaybeInt_wf Nothing_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Nothing : MaybeInt :=
  exist _ Nothing_u Nothing_lem.

#[global] Hint Resolve MaybeInt_wf_ref: wf_constr_db.

#[global] Hint Unfold MaybeInt_wf: wf_constr_db.

#[global] Hint Resolve MaybeInt_eq: ref_constr_db.

#[global] Hint Unfold Just: ref_constr_db.

#[global] Hint Unfold Nothing: ref_constr_db.

Definition mappend_spec (lq_tmp0 lq_tmp1 : MaybeInt): Type :=
  MaybeInt.

#[global] Hint Unfold mappend_spec: lia_unfold.

Definition mappend (lq_tmp0 lq_tmp1 : MaybeInt): mappend_spec lq_tmp0 lq_tmp1.
Proof.
  destruct lq_tmp0 as [lq_tmp0 lq_tmp0_p].
  destruct lq_tmp1 as [lq_tmp1 lq_tmp1_p].
  destruct lq_tmp0 as [x|].
  - refine (Just (# x)).
  - refine (exist (λ (lq_tmp1 : MaybeInt_u), MaybeInt_wf lq_tmp1 ∧ True) lq_tmp1 ltac:(solver)).
Defined.

Inductive mappend_rel: MaybeInt_u → MaybeInt_u → MaybeInt_u → Prop :=
  | mappend_Nothing_x: ∀ lq_tmp1, mappend_rel Nothing_u lq_tmp1 lq_tmp1
  | mappend_Just_x: ∀ x lq_tmp1, mappend_rel (Just_u x) lq_tmp1 (Just_u x).

#[global] Hint Constructors mappend_rel: core_hint_db.

#[global] Instance mappend_lookup_rel: dictionary rel mappend := { lookup' := mappend_rel }.

#[global] Instance mappend_getF: getFunc mappend_rel := { getF' := mappend }.

Theorem mappend_rel_funct [lq_tmp0 lq_tmp1 : MaybeInt_u]:
  ∀ (VV VV' : MaybeInt_u),
  mappend_rel lq_tmp0 lq_tmp1 VV → (mappend_rel lq_tmp0 lq_tmp1 VV' → VV = VV').
Proof.
  destruct lq_tmp0 as [x|]; rel_functionhood_body.
Qed.

#[global] Hint Resolve mappend_rel_funct: f_rel_funct_db.

Theorem mappend_Nothing_x_lem lq_tmp1 mappend_Nothing_x_lem_res:
  mappend_rel Nothing_u lq_tmp1 mappend_Nothing_x_lem_res ↔ mappend_Nothing_x_lem_res == lq_tmp1.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite mappend_Nothing_x_lem: f_rel_back.

Theorem mappend_Just_x_lem lq_tmp1 x mappend_Just_x_lem_res:
  mappend_rel (Just_u x) lq_tmp1 mappend_Just_x_lem_res ↔ mappend_Just_x_lem_res == Just_u x.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite mappend_Just_x_lem: f_rel_back.

Theorem mappend_rel_ex
  (lq_tmp0 : MaybeInt_u)
  (lq_tmp0_p : MaybeInt_wf lq_tmp0 ∧ True)
  (lq_tmp1 : MaybeInt_u)
  (lq_tmp1_p : MaybeInt_wf lq_tmp1 ∧ True):
  mappend_rel lq_tmp0 lq_tmp1 ⌊ mappend (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p) ⌋.
Proof.
  Opaque mappend.
  existence_lemma_pre mappend;
  destruct lq_tmp0 as [x|];
  [fix_notations | fix_notations];
  simpl in *.
  Transparent mappend.
  all: existence_lemma_quicksolve mappend; f__f_rel_ex_body; f_rel_finish.
Qed.

#[global] Hint Resolve mappend_rel_ex: rel_ax_db.

#[global] Opaque mappend.

Theorem mappend__mappend_rel_rw
  (lq_tmp0 : MaybeInt_u)
  (lq_tmp0_p : MaybeInt_wf lq_tmp0 ∧ True)
  (lq_tmp1 : MaybeInt_u)
  (lq_tmp1_p : MaybeInt_wf lq_tmp1 ∧ True)
  (VV : MaybeInt_u):
  ⌊ mappend (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p) ⌋ = VV
  ↔ mappend_rel lq_tmp0 lq_tmp1 VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite mappend__mappend_rel_rw: f_rel_funct_db.

#[global] Hint Resolve mappend__mappend_rel_rw: rel_ax_db.

#[global] Instance mappend_lookup_rw: dictionary rwLem mappend := {
    lookup' := mappend__mappend_rel_rw }.

Theorem mappend__mappend_rel (lq_tmp0 lq_tmp1 : MaybeInt) (VV : MaybeInt_u):
  ⌊ mappend lq_tmp0 lq_tmp1 ⌋ = VV ↔ mappend_rel ⌊ lq_tmp0 ⌋ ⌊ lq_tmp1 ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite mappend__mappend_rel: f_rel_funct_db.

Theorem mappend__mappend_rel'
  (lq_tmp0_u lq_tmp1_u : MaybeInt_u) (lq_tmp0 lq_tmp1 : MaybeInt) (VV : MaybeInt_u):
  lq_tmp0_u = ⌊ lq_tmp0 ⌋
  → (lq_tmp1_u = ⌊ lq_tmp1 ⌋ → ⌊ mappend lq_tmp0 lq_tmp1 ⌋ = VV ↔ mappend_rel lq_tmp0_u lq_tmp1_u VV).
Proof.
  intros -> ->. refine (mappend__mappend_rel lq_tmp0 lq_tmp1 VV).
Qed.

#[global] Hint Resolve mappend__mappend_rel': f_rel_funct_db.

Theorem mappend_rel_mk
  (lq_tmp0 : MaybeInt_u)
  (lq_tmp0_p : MaybeInt_wf lq_tmp0 ∧ True)
  (lq_tmp1 : MaybeInt_u)
  (lq_tmp1_p : MaybeInt_wf lq_tmp1 ∧ True):
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
  (MaybeInt ::RT λ (lq_tmp0 : MaybeInt), MaybeInt ::RT λ (lq_tmp1 : MaybeInt), nilRT)
  (MaybeInt_u ::UT (MaybeInt_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((MaybeInt
  ::RT λ (lq_tmp0 : MaybeInt),
       MaybeInt ::RT λ (lq_tmp1 : MaybeInt), nilRT)) ((MaybeInt_u ::UT (MaybeInt_u ::UT nilUT))))
  MaybeInt_u
  (λ (x_63413805 : ArgList (MaybeInt
                            ::RT λ (lq_tmp0 : MaybeInt), MaybeInt ::RT λ (lq_tmp1 : MaybeInt), nilRT))
     (v_x_63413805 : MaybeInt_u),
   ltac:(flattenP (λ (lq_tmp0 lq_tmp1 : MaybeInt) (VV : MaybeInt_u),
 MaybeInt_wf VV ∧ True) x_63413805 v_x_63413805)).
Proof.
  buildPackG mappend mappend_rel mappend__mappend_rel mappend_rel_funct.
Defined.

#[global] Instance mappend_upack: @uPack (MaybeInt_u ::UT (MaybeInt_u ::UT nilUT)) MaybeInt_u.
Proof.
  buildUPackG mappend_rel mappend_rel_funct.
Defined.

Definition mappend_assoc_spec (xs ys zs : MaybeInt): Type :=
  {{∀ mappend_res,
    mappend_rel ⌊ xs ⌋ ⌊ ys ⌋ mappend_res
    → ∀ mappend_res_2,
      mappend_rel mappend_res ⌊ zs ⌋ mappend_res_2
      → ∀ mappend_res_3,
        mappend_rel ⌊ ys ⌋ ⌊ zs ⌋ mappend_res_3
        → ∀ mappend_res_4,
          mappend_rel ⌊ xs ⌋ mappend_res_3 mappend_res_4 → mappend_res_2 == mappend_res_4}}.

#[global] Hint Unfold mappend_assoc_spec: lia_unfold.

Theorem mappend_assoc (xs ys zs : MaybeInt): mappend_assoc_spec xs ys zs.
Proof.
  destruct xs as [xs xs_p].
  destruct ys as [ys ys_p].
  destruct zs as [zs zs_p].
  destruct xs as [x|].
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
  - destruct ys as [y|].
    + refine (subsumptionCast
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
    + refine (subsumptionCast
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
Qed.

Definition mempty_spec : Type :=
  MaybeInt.

#[global] Hint Unfold mempty_spec: lia_unfold.

Definition mempty : mempty_spec.
Proof.
  refine Nothing.
Defined.

Inductive mempty_rel: MaybeInt_u → Prop :=
  | mempty_Constr: mempty_rel Nothing_u.

#[global] Hint Constructors mempty_rel: core_hint_db.

#[global] Instance mempty_lookup_rel: dictionary rel mempty := { lookup' := mempty_rel }.

#[global] Instance mempty_getF: getFunc mempty_rel := { getF' := mempty }.

Theorem mempty_rel_funct : ∀ (VV VV' : MaybeInt_u), mempty_rel VV → (mempty_rel VV' → VV = VV').
Proof.
  rel_functionhood_body.
Qed.

#[global] Hint Resolve mempty_rel_funct: f_rel_funct_db.

Theorem mempty_inv_lem mempty_inv_lem_res:
  mempty_rel mempty_inv_lem_res ↔ mempty_inv_lem_res == Nothing_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite mempty_inv_lem: f_rel_back.

Theorem mempty_rel_ex : mempty_rel ⌊ mempty ⌋.
Proof.
  Opaque mempty.
  existence_lemma_pre mempty; fix_notations; simpl in *.
  Transparent mempty.
  all: existence_lemma_quicksolve mempty; f__f_rel_ex_body; f_rel_finish.
Qed.

#[global] Hint Resolve mempty_rel_ex: rel_ax_db.

#[global] Opaque mempty.

Theorem mempty__mempty_rel_rw (VV : MaybeInt_u): ⌊ mempty ⌋ = VV ↔ mempty_rel VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite mempty__mempty_rel_rw: f_rel_funct_db.

#[global] Hint Resolve mempty__mempty_rel_rw: rel_ax_db.

#[global] Instance mempty_lookup_rw: dictionary rwLem mempty := {
    lookup' := mempty__mempty_rel_rw }.

Theorem mempty__mempty_rel (VV : MaybeInt_u): ⌊ mempty ⌋ = VV ↔ mempty_rel VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite mempty__mempty_rel: f_rel_funct_db.

Theorem mempty__mempty_rel' (VV : MaybeInt_u): ⌊ mempty ⌋ = VV ↔ mempty_rel VV.
Proof.
  intros. refine (mempty__mempty_rel VV).
Qed.

#[global] Hint Resolve mempty__mempty_rel': f_rel_funct_db.

Theorem mempty_rel_mk : {VV: _ | mempty_rel VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, mempty_rel VV) mempty _);
  rewrite <- mempty__mempty_rel';
  quicksolve.
Qed.

#[global] Hint Resolve mempty_rel_mk: f_rel_funct_db.

Definition mempty_left_spec (x : MaybeInt): Type :=
  {{∀ mempty_res,
    mempty_rel mempty_res
    → ∀ mappend_res, mappend_rel mempty_res ⌊ x ⌋ mappend_res → mappend_res == ⌊ x ⌋}}.

#[global] Hint Unfold mempty_left_spec: lia_unfold.

Theorem mempty_left (x : MaybeInt): mempty_left_spec x.
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
Qed.

Definition mempty_right_spec (x : MaybeInt): Type :=
  {{∀ mempty_res,
    mempty_rel mempty_res
    → ∀ mappend_res, mappend_rel ⌊ x ⌋ mempty_res mappend_res → mappend_res == ⌊ x ⌋}}.

#[global] Hint Unfold mempty_right_spec: lia_unfold.

Theorem mempty_right (x : MaybeInt): mempty_right_spec x.
Proof.
  destruct x as [x x_p].
  destruct x as [x|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∀ mempty_res,
             mempty_rel mempty_res
             → ∀ mappend_res, mappend_rel ⌊ x ⌋ mempty_res mappend_res → mappend_res == ⌊ x ⌋)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∀ mempty_res,
             mempty_rel mempty_res
             → ∀ mappend_res, mappend_rel ⌊ x ⌋ mempty_res mappend_res → mappend_res == ⌊ x ⌋)
            (# unit)
            ltac:(solver)).
Qed.
