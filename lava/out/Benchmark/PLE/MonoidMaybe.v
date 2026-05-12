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
  MaybeInt_wf ⌊ tm -⌋.
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

Definition mappend_spec (ds_d48G y : MaybeInt): Type :=
  MaybeInt.

#[global] Hint Unfold mappend_spec: lia_unfold.

Definition mappend (ds_d48G y : MaybeInt): mappend_spec ds_d48G y.
Proof.
  destruct ds_d48G as [ds_d48G ds_d48G_p].
  destruct y as [y y_p].
  destruct ds_d48G as [x|].
  - refine (Just (# x)).
  - refine (exist (λ (y : MaybeInt_u), MaybeInt_wf y ∧ True) y ltac:(solver)).
Defined.

Inductive mappend_rel: MaybeInt_u → MaybeInt_u → MaybeInt_u → Prop :=
  | mappend_Nothing_x: ∀ y, mappend_rel Nothing_u y y
  | mappend_Just_x: ∀ x y, mappend_rel (Just_u x) y (Just_u x).

#[global] Hint Constructors mappend_rel: core_hint_db.

#[global] Instance mappend_lookup_rel: dictionary rel mappend := { lookup' := mappend_rel }.

#[global] Instance mappend_getF: getFunc mappend_rel := { getF' := mappend }.

Theorem mappend_rel_funct [ds_d48G y : MaybeInt_u]:
  ∀ (VV VV' : MaybeInt_u), mappend_rel ds_d48G y VV → (mappend_rel ds_d48G y VV' → VV = VV').
Proof.
  destruct ds_d48G as [x|]; rel_functionhood_body.
Qed.

#[global] Hint Resolve mappend_rel_funct: f_rel_funct_db.

Theorem mappend_Nothing_x_lem y mappend_Nothing_x_lem_res:
  mappend_rel Nothing_u y mappend_Nothing_x_lem_res ↔ mappend_Nothing_x_lem_res == y.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite mappend_Nothing_x_lem: f_rel_back.

Theorem mappend_Just_x_lem x y mappend_Just_x_lem_res:
  mappend_rel (Just_u x) y mappend_Just_x_lem_res ↔ mappend_Just_x_lem_res == Just_u x.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite mappend_Just_x_lem: f_rel_back.

Theorem mappend_rel_ex
  (ds_d48G : MaybeInt_u)
  (ds_d48G_p : MaybeInt_wf ds_d48G ∧ True)
  (y : MaybeInt_u)
  (y_p : MaybeInt_wf y ∧ True):
  mappend_rel ds_d48G y ⌊ mappend (exist _ ds_d48G ds_d48G_p) (exist _ y y_p) -⌋.
Proof.
  Opaque mappend.
  existence_lemma_pre mappend;
  destruct ds_d48G as [x|];
  [fix_notations | fix_notations];
  simpl in *.
  Transparent mappend.
  all: (existence_lemma_quicksolve mappend; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve mappend_rel_ex: rel_ax_db.

#[global] Opaque mappend.

Theorem mappend__mappend_rel_rw
  (ds_d48G : MaybeInt_u)
  (ds_d48G_p : MaybeInt_wf ds_d48G ∧ True)
  (y : MaybeInt_u)
  (y_p : MaybeInt_wf y ∧ True)
  (VV : MaybeInt_u):
  ⌊ mappend (exist _ ds_d48G ds_d48G_p) (exist _ y y_p) -⌋ = VV ↔ mappend_rel ds_d48G y VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite mappend__mappend_rel_rw: f_rel_funct_db.

#[global] Hint Resolve mappend__mappend_rel_rw: rel_ax_db.

#[global] Instance mappend_lookup_rw: dictionary rwLem mappend := {
    lookup' := mappend__mappend_rel_rw }.

Theorem mappend__mappend_rel (ds_d48G y : MaybeInt) (VV : MaybeInt_u):
  ⌊ mappend ds_d48G y -⌋ = VV ↔ mappend_rel ⌊ ds_d48G ⌋ ⌊ y ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite mappend__mappend_rel: f_rel_funct_db.

Theorem mappend__mappend_rel' (ds_d48G_u y_u : MaybeInt_u) (ds_d48G y : MaybeInt) (VV : MaybeInt_u):
  ds_d48G_u = ⌊ ds_d48G ⌋
  → (y_u = ⌊ y ⌋ → ⌊ mappend ds_d48G y -⌋ = VV ↔ mappend_rel ds_d48G_u y_u VV).
Proof.
  intros -> ->. refine (mappend__mappend_rel ds_d48G y VV).
Qed.

#[global] Hint Resolve mappend__mappend_rel': f_rel_funct_db.

Theorem mappend_rel_mk
  (ds_d48G : MaybeInt_u)
  (ds_d48G_p : MaybeInt_wf ds_d48G ∧ True)
  (y : MaybeInt_u)
  (y_p : MaybeInt_wf y ∧ True):
  {VV: _ | mappend_rel ds_d48G y VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, mappend_rel ds_d48G y VV)
          (mappend (exist _ ds_d48G ds_d48G_p) (exist _ y y_p))
          _);
  rewrite <- mappend__mappend_rel';
  quicksolve.
Qed.

#[global] Hint Resolve mappend_rel_mk: f_rel_funct_db.

#[global] Instance mappend_pack:
  @Pack
  (MaybeInt ::RT λ (ds_d48G : MaybeInt), MaybeInt ::RT λ (y : MaybeInt), nilRT)
  (MaybeInt_u ::UT (MaybeInt_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((MaybeInt
  ::RT λ (ds_d48G : MaybeInt),
       MaybeInt ::RT λ (y : MaybeInt), nilRT)) ((MaybeInt_u ::UT (MaybeInt_u ::UT nilUT))))
  MaybeInt_u
  (λ (x_53827607 : ArgList (MaybeInt
                            ::RT λ (ds_d48G : MaybeInt), MaybeInt ::RT λ (y : MaybeInt), nilRT))
     (v_x_53827607 : MaybeInt_u),
   ltac:(flattenP (λ (ds_d48G y : MaybeInt) (VV : MaybeInt_u), MaybeInt_wf VV ∧ True) x_53827607 v_x_53827607)).
Proof.
  buildPackG mappend mappend_rel mappend__mappend_rel mappend_rel_funct.
Defined.

#[global] Instance mappend_upack: @uPack (MaybeInt_u ::UT (MaybeInt_u ::UT nilUT)) MaybeInt_u.
Proof.
  buildUPackG mappend_rel mappend_rel_funct.
Defined.

Definition mappend_assoc_spec (ds_d48D y z : MaybeInt): Type :=
  {{∃ (mappend_res : MaybeInt_u),
    mappend_rel ⌊ ds_d48D ⌋ ⌊ y ⌋ mappend_res
    ∧ ∃ (mappend_res_2 : MaybeInt_u),
      mappend_rel mappend_res ⌊ z ⌋ mappend_res_2
      ∧ ∃ (mappend_res_3 : MaybeInt_u),
        mappend_rel ⌊ y ⌋ ⌊ z ⌋ mappend_res_3
        ∧ ∃ (mappend_res_4 : MaybeInt_u),
          mappend_rel ⌊ ds_d48D ⌋ mappend_res_3 mappend_res_4 ∧ mappend_res_2 == mappend_res_4}}.

#[global] Hint Unfold mappend_assoc_spec: lia_unfold.

Theorem mappend_assoc (ds_d48D y z : MaybeInt): mappend_assoc_spec ds_d48D y z.
Proof.
  destruct ds_d48D as [ds_d48D ds_d48D_p].
  destruct y as [y y_p].
  destruct z as [z z_p].
  destruct ds_d48D as [x|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (mappend_res : MaybeInt_u),
             mappend_rel ds_d48D y mappend_res
             ∧ ∃ (mappend_res_2 : MaybeInt_u),
               mappend_rel mappend_res z mappend_res_2
               ∧ ∃ (mappend_res_3 : MaybeInt_u),
                 mappend_rel y z mappend_res_3
                 ∧ ∃ (mappend_res_4 : MaybeInt_u),
                   mappend_rel ds_d48D mappend_res_3 mappend_res_4 ∧ mappend_res_2 == mappend_res_4)
            (# unit)
            ltac:(solver)).
  - destruct y as [y|].
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∃ (mappend_res : MaybeInt_u),
               mappend_rel ds_d48D y mappend_res
               ∧ ∃ (mappend_res_2 : MaybeInt_u),
                 mappend_rel mappend_res z mappend_res_2
                 ∧ ∃ (mappend_res_3 : MaybeInt_u),
                   mappend_rel y z mappend_res_3
                   ∧ ∃ (mappend_res_4 : MaybeInt_u),
                     mappend_rel ds_d48D mappend_res_3 mappend_res_4 ∧ mappend_res_2 == mappend_res_4)
              (# unit)
              ltac:(solver)).
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∃ (mappend_res : MaybeInt_u),
               mappend_rel ds_d48D y mappend_res
               ∧ ∃ (mappend_res_2 : MaybeInt_u),
                 mappend_rel mappend_res z mappend_res_2
                 ∧ ∃ (mappend_res_3 : MaybeInt_u),
                   mappend_rel y z mappend_res_3
                   ∧ ∃ (mappend_res_4 : MaybeInt_u),
                     mappend_rel ds_d48D mappend_res_3 mappend_res_4 ∧ mappend_res_2 == mappend_res_4)
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

Definition mempty_left_spec (ds_d48F : MaybeInt): Type :=
  {{∃ (mappend_res : MaybeInt_u),
    mappend_rel ⌊ mempty -⌋ ⌊ ds_d48F ⌋ mappend_res ∧ mappend_res == ⌊ ds_d48F ⌋}}.

#[global] Hint Unfold mempty_left_spec: lia_unfold.

Theorem mempty_left (ds_d48F : MaybeInt): mempty_left_spec ds_d48F.
Proof.
  destruct ds_d48F as [ds_d48F ds_d48F_p].
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (mappend_res : MaybeInt_u), mappend_rel ⌊ mempty -⌋ ds_d48F mappend_res ∧ mappend_res == ds_d48F)
          (# unit)
          ltac:(solver)).
Qed.

Definition mempty_right_spec (ds_d48E : MaybeInt): Type :=
  {{∃ (mappend_res : MaybeInt_u),
    mappend_rel ⌊ ds_d48E ⌋ ⌊ mempty -⌋ mappend_res ∧ mappend_res == ⌊ ds_d48E ⌋}}.

#[global] Hint Unfold mempty_right_spec: lia_unfold.

Theorem mempty_right (ds_d48E : MaybeInt): mempty_right_spec ds_d48E.
Proof.
  destruct ds_d48E as [ds_d48E ds_d48E_p].
  destruct ds_d48E as [x|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (mappend_res : MaybeInt_u), mappend_rel ds_d48E ⌊ mempty -⌋ mappend_res ∧ mappend_res == ds_d48E)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (mappend_res : MaybeInt_u), mappend_rel ds_d48E ⌊ mempty -⌋ mappend_res ∧ mappend_res == ds_d48E)
            (# unit)
            ltac:(solver)).
Qed.
