From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Set Universe Polymorphism. 
From Coq Require Import Unicode.Utf8.

Inductive SFBool_u: Type :=
  | SFFalse_u: SFBool_u | SFTrue_u: SFBool_u.

Fixpoint SFBool_eq (x y : SFBool_u): bool :=
  match (x, y) with
  | (SFFalse_u, SFFalse_u) => true
  | (SFTrue_u, SFTrue_u) => true
  | (_, _) => false
  end.

Theorem SFBool_eq_refl : ∀ (x : SFBool_u), is_true (SFBool_eq x x).
Proof.
  eq_refl_rec.
Qed.

#[global] Hint Resolve SFBool_eq_refl: eq_hint_db.

Theorem SFBool_eqb_eq : ∀ (s t : SFBool_u), is_true (SFBool_eq s t) → s = t.
Proof.
  eqb_eq_lem.
Qed.

#[global] Hint Resolve SFBool_eqb_eq: eq_hint_db.

#[global] Instance leibnitz_eq_SFBool: LeibnitzEqB := {
    equalB' := SFBool_eq;
    refl' := SFBool_eq_refl;
    eqb_eq' := SFBool_eqb_eq }.

Fixpoint SFBool_wf (x : SFBool_u): Prop :=
  match x with | SFFalse_u => True | SFTrue_u => True end.

Theorem SFBool_wf_ref [p : SFBool_u → Prop] (tm : {v: SFBool_u | SFBool_wf v ∧ p v}):
  SFBool_wf ⌊ tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation SFBool := {x: SFBool_u | SFBool_wf x ∧ True}.

Definition SFFalse_lem : SFBool_wf SFFalse_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition SFFalse : SFBool :=
  exist _ SFFalse_u SFFalse_lem.

Definition SFTrue_lem : SFBool_wf SFTrue_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition SFTrue : SFBool :=
  exist _ SFTrue_u SFTrue_lem.

#[global] Hint Resolve SFBool_wf_ref: wf_constr_db.

#[global] Hint Unfold SFBool_wf: wf_constr_db.

#[global] Hint Resolve SFBool_eq: ref_constr_db.

#[global] Hint Unfold SFFalse: ref_constr_db.

#[global] Hint Unfold SFTrue: ref_constr_db.

Definition andb_spec (b1 b2 : SFBool): Type :=
  SFBool.

#[global] Hint Unfold andb_spec: lia_unfold.

Definition andb (b1 b2 : SFBool): andb_spec b1 b2.
Proof.
  destruct b1 as [b1 b1_p].
  destruct b2 as [b2 b2_p].
  destruct b1 as [|].
  - refine SFFalse.
  - refine (exist (λ (b2 : SFBool_u), SFBool_wf b2 ∧ True) b2 ltac:(solver)).
Defined.

Inductive andb_rel: SFBool_u → SFBool_u → SFBool_u → Prop :=
  | andb_SFFalse_x: ∀ b2, andb_rel SFFalse_u b2 SFFalse_u
  | andb_SFTrue_x: ∀ b2, andb_rel SFTrue_u b2 b2.

#[global] Hint Constructors andb_rel: core_hint_db.

#[global] Instance andb_lookup_rel: dictionary rel andb := { lookup' := andb_rel }.

#[global] Instance andb_getF: getFunc andb_rel := { getF' := andb }.

Theorem andb_rel_funct [b1 b2 : SFBool_u]:
  ∀ (VV VV' : SFBool_u), andb_rel b1 b2 VV → (andb_rel b1 b2 VV' → VV = VV').
Proof.
  destruct b1 as [|]; rel_functionhood_body.
Qed.

#[global] Hint Resolve andb_rel_funct: f_rel_funct_db.

Theorem andb_SFFalse_x_lem b2 andb_SFFalse_x_lem_res:
  andb_rel SFFalse_u b2 andb_SFFalse_x_lem_res ↔ andb_SFFalse_x_lem_res == SFFalse_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite andb_SFFalse_x_lem: f_rel_back.

Theorem andb_SFTrue_x_lem b2 andb_SFTrue_x_lem_res:
  andb_rel SFTrue_u b2 andb_SFTrue_x_lem_res ↔ andb_SFTrue_x_lem_res == b2.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite andb_SFTrue_x_lem: f_rel_back.

Theorem andb_rel_ex
  (b1 : SFBool_u) (b1_p : SFBool_wf b1 ∧ True) (b2 : SFBool_u) (b2_p : SFBool_wf b2 ∧ True):
  andb_rel b1 b2 ⌊ andb (exist _ b1 b1_p) (exist _ b2 b2_p) -⌋.
Proof.
  Opaque andb.
  existence_lemma_pre andb;
  destruct b1 as [|];
  [fix_notations | fix_notations];
  simpl in *.
  Transparent andb.
  all: (existence_lemma_quicksolve andb; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve andb_rel_ex: rel_ax_db.

#[global] Opaque andb.

Theorem andb__andb_rel_rw
  (b1 : SFBool_u)
  (b1_p : SFBool_wf b1 ∧ True)
  (b2 : SFBool_u)
  (b2_p : SFBool_wf b2 ∧ True)
  (VV : SFBool_u):
  ⌊ andb (exist _ b1 b1_p) (exist _ b2 b2_p) -⌋ = VV ↔ andb_rel b1 b2 VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite andb__andb_rel_rw: f_rel_funct_db.

#[global] Hint Resolve andb__andb_rel_rw: rel_ax_db.

#[global] Instance andb_lookup_rw: dictionary rwLem andb := { lookup' := andb__andb_rel_rw }.

Theorem andb__andb_rel (b1 b2 : SFBool) (VV : SFBool_u):
  ⌊ andb b1 b2 -⌋ = VV ↔ andb_rel ⌊ b1 ⌋ ⌊ b2 ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite andb__andb_rel: f_rel_funct_db.

Theorem andb__andb_rel' (b1_u b2_u : SFBool_u) (b1 b2 : SFBool) (VV : SFBool_u):
  b1_u = ⌊ b1 ⌋ → (b2_u = ⌊ b2 ⌋ → ⌊ andb b1 b2 -⌋ = VV ↔ andb_rel b1_u b2_u VV).
Proof.
  intros -> ->. refine (andb__andb_rel b1 b2 VV).
Qed.

#[global] Hint Resolve andb__andb_rel': f_rel_funct_db.

Theorem andb_rel_mk
  (b1 : SFBool_u) (b1_p : SFBool_wf b1 ∧ True) (b2 : SFBool_u) (b2_p : SFBool_wf b2 ∧ True):
  {VV: _ | andb_rel b1 b2 VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, andb_rel b1 b2 VV) (andb (exist _ b1 b1_p) (exist _ b2 b2_p)) _);
  rewrite <- andb__andb_rel';
  quicksolve.
Qed.

#[global] Hint Resolve andb_rel_mk: f_rel_funct_db.

#[global] Instance andb_pack:
  @Pack
  (SFBool ::RT λ (b1 : SFBool), SFBool ::RT λ (b2 : SFBool), nilRT)
  (SFBool_u ::UT (SFBool_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((SFBool ::RT λ (b1 : SFBool), SFBool ::RT λ (b2 : SFBool), nilRT)) ((SFBool_u ::UT (SFBool_u ::UT nilUT))))
  SFBool_u
  (λ (x_89922389 : ArgList (SFBool ::RT λ (b1 : SFBool), SFBool ::RT λ (b2 : SFBool), nilRT))
     (v_x_89922389 : SFBool_u),
   ltac:(flattenP (λ (b1 b2 : SFBool) (VV : SFBool_u), SFBool_wf VV ∧ True) x_89922389 v_x_89922389)).
Proof.
  buildPackG andb andb_rel andb__andb_rel andb_rel_funct.
Defined.

#[global] Instance andb_upack: @uPack (SFBool_u ::UT (SFBool_u ::UT nilUT)) SFBool_u.
Proof.
  buildUPackG andb_rel andb_rel_funct.
Defined.

Definition andb'_spec (b1 b2 : SFBool): Type :=
  SFBool.

#[global] Hint Unfold andb'_spec: lia_unfold.

Definition andb' (b1 b2 : SFBool): andb'_spec b1 b2.
Proof.
  destruct b1 as [b1 b1_p].
  destruct b2 as [b2 b2_p].
  let E := fresh "E" in destruct (b1 ==? SFTrue_u) as [|] eqn:E;
  [refine (exist (λ (b2 : SFBool_u), SFBool_wf b2 ∧ True) b2 ltac:(solver)) | refine SFFalse].
Defined.

Definition andb3_spec (ds_d3iD ds_d3iE ds_d3iF : SFBool): Type :=
  SFBool.

#[global] Hint Unfold andb3_spec: lia_unfold.

Definition andb3 (ds_d3iD ds_d3iE ds_d3iF : SFBool): andb3_spec ds_d3iD ds_d3iE ds_d3iF.
Proof.
  destruct ds_d3iD as [ds_d3iD ds_d3iD_p].
  destruct ds_d3iE as [ds_d3iE ds_d3iE_p].
  destruct ds_d3iF as [ds_d3iF ds_d3iF_p].
  destruct ds_d3iD as [|].
  - refine SFFalse.
  - destruct ds_d3iE as [|].
    + refine SFFalse.
    + destruct ds_d3iF as [|].
      ** refine SFFalse.
      ** refine SFTrue.
Defined.

Inductive andb3_rel: SFBool_u → SFBool_u → SFBool_u → SFBool_u → Prop :=
  | andb3_SFFalse_x_x: ∀ ds_d3iE ds_d3iF, andb3_rel SFFalse_u ds_d3iE ds_d3iF SFFalse_u
  | andb3_SFTrue_SFFalse_x: ∀ ds_d3iF, andb3_rel SFTrue_u SFFalse_u ds_d3iF SFFalse_u
  | andb3_SFTrue_SFTrue_SFFalse: andb3_rel SFTrue_u SFTrue_u SFFalse_u SFFalse_u
  | andb3_SFTrue_SFTrue_SFTrue: andb3_rel SFTrue_u SFTrue_u SFTrue_u SFTrue_u.

#[global] Hint Constructors andb3_rel: core_hint_db.

#[global] Instance andb3_lookup_rel: dictionary rel andb3 := { lookup' := andb3_rel }.

#[global] Instance andb3_getF: getFunc andb3_rel := { getF' := andb3 }.

Theorem andb3_rel_funct [ds_d3iD ds_d3iE ds_d3iF : SFBool_u]:
  ∀ (VV VV' : SFBool_u),
  andb3_rel ds_d3iD ds_d3iE ds_d3iF VV → (andb3_rel ds_d3iD ds_d3iE ds_d3iF VV' → VV = VV').
Proof.
  destruct ds_d3iD as [|];
  [ |
   destruct ds_d3iE as [|];
   [ | destruct ds_d3iF as [|]]];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve andb3_rel_funct: f_rel_funct_db.

Theorem andb3_SFFalse_x_x_lem ds_d3iE ds_d3iF andb3_SFFalse_x_x_lem_res:
  andb3_rel SFFalse_u ds_d3iE ds_d3iF andb3_SFFalse_x_x_lem_res
  ↔ andb3_SFFalse_x_x_lem_res == SFFalse_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite andb3_SFFalse_x_x_lem: f_rel_back.

Theorem andb3_SFTrue_SFFalse_x_lem ds_d3iF andb3_SFTrue_SFFalse_x_lem_res:
  andb3_rel SFTrue_u SFFalse_u ds_d3iF andb3_SFTrue_SFFalse_x_lem_res
  ↔ andb3_SFTrue_SFFalse_x_lem_res == SFFalse_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite andb3_SFTrue_SFFalse_x_lem: f_rel_back.

Theorem andb3_SFTrue_SFTrue_SFFalse_lem andb3_SFTrue_SFTrue_SFFalse_lem_res:
  andb3_rel SFTrue_u SFTrue_u SFFalse_u andb3_SFTrue_SFTrue_SFFalse_lem_res
  ↔ andb3_SFTrue_SFTrue_SFFalse_lem_res == SFFalse_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite andb3_SFTrue_SFTrue_SFFalse_lem: f_rel_back.

Theorem andb3_SFTrue_SFTrue_SFTrue_lem andb3_SFTrue_SFTrue_SFTrue_lem_res:
  andb3_rel SFTrue_u SFTrue_u SFTrue_u andb3_SFTrue_SFTrue_SFTrue_lem_res
  ↔ andb3_SFTrue_SFTrue_SFTrue_lem_res == SFTrue_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite andb3_SFTrue_SFTrue_SFTrue_lem: f_rel_back.

Theorem andb3_rel_ex
  (ds_d3iD : SFBool_u)
  (ds_d3iD_p : SFBool_wf ds_d3iD ∧ True)
  (ds_d3iE : SFBool_u)
  (ds_d3iE_p : SFBool_wf ds_d3iE ∧ True)
  (ds_d3iF : SFBool_u)
  (ds_d3iF_p : SFBool_wf ds_d3iF ∧ True):
  andb3_rel
  ds_d3iD
  ds_d3iE
  ds_d3iF
  ⌊ andb3 (exist _ ds_d3iD ds_d3iD_p) (exist _ ds_d3iE ds_d3iE_p) (exist _ ds_d3iF ds_d3iF_p) -⌋.
Proof.
  Opaque andb3.
  existence_lemma_pre andb3;
  destruct ds_d3iD as [|];
  [fix_notations |
   destruct ds_d3iE as [|];
   [fix_notations |
    destruct ds_d3iF as [|];
    [fix_notations | fix_notations]]];
  simpl in *.
  Transparent andb3.
  all: (existence_lemma_quicksolve andb3; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve andb3_rel_ex: rel_ax_db.

#[global] Opaque andb3.

Theorem andb3__andb3_rel_rw
  (ds_d3iD : SFBool_u)
  (ds_d3iD_p : SFBool_wf ds_d3iD ∧ True)
  (ds_d3iE : SFBool_u)
  (ds_d3iE_p : SFBool_wf ds_d3iE ∧ True)
  (ds_d3iF : SFBool_u)
  (ds_d3iF_p : SFBool_wf ds_d3iF ∧ True)
  (VV : SFBool_u):
  ⌊ andb3 (exist _ ds_d3iD ds_d3iD_p) (exist _ ds_d3iE ds_d3iE_p) (exist _ ds_d3iF ds_d3iF_p) -⌋ = VV
  ↔ andb3_rel ds_d3iD ds_d3iE ds_d3iF VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite andb3__andb3_rel_rw: f_rel_funct_db.

#[global] Hint Resolve andb3__andb3_rel_rw: rel_ax_db.

#[global] Instance andb3_lookup_rw: dictionary rwLem andb3 := { lookup' := andb3__andb3_rel_rw }.

Theorem andb3__andb3_rel (ds_d3iD ds_d3iE ds_d3iF : SFBool) (VV : SFBool_u):
  ⌊ andb3 ds_d3iD ds_d3iE ds_d3iF -⌋ = VV ↔ andb3_rel ⌊ ds_d3iD ⌋ ⌊ ds_d3iE ⌋ ⌊ ds_d3iF ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite andb3__andb3_rel: f_rel_funct_db.

Theorem andb3__andb3_rel'
  (ds_d3iD_u ds_d3iE_u ds_d3iF_u : SFBool_u) (ds_d3iD ds_d3iE ds_d3iF : SFBool) (VV : SFBool_u):
  ds_d3iD_u = ⌊ ds_d3iD ⌋
  → (ds_d3iE_u = ⌊ ds_d3iE ⌋
     → (ds_d3iF_u = ⌊ ds_d3iF ⌋
        → ⌊ andb3 ds_d3iD ds_d3iE ds_d3iF -⌋ = VV ↔ andb3_rel ds_d3iD_u ds_d3iE_u ds_d3iF_u VV)).
Proof.
  intros -> -> ->. refine (andb3__andb3_rel ds_d3iD ds_d3iE ds_d3iF VV).
Qed.

#[global] Hint Resolve andb3__andb3_rel': f_rel_funct_db.

Theorem andb3_rel_mk
  (ds_d3iD : SFBool_u)
  (ds_d3iD_p : SFBool_wf ds_d3iD ∧ True)
  (ds_d3iE : SFBool_u)
  (ds_d3iE_p : SFBool_wf ds_d3iE ∧ True)
  (ds_d3iF : SFBool_u)
  (ds_d3iF_p : SFBool_wf ds_d3iF ∧ True):
  {VV: _ | andb3_rel ds_d3iD ds_d3iE ds_d3iF VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, andb3_rel ds_d3iD ds_d3iE ds_d3iF VV)
          (andb3 (exist _ ds_d3iD ds_d3iD_p) (exist _ ds_d3iE ds_d3iE_p) (exist _ ds_d3iF ds_d3iF_p))
          _);
  rewrite <- andb3__andb3_rel';
  quicksolve.
Qed.

#[global] Hint Resolve andb3_rel_mk: f_rel_funct_db.

#[global] Instance andb3_pack:
  @Pack
  (SFBool
   ::RT λ (ds_d3iD : SFBool),
        SFBool ::RT λ (ds_d3iE : SFBool), SFBool ::RT λ (ds_d3iF : SFBool), nilRT)
  (SFBool_u ::UT (SFBool_u ::UT (SFBool_u ::UT nilUT)))
  ltac:(mkProjectsArgListTG ((SFBool
  ::RT λ (ds_d3iD : SFBool),
       SFBool
       ::RT λ (ds_d3iE : SFBool),
            SFBool ::RT λ (ds_d3iF : SFBool), nilRT)) ((SFBool_u ::UT (SFBool_u ::UT (SFBool_u ::UT nilUT)))))
  SFBool_u
  (λ (x_77734775 : ArgList (SFBool
                            ::RT λ (ds_d3iD : SFBool),
                                 SFBool ::RT λ (ds_d3iE : SFBool), SFBool ::RT λ (ds_d3iF : SFBool), nilRT))
     (v_x_77734775 : SFBool_u),
   ltac:(flattenP (λ (ds_d3iD ds_d3iE ds_d3iF : SFBool) (VV : SFBool_u),
 SFBool_wf VV ∧ True) x_77734775 v_x_77734775)).
Proof.
  buildPackG andb3 andb3_rel andb3__andb3_rel andb3_rel_funct.
Defined.

#[global] Instance andb3_upack:
  @uPack (SFBool_u ::UT (SFBool_u ::UT (SFBool_u ::UT nilUT))) SFBool_u.
Proof.
  buildUPackG andb3_rel andb3_rel_funct.
Defined.

Definition test_andb31_spec : Type :=
  {{∃ (andb3_res : SFBool_u),
    andb3_rel SFTrue_u SFTrue_u SFTrue_u andb3_res ∧ andb3_res == SFTrue_u}}.

#[global] Hint Unfold test_andb31_spec: lia_unfold.

Theorem test_andb31 : test_andb31_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (andb3_res : SFBool_u), andb3_rel SFTrue_u SFTrue_u SFTrue_u andb3_res ∧ andb3_res == SFTrue_u)
          (# unit)
          ltac:(solver)).
Qed.

Definition test_andb32_spec : Type :=
  {{∃ (andb3_res : SFBool_u),
    andb3_rel SFFalse_u SFTrue_u SFTrue_u andb3_res ∧ andb3_res == SFFalse_u}}.

#[global] Hint Unfold test_andb32_spec: lia_unfold.

Theorem test_andb32 : test_andb32_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (andb3_res : SFBool_u), andb3_rel SFFalse_u SFTrue_u SFTrue_u andb3_res ∧ andb3_res == SFFalse_u)
          (# unit)
          ltac:(solver)).
Qed.

Definition test_andb33_spec : Type :=
  {{∃ (andb3_res : SFBool_u),
    andb3_rel SFTrue_u SFFalse_u SFTrue_u andb3_res ∧ andb3_res == SFFalse_u}}.

#[global] Hint Unfold test_andb33_spec: lia_unfold.

Theorem test_andb33 : test_andb33_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (andb3_res : SFBool_u), andb3_rel SFTrue_u SFFalse_u SFTrue_u andb3_res ∧ andb3_res == SFFalse_u)
          (# unit)
          ltac:(solver)).
Qed.

Definition test_andb34_spec : Type :=
  {{∃ (andb3_res : SFBool_u),
    andb3_rel SFTrue_u SFTrue_u SFFalse_u andb3_res ∧ andb3_res == SFFalse_u}}.

#[global] Hint Unfold test_andb34_spec: lia_unfold.

Theorem test_andb34 : test_andb34_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (andb3_res : SFBool_u), andb3_rel SFTrue_u SFTrue_u SFFalse_u andb3_res ∧ andb3_res == SFFalse_u)
          (# unit)
          ltac:(solver)).
Qed.

Definition andb_commutative_spec (ds_d3hC ds_d3hD : SFBool): Type :=
  {{∃ (andb_res : SFBool_u),
    andb_rel ⌊ ds_d3hC ⌋ ⌊ ds_d3hD ⌋ andb_res
    ∧ ∃ (andb_res_2 : SFBool_u),
      andb_rel ⌊ ds_d3hD ⌋ ⌊ ds_d3hC ⌋ andb_res_2 ∧ andb_res == andb_res_2}}.

#[global] Hint Unfold andb_commutative_spec: lia_unfold.

Theorem andb_commutative (ds_d3hC ds_d3hD : SFBool): andb_commutative_spec ds_d3hC ds_d3hD.
Proof.
  destruct ds_d3hC as [ds_d3hC ds_d3hC_p].
  destruct ds_d3hD as [ds_d3hD ds_d3hD_p].
  destruct ds_d3hC as [|].
  - destruct ds_d3hD as [|].
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∃ (andb_res : SFBool_u), andb_rel SFFalse_u SFFalse_u andb_res ∧ andb_res == andb_res)
              (# unit)
              ltac:(solver)).
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∃ (andb_res : SFBool_u),
               andb_rel SFFalse_u SFTrue_u andb_res
               ∧ ∃ (andb_res_2 : SFBool_u), andb_rel SFTrue_u SFFalse_u andb_res_2 ∧ andb_res == andb_res_2)
              (# unit)
              ltac:(solver)).
  - destruct ds_d3hD as [|].
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∃ (andb_res : SFBool_u),
               andb_rel SFTrue_u SFFalse_u andb_res
               ∧ ∃ (andb_res_2 : SFBool_u), andb_rel SFFalse_u SFTrue_u andb_res_2 ∧ andb_res == andb_res_2)
              (# unit)
              ltac:(solver)).
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit), ∃ (andb_res : SFBool_u), andb_rel SFTrue_u SFTrue_u andb_res ∧ andb_res == andb_res)
              (# unit)
              ltac:(solver)).
Qed.

Definition andb_true_elim2_spec
  (ds_d3hz ds_d3hA : SFBool)
  (ds_d3hB : {{∃ (andb_res : SFBool_u),
               andb_rel ⌊ ds_d3hz ⌋ ⌊ ds_d3hA ⌋ andb_res ∧ andb_res == SFTrue_u}}):
  Type :=
  {{⌊ ds_d3hA ⌋ == SFTrue_u}}.

#[global] Hint Unfold andb_true_elim2_spec: lia_unfold.

Theorem andb_true_elim2
  (ds_d3hz ds_d3hA : SFBool)
  (ds_d3hB : {{∃ (andb_res : SFBool_u),
               andb_rel ⌊ ds_d3hz ⌋ ⌊ ds_d3hA ⌋ andb_res ∧ andb_res == SFTrue_u}}):
  andb_true_elim2_spec ds_d3hz ds_d3hA ds_d3hB.
Proof.
  destruct ds_d3hz as [ds_d3hz ds_d3hz_p].
  destruct ds_d3hA as [ds_d3hA ds_d3hA_p].
  destruct ds_d3hB as [ds_d3hB ds_d3hB_p].
  destruct ds_d3hz as [|].
  - destruct ds_d3hA as [|].
    + refine (subsumptionCast Unit (λ (VV : Unit), SFFalse_u == SFTrue_u) (# unit) ltac:(solver)).
    + refine (subsumptionCast Unit (λ (VV : Unit), SFTrue_u == SFTrue_u) (# unit) ltac:(solver)).
  - destruct ds_d3hA as [|].
    + refine (subsumptionCast Unit (λ (VV : Unit), SFFalse_u == SFTrue_u) (# unit) ltac:(solver)).
    + refine (subsumptionCast Unit (λ (VV : Unit), SFTrue_u == SFTrue_u) (# unit) ltac:(solver)).
Qed.

Definition identity_fn_applied_twice_spec
  (f : @Pack
       (SFBool ::RT λ (lq_tmp0 : SFBool), nilRT)
       (SFBool_u ::UT nilUT)
       ltac:(mkProjectsArgListTG ((SFBool ::RT λ (lq_tmp0 : SFBool), nilRT)) ((SFBool_u ::UT nilUT)))
       SFBool_u
       (λ (x_80611037 : ArgList (SFBool ::RT λ (lq_tmp0 : SFBool), nilRT)) (v_x_80611037 : SFBool_u),
        ltac:(flattenP (λ (lq_tmp0 : SFBool) (VV : SFBool_u), SFBool_wf VV ∧ True) x_80611037 v_x_80611037)))
  (h : @Pack
       (SFBool ::RT λ (x : SFBool), nilRT)
       (SFBool_u ::UT nilUT)
       ltac:(mkProjectsArgListTG ((SFBool ::RT λ (x : SFBool), nilRT)) ((SFBool_u ::UT nilUT)))
       Unit
       (λ (x_44180694 : ArgList (SFBool ::RT λ (x : SFBool), nilRT)) (v_x_44180694 : Unit),
        ltac:(flattenP (λ (x : SFBool) (VV : Unit),
 ∃ (f_res : SFBool_u), getPackRel f ⌊ x ⌋ f_res ∧ f_res == ⌊ x ⌋) x_44180694 v_x_44180694)))
  (b : SFBool):
  Type :=
  {{∃ (f_res : SFBool_u),
    getPackRel f ⌊ b ⌋ f_res ∧ ∃ (f_res_2 : SFBool_u), getPackRel f f_res f_res_2 ∧ f_res_2 == ⌊ b ⌋}}.

#[global] Hint Unfold identity_fn_applied_twice_spec: lia_unfold.

Theorem identity_fn_applied_twice
  (f : @Pack
       (SFBool ::RT λ (lq_tmp0 : SFBool), nilRT)
       (SFBool_u ::UT nilUT)
       ltac:(mkProjectsArgListTG ((SFBool ::RT λ (lq_tmp0 : SFBool), nilRT)) ((SFBool_u ::UT nilUT)))
       SFBool_u
       (λ (x_80611037 : ArgList (SFBool ::RT λ (lq_tmp0 : SFBool), nilRT)) (v_x_80611037 : SFBool_u),
        ltac:(flattenP (λ (lq_tmp0 : SFBool) (VV : SFBool_u), SFBool_wf VV ∧ True) x_80611037 v_x_80611037)))
  (h : @Pack
       (SFBool ::RT λ (x : SFBool), nilRT)
       (SFBool_u ::UT nilUT)
       ltac:(mkProjectsArgListTG ((SFBool ::RT λ (x : SFBool), nilRT)) ((SFBool_u ::UT nilUT)))
       Unit
       (λ (x_44180694 : ArgList (SFBool ::RT λ (x : SFBool), nilRT)) (v_x_44180694 : Unit),
        ltac:(flattenP (λ (x : SFBool) (VV : Unit),
 ∃ (f_res : SFBool_u), getPackRel f ⌊ x ⌋ f_res ∧ f_res == ⌊ x ⌋) x_44180694 v_x_44180694)))
  (b : SFBool):
  identity_fn_applied_twice_spec f h b.
Proof.
  destruct b as [b b_p].
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (f_res : SFBool_u),
           getPackRel f b f_res ∧ ∃ (f_res_2 : SFBool_u), getPackRel f f_res f_res_2 ∧ f_res_2 == b)
          (let _: True :=
           ⌈ # unit ⌉ in
           let _: VV == ⌊ getPackF f (exist (λ (b : SFBool_u), SFBool_wf b ∧ True) b ltac:(solver)) ⌋
                  ∧ VV
                    == ⌊ getPackF f (getPackF f (exist (λ (b : SFBool_u), SFBool_wf b ∧ True) b ltac:(solver))) ⌋ :=
           ⌈ let _: True :=
             ⌈ let _: ∃ (f_res : SFBool_u), getPackRel f b f_res ∧ f_res == b :=
               ⌈ getPackF h (exist (λ (b : SFBool_u), SFBool_wf b ∧ True) b ltac:(solver)) ⌉ in
               let _: ⌊ getPackF h (getPackF f (exist (λ (b : SFBool_u), SFBool_wf b ∧ True) b ltac:(solver))) ⌋
                      == b :=
               ltac:(solver) in
               exist (λ (b : SFBool_u), SFBool_wf b ∧ True) b ltac:(solver) ⌉ in
             let _: ⌊ getPackF f (getPackF f (exist (λ (b : SFBool_u), SFBool_wf b ∧ True) b ltac:(solver))) ⌋
                    == ⌊ getPackF f (exist (λ (b : SFBool_u), SFBool_wf b ∧ True) b ltac:(solver)) ⌋ :=
             ltac:(solver) in
             subsumptionCast
             SFBool_u
             (λ (VV : SFBool_u),
              SFBool_wf VV
              ∧ VV == ⌊ getPackF f (getPackF f (exist (λ (b : SFBool_u), SFBool_wf b ∧ True) b ltac:(solver))) ⌋)
             (getPackF f (exist (λ (b : SFBool_u), SFBool_wf b ∧ True) b ltac:(solver)))
             ltac:(solver) ⌉ in
           # unit)
          ltac:(solver)).
Qed.

Definition nandb_spec (ds_d3iK ds_d3iL : SFBool): Type :=
  SFBool.

#[global] Hint Unfold nandb_spec: lia_unfold.

Definition nandb (ds_d3iK ds_d3iL : SFBool): nandb_spec ds_d3iK ds_d3iL.
Proof.
  destruct ds_d3iK as [ds_d3iK ds_d3iK_p].
  destruct ds_d3iL as [ds_d3iL ds_d3iL_p].
  destruct ds_d3iK as [|].
  - refine SFTrue.
  - destruct ds_d3iL as [|].
    + refine SFTrue.
    + refine SFFalse.
Defined.

Inductive nandb_rel: SFBool_u → SFBool_u → SFBool_u → Prop :=
  | nandb_SFFalse_x: ∀ ds_d3iL, nandb_rel SFFalse_u ds_d3iL SFTrue_u
  | nandb_SFTrue_SFFalse: nandb_rel SFTrue_u SFFalse_u SFTrue_u
  | nandb_SFTrue_SFTrue: nandb_rel SFTrue_u SFTrue_u SFFalse_u.

#[global] Hint Constructors nandb_rel: core_hint_db.

#[global] Instance nandb_lookup_rel: dictionary rel nandb := { lookup' := nandb_rel }.

#[global] Instance nandb_getF: getFunc nandb_rel := { getF' := nandb }.

Theorem nandb_rel_funct [ds_d3iK ds_d3iL : SFBool_u]:
  ∀ (VV VV' : SFBool_u), nandb_rel ds_d3iK ds_d3iL VV → (nandb_rel ds_d3iK ds_d3iL VV' → VV = VV').
Proof.
  destruct ds_d3iK as [|];
  [ | destruct ds_d3iL as [|]];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve nandb_rel_funct: f_rel_funct_db.

Theorem nandb_SFFalse_x_lem ds_d3iL nandb_SFFalse_x_lem_res:
  nandb_rel SFFalse_u ds_d3iL nandb_SFFalse_x_lem_res ↔ nandb_SFFalse_x_lem_res == SFTrue_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite nandb_SFFalse_x_lem: f_rel_back.

Theorem nandb_SFTrue_SFFalse_lem nandb_SFTrue_SFFalse_lem_res:
  nandb_rel SFTrue_u SFFalse_u nandb_SFTrue_SFFalse_lem_res
  ↔ nandb_SFTrue_SFFalse_lem_res == SFTrue_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite nandb_SFTrue_SFFalse_lem: f_rel_back.

Theorem nandb_SFTrue_SFTrue_lem nandb_SFTrue_SFTrue_lem_res:
  nandb_rel SFTrue_u SFTrue_u nandb_SFTrue_SFTrue_lem_res ↔ nandb_SFTrue_SFTrue_lem_res == SFFalse_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite nandb_SFTrue_SFTrue_lem: f_rel_back.

Theorem nandb_rel_ex
  (ds_d3iK : SFBool_u)
  (ds_d3iK_p : SFBool_wf ds_d3iK ∧ True)
  (ds_d3iL : SFBool_u)
  (ds_d3iL_p : SFBool_wf ds_d3iL ∧ True):
  nandb_rel ds_d3iK ds_d3iL ⌊ nandb (exist _ ds_d3iK ds_d3iK_p) (exist _ ds_d3iL ds_d3iL_p) -⌋.
Proof.
  Opaque nandb.
  existence_lemma_pre nandb;
  destruct ds_d3iK as [|];
  [fix_notations |
   destruct ds_d3iL as [|];
   [fix_notations | fix_notations]];
  simpl in *.
  Transparent nandb.
  all: (existence_lemma_quicksolve nandb; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve nandb_rel_ex: rel_ax_db.

#[global] Opaque nandb.

Theorem nandb__nandb_rel_rw
  (ds_d3iK : SFBool_u)
  (ds_d3iK_p : SFBool_wf ds_d3iK ∧ True)
  (ds_d3iL : SFBool_u)
  (ds_d3iL_p : SFBool_wf ds_d3iL ∧ True)
  (VV : SFBool_u):
  ⌊ nandb (exist _ ds_d3iK ds_d3iK_p) (exist _ ds_d3iL ds_d3iL_p) -⌋ = VV
  ↔ nandb_rel ds_d3iK ds_d3iL VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite nandb__nandb_rel_rw: f_rel_funct_db.

#[global] Hint Resolve nandb__nandb_rel_rw: rel_ax_db.

#[global] Instance nandb_lookup_rw: dictionary rwLem nandb := { lookup' := nandb__nandb_rel_rw }.

Theorem nandb__nandb_rel (ds_d3iK ds_d3iL : SFBool) (VV : SFBool_u):
  ⌊ nandb ds_d3iK ds_d3iL -⌋ = VV ↔ nandb_rel ⌊ ds_d3iK ⌋ ⌊ ds_d3iL ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite nandb__nandb_rel: f_rel_funct_db.

Theorem nandb__nandb_rel'
  (ds_d3iK_u ds_d3iL_u : SFBool_u) (ds_d3iK ds_d3iL : SFBool) (VV : SFBool_u):
  ds_d3iK_u = ⌊ ds_d3iK ⌋
  → (ds_d3iL_u = ⌊ ds_d3iL ⌋ → ⌊ nandb ds_d3iK ds_d3iL -⌋ = VV ↔ nandb_rel ds_d3iK_u ds_d3iL_u VV).
Proof.
  intros -> ->. refine (nandb__nandb_rel ds_d3iK ds_d3iL VV).
Qed.

#[global] Hint Resolve nandb__nandb_rel': f_rel_funct_db.

Theorem nandb_rel_mk
  (ds_d3iK : SFBool_u)
  (ds_d3iK_p : SFBool_wf ds_d3iK ∧ True)
  (ds_d3iL : SFBool_u)
  (ds_d3iL_p : SFBool_wf ds_d3iL ∧ True):
  {VV: _ | nandb_rel ds_d3iK ds_d3iL VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, nandb_rel ds_d3iK ds_d3iL VV)
          (nandb (exist _ ds_d3iK ds_d3iK_p) (exist _ ds_d3iL ds_d3iL_p))
          _);
  rewrite <- nandb__nandb_rel';
  quicksolve.
Qed.

#[global] Hint Resolve nandb_rel_mk: f_rel_funct_db.

#[global] Instance nandb_pack:
  @Pack
  (SFBool ::RT λ (ds_d3iK : SFBool), SFBool ::RT λ (ds_d3iL : SFBool), nilRT)
  (SFBool_u ::UT (SFBool_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((SFBool
  ::RT λ (ds_d3iK : SFBool),
       SFBool ::RT λ (ds_d3iL : SFBool), nilRT)) ((SFBool_u ::UT (SFBool_u ::UT nilUT))))
  SFBool_u
  (λ (x_38598083 : ArgList (SFBool
                            ::RT λ (ds_d3iK : SFBool), SFBool ::RT λ (ds_d3iL : SFBool), nilRT))
     (v_x_38598083 : SFBool_u),
   ltac:(flattenP (λ (ds_d3iK ds_d3iL : SFBool) (VV : SFBool_u), SFBool_wf VV ∧ True) x_38598083 v_x_38598083)).
Proof.
  buildPackG nandb nandb_rel nandb__nandb_rel nandb_rel_funct.
Defined.

#[global] Instance nandb_upack: @uPack (SFBool_u ::UT (SFBool_u ::UT nilUT)) SFBool_u.
Proof.
  buildUPackG nandb_rel nandb_rel_funct.
Defined.

Definition test_nandb1_spec : Type :=
  {{∃ (nandb_res : SFBool_u), nandb_rel SFTrue_u SFFalse_u nandb_res ∧ nandb_res == SFTrue_u}}.

#[global] Hint Unfold test_nandb1_spec: lia_unfold.

Theorem test_nandb1 : test_nandb1_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (nandb_res : SFBool_u), nandb_rel SFTrue_u SFFalse_u nandb_res ∧ nandb_res == SFTrue_u)
          (# unit)
          ltac:(solver)).
Qed.

Definition test_nandb2_spec : Type :=
  {{∃ (nandb_res : SFBool_u), nandb_rel SFFalse_u SFFalse_u nandb_res ∧ nandb_res == SFTrue_u}}.

#[global] Hint Unfold test_nandb2_spec: lia_unfold.

Theorem test_nandb2 : test_nandb2_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (nandb_res : SFBool_u), nandb_rel SFFalse_u SFFalse_u nandb_res ∧ nandb_res == SFTrue_u)
          (# unit)
          ltac:(solver)).
Qed.

Definition test_nandb3_spec : Type :=
  {{∃ (nandb_res : SFBool_u), nandb_rel SFFalse_u SFTrue_u nandb_res ∧ nandb_res == SFTrue_u}}.

#[global] Hint Unfold test_nandb3_spec: lia_unfold.

Theorem test_nandb3 : test_nandb3_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (nandb_res : SFBool_u), nandb_rel SFFalse_u SFTrue_u nandb_res ∧ nandb_res == SFTrue_u)
          (# unit)
          ltac:(solver)).
Qed.

Definition test_nandb4_spec : Type :=
  {{∃ (nandb_res : SFBool_u), nandb_rel SFTrue_u SFTrue_u nandb_res ∧ nandb_res == SFFalse_u}}.

#[global] Hint Unfold test_nandb4_spec: lia_unfold.

Theorem test_nandb4 : test_nandb4_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (nandb_res : SFBool_u), nandb_rel SFTrue_u SFTrue_u nandb_res ∧ nandb_res == SFFalse_u)
          (# unit)
          ltac:(solver)).
Qed.

Definition negb_spec (ds_d3iS : SFBool): Type :=
  SFBool.

#[global] Hint Unfold negb_spec: lia_unfold.

Definition negb (ds_d3iS : SFBool): negb_spec ds_d3iS.
Proof.
  destruct ds_d3iS as [ds_d3iS ds_d3iS_p].
  destruct ds_d3iS as [|].
  - refine SFTrue.
  - refine SFFalse.
Defined.

Inductive negb_rel: SFBool_u → SFBool_u → Prop :=
  | negb_SFFalse: negb_rel SFFalse_u SFTrue_u | negb_SFTrue: negb_rel SFTrue_u SFFalse_u.

#[global] Hint Constructors negb_rel: core_hint_db.

#[global] Instance negb_lookup_rel: dictionary rel negb := { lookup' := negb_rel }.

#[global] Instance negb_getF: getFunc negb_rel := { getF' := negb }.

Theorem negb_rel_funct [ds_d3iS : SFBool_u]:
  ∀ (VV VV' : SFBool_u), negb_rel ds_d3iS VV → (negb_rel ds_d3iS VV' → VV = VV').
Proof.
  destruct ds_d3iS as [|]; rel_functionhood_body.
Qed.

#[global] Hint Resolve negb_rel_funct: f_rel_funct_db.

Theorem negb_SFFalse_lem negb_SFFalse_lem_res:
  negb_rel SFFalse_u negb_SFFalse_lem_res ↔ negb_SFFalse_lem_res == SFTrue_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite negb_SFFalse_lem: f_rel_back.

Theorem negb_SFTrue_lem negb_SFTrue_lem_res:
  negb_rel SFTrue_u negb_SFTrue_lem_res ↔ negb_SFTrue_lem_res == SFFalse_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite negb_SFTrue_lem: f_rel_back.

Theorem negb_rel_ex (ds_d3iS : SFBool_u) (ds_d3iS_p : SFBool_wf ds_d3iS ∧ True):
  negb_rel ds_d3iS ⌊ negb (exist _ ds_d3iS ds_d3iS_p) -⌋.
Proof.
  Opaque negb.
  existence_lemma_pre negb;
  destruct ds_d3iS as [|];
  [fix_notations | fix_notations];
  simpl in *.
  Transparent negb.
  all: (existence_lemma_quicksolve negb; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve negb_rel_ex: rel_ax_db.

#[global] Opaque negb.

Theorem negb__negb_rel_rw
  (ds_d3iS : SFBool_u) (ds_d3iS_p : SFBool_wf ds_d3iS ∧ True) (VV : SFBool_u):
  ⌊ negb (exist _ ds_d3iS ds_d3iS_p) -⌋ = VV ↔ negb_rel ds_d3iS VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite negb__negb_rel_rw: f_rel_funct_db.

#[global] Hint Resolve negb__negb_rel_rw: rel_ax_db.

#[global] Instance negb_lookup_rw: dictionary rwLem negb := { lookup' := negb__negb_rel_rw }.

Theorem negb__negb_rel (ds_d3iS : SFBool) (VV : SFBool_u):
  ⌊ negb ds_d3iS -⌋ = VV ↔ negb_rel ⌊ ds_d3iS ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite negb__negb_rel: f_rel_funct_db.

Theorem negb__negb_rel' (ds_d3iS_u : SFBool_u) (ds_d3iS : SFBool) (VV : SFBool_u):
  ds_d3iS_u = ⌊ ds_d3iS ⌋ → ⌊ negb ds_d3iS -⌋ = VV ↔ negb_rel ds_d3iS_u VV.
Proof.
  intros ->. refine (negb__negb_rel ds_d3iS VV).
Qed.

#[global] Hint Resolve negb__negb_rel': f_rel_funct_db.

Theorem negb_rel_mk (ds_d3iS : SFBool_u) (ds_d3iS_p : SFBool_wf ds_d3iS ∧ True):
  {VV: _ | negb_rel ds_d3iS VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, negb_rel ds_d3iS VV) (negb (exist _ ds_d3iS ds_d3iS_p)) _);
  rewrite <- negb__negb_rel';
  quicksolve.
Qed.

#[global] Hint Resolve negb_rel_mk: f_rel_funct_db.

#[global] Instance negb_pack:
  @Pack
  (SFBool ::RT λ (ds_d3iS : SFBool), nilRT)
  (SFBool_u ::UT nilUT)
  ltac:(mkProjectsArgListTG ((SFBool ::RT λ (ds_d3iS : SFBool), nilRT)) ((SFBool_u ::UT nilUT)))
  SFBool_u
  (λ (x_70267813 : ArgList (SFBool ::RT λ (ds_d3iS : SFBool), nilRT)) (v_x_70267813 : SFBool_u),
   ltac:(flattenP (λ (ds_d3iS : SFBool) (VV : SFBool_u), SFBool_wf VV ∧ True) x_70267813 v_x_70267813)).
Proof.
  buildPackG negb negb_rel negb__negb_rel negb_rel_funct.
Defined.

#[global] Instance negb_upack: @uPack (SFBool_u ::UT nilUT) SFBool_u.
Proof.
  buildUPackG negb_rel negb_rel_funct.
Defined.

Definition negb'_spec (b : SFBool): Type :=
  SFBool.

#[global] Hint Unfold negb'_spec: lia_unfold.

Definition negb' (b : SFBool): negb'_spec b.
Proof.
  destruct b as [b b_p].
  let E := fresh "E" in destruct (b ==? SFTrue_u) as [|] eqn:E;
  [refine SFFalse | refine SFTrue].
Defined.

Definition negb_involutive_spec (ds_d3hE : SFBool): Type :=
  {{∃ (negb_res : SFBool_u),
    negb_rel ⌊ ds_d3hE ⌋ negb_res
    ∧ ∃ (negb_res_2 : SFBool_u), negb_rel negb_res negb_res_2 ∧ negb_res_2 == ⌊ ds_d3hE ⌋}}.

#[global] Hint Unfold negb_involutive_spec: lia_unfold.

Theorem negb_involutive (ds_d3hE : SFBool): negb_involutive_spec ds_d3hE.
Proof.
  destruct ds_d3hE as [ds_d3hE ds_d3hE_p].
  destruct ds_d3hE as [|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (negb_res : SFBool_u),
             negb_rel SFFalse_u negb_res
             ∧ ∃ (negb_res_2 : SFBool_u), negb_rel negb_res negb_res_2 ∧ negb_res_2 == SFFalse_u)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (negb_res : SFBool_u),
             negb_rel SFTrue_u negb_res
             ∧ ∃ (negb_res_2 : SFBool_u), negb_rel negb_res negb_res_2 ∧ negb_res_2 == SFTrue_u)
            (# unit)
            ltac:(solver)).
Qed.

Definition orb_spec (b1 b2 : SFBool): Type :=
  SFBool.

#[global] Hint Unfold orb_spec: lia_unfold.

Definition orb (b1 b2 : SFBool): orb_spec b1 b2.
Proof.
  destruct b1 as [b1 b1_p].
  destruct b2 as [b2 b2_p].
  destruct b1 as [|].
  - refine (exist (λ (b2 : SFBool_u), SFBool_wf b2 ∧ True) b2 ltac:(solver)).
  - refine SFTrue.
Defined.

Inductive orb_rel: SFBool_u → SFBool_u → SFBool_u → Prop :=
  | orb_SFFalse_x: ∀ b2, orb_rel SFFalse_u b2 b2 | orb_SFTrue_x: ∀ b2, orb_rel SFTrue_u b2 SFTrue_u.

#[global] Hint Constructors orb_rel: core_hint_db.

#[global] Instance orb_lookup_rel: dictionary rel orb := { lookup' := orb_rel }.

#[global] Instance orb_getF: getFunc orb_rel := { getF' := orb }.

Theorem orb_rel_funct [b1 b2 : SFBool_u]:
  ∀ (VV VV' : SFBool_u), orb_rel b1 b2 VV → (orb_rel b1 b2 VV' → VV = VV').
Proof.
  destruct b1 as [|]; rel_functionhood_body.
Qed.

#[global] Hint Resolve orb_rel_funct: f_rel_funct_db.

Theorem orb_SFFalse_x_lem b2 orb_SFFalse_x_lem_res:
  orb_rel SFFalse_u b2 orb_SFFalse_x_lem_res ↔ orb_SFFalse_x_lem_res == b2.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite orb_SFFalse_x_lem: f_rel_back.

Theorem orb_SFTrue_x_lem b2 orb_SFTrue_x_lem_res:
  orb_rel SFTrue_u b2 orb_SFTrue_x_lem_res ↔ orb_SFTrue_x_lem_res == SFTrue_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite orb_SFTrue_x_lem: f_rel_back.

Theorem orb_rel_ex
  (b1 : SFBool_u) (b1_p : SFBool_wf b1 ∧ True) (b2 : SFBool_u) (b2_p : SFBool_wf b2 ∧ True):
  orb_rel b1 b2 ⌊ orb (exist _ b1 b1_p) (exist _ b2 b2_p) -⌋.
Proof.
  Opaque orb.
  existence_lemma_pre orb;
  destruct b1 as [|];
  [fix_notations | fix_notations];
  simpl in *.
  Transparent orb.
  all: (existence_lemma_quicksolve orb; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve orb_rel_ex: rel_ax_db.

#[global] Opaque orb.

Theorem orb__orb_rel_rw
  (b1 : SFBool_u)
  (b1_p : SFBool_wf b1 ∧ True)
  (b2 : SFBool_u)
  (b2_p : SFBool_wf b2 ∧ True)
  (VV : SFBool_u):
  ⌊ orb (exist _ b1 b1_p) (exist _ b2 b2_p) -⌋ = VV ↔ orb_rel b1 b2 VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite orb__orb_rel_rw: f_rel_funct_db.

#[global] Hint Resolve orb__orb_rel_rw: rel_ax_db.

#[global] Instance orb_lookup_rw: dictionary rwLem orb := { lookup' := orb__orb_rel_rw }.

Theorem orb__orb_rel (b1 b2 : SFBool) (VV : SFBool_u):
  ⌊ orb b1 b2 -⌋ = VV ↔ orb_rel ⌊ b1 ⌋ ⌊ b2 ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite orb__orb_rel: f_rel_funct_db.

Theorem orb__orb_rel' (b1_u b2_u : SFBool_u) (b1 b2 : SFBool) (VV : SFBool_u):
  b1_u = ⌊ b1 ⌋ → (b2_u = ⌊ b2 ⌋ → ⌊ orb b1 b2 -⌋ = VV ↔ orb_rel b1_u b2_u VV).
Proof.
  intros -> ->. refine (orb__orb_rel b1 b2 VV).
Qed.

#[global] Hint Resolve orb__orb_rel': f_rel_funct_db.

Theorem orb_rel_mk
  (b1 : SFBool_u) (b1_p : SFBool_wf b1 ∧ True) (b2 : SFBool_u) (b2_p : SFBool_wf b2 ∧ True):
  {VV: _ | orb_rel b1 b2 VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, orb_rel b1 b2 VV) (orb (exist _ b1 b1_p) (exist _ b2 b2_p)) _);
  rewrite <- orb__orb_rel';
  quicksolve.
Qed.

#[global] Hint Resolve orb_rel_mk: f_rel_funct_db.

#[global] Instance orb_pack:
  @Pack
  (SFBool ::RT λ (b1 : SFBool), SFBool ::RT λ (b2 : SFBool), nilRT)
  (SFBool_u ::UT (SFBool_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((SFBool ::RT λ (b1 : SFBool), SFBool ::RT λ (b2 : SFBool), nilRT)) ((SFBool_u ::UT (SFBool_u ::UT nilUT))))
  SFBool_u
  (λ (x_89922389 : ArgList (SFBool ::RT λ (b1 : SFBool), SFBool ::RT λ (b2 : SFBool), nilRT))
     (v_x_89922389 : SFBool_u),
   ltac:(flattenP (λ (b1 b2 : SFBool) (VV : SFBool_u), SFBool_wf VV ∧ True) x_89922389 v_x_89922389)).
Proof.
  buildPackG orb orb_rel orb__orb_rel orb_rel_funct.
Defined.

#[global] Instance orb_upack: @uPack (SFBool_u ::UT (SFBool_u ::UT nilUT)) SFBool_u.
Proof.
  buildUPackG orb_rel orb_rel_funct.
Defined.

Definition andb_eq_orb_spec
  (ds_d3hv ds_d3hw : SFBool)
  (ds_d3hx : {{∃ (andb_res : SFBool_u),
               andb_rel ⌊ ds_d3hv ⌋ ⌊ ds_d3hw ⌋ andb_res
               ∧ ∃ (orb_res : SFBool_u), orb_rel ⌊ ds_d3hv ⌋ ⌊ ds_d3hw ⌋ orb_res ∧ andb_res == orb_res}}):
  Type :=
  {{⌊ ds_d3hv ⌋ == ⌊ ds_d3hw ⌋}}.

#[global] Hint Unfold andb_eq_orb_spec: lia_unfold.

Theorem andb_eq_orb
  (ds_d3hv ds_d3hw : SFBool)
  (ds_d3hx : {{∃ (andb_res : SFBool_u),
               andb_rel ⌊ ds_d3hv ⌋ ⌊ ds_d3hw ⌋ andb_res
               ∧ ∃ (orb_res : SFBool_u), orb_rel ⌊ ds_d3hv ⌋ ⌊ ds_d3hw ⌋ orb_res ∧ andb_res == orb_res}}):
  andb_eq_orb_spec ds_d3hv ds_d3hw ds_d3hx.
Proof.
  destruct ds_d3hv as [ds_d3hv ds_d3hv_p].
  destruct ds_d3hw as [ds_d3hw ds_d3hw_p].
  destruct ds_d3hx as [ds_d3hx ds_d3hx_p].
  destruct ds_d3hv as [|].
  - destruct ds_d3hw as [|].
    + refine (subsumptionCast Unit (λ (VV : Unit), SFFalse_u == SFFalse_u) (# unit) ltac:(solver)).
    + refine (subsumptionCast Unit (λ (VV : Unit), SFFalse_u == SFTrue_u) (# unit) ltac:(solver)).
  - destruct ds_d3hw as [|].
    + refine (subsumptionCast Unit (λ (VV : Unit), SFTrue_u == SFFalse_u) (# unit) ltac:(solver)).
    + refine (subsumptionCast Unit (λ (VV : Unit), SFTrue_u == SFTrue_u) (# unit) ltac:(solver)).
Qed.

Definition test_orb1_spec : Type :=
  {{∃ (orb_res : SFBool_u), orb_rel SFTrue_u SFFalse_u orb_res ∧ orb_res == SFTrue_u}}.

#[global] Hint Unfold test_orb1_spec: lia_unfold.

Theorem test_orb1 : test_orb1_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit), ∃ (orb_res : SFBool_u), orb_rel SFTrue_u SFFalse_u orb_res ∧ orb_res == SFTrue_u)
          (# unit)
          ltac:(solver)).
Qed.

Definition test_orb2_spec : Type :=
  {{∃ (orb_res : SFBool_u), orb_rel SFFalse_u SFFalse_u orb_res ∧ orb_res == SFFalse_u}}.

#[global] Hint Unfold test_orb2_spec: lia_unfold.

Theorem test_orb2 : test_orb2_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit), ∃ (orb_res : SFBool_u), orb_rel SFFalse_u SFFalse_u orb_res ∧ orb_res == SFFalse_u)
          (# unit)
          ltac:(solver)).
Qed.

Definition test_orb3_spec : Type :=
  {{∃ (orb_res : SFBool_u), orb_rel SFFalse_u SFTrue_u orb_res ∧ orb_res == SFTrue_u}}.

#[global] Hint Unfold test_orb3_spec: lia_unfold.

Theorem test_orb3 : test_orb3_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit), ∃ (orb_res : SFBool_u), orb_rel SFFalse_u SFTrue_u orb_res ∧ orb_res == SFTrue_u)
          (# unit)
          ltac:(solver)).
Qed.

Definition test_orb4_spec : Type :=
  {{∃ (orb_res : SFBool_u), orb_rel SFTrue_u SFTrue_u orb_res ∧ orb_res == SFTrue_u}}.

#[global] Hint Unfold test_orb4_spec: lia_unfold.

Theorem test_orb4 : test_orb4_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit), ∃ (orb_res : SFBool_u), orb_rel SFTrue_u SFTrue_u orb_res ∧ orb_res == SFTrue_u)
          (# unit)
          ltac:(solver)).
Qed.

Definition test_orb5_spec : Type :=
  {{∃ (orb_res : SFBool_u),
    orb_rel SFFalse_u SFTrue_u orb_res
    ∧ ∃ (orb_res_2 : SFBool_u), orb_rel SFFalse_u orb_res orb_res_2 ∧ orb_res_2 == SFTrue_u}}.

#[global] Hint Unfold test_orb5_spec: lia_unfold.

Theorem test_orb5 : test_orb5_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (orb_res : SFBool_u),
           orb_rel SFFalse_u SFTrue_u orb_res
           ∧ ∃ (orb_res_2 : SFBool_u), orb_rel SFFalse_u orb_res orb_res_2 ∧ orb_res_2 == SFTrue_u)
          (# unit)
          ltac:(solver)).
Qed.

Definition orb'_spec (b1 b2 : SFBool): Type :=
  SFBool.

#[global] Hint Unfold orb'_spec: lia_unfold.

Definition orb' (b1 b2 : SFBool): orb'_spec b1 b2.
Proof.
  destruct b1 as [b1 b1_p].
  destruct b2 as [b2 b2_p].
  let E := fresh "E" in destruct (b1 ==? SFTrue_u) as [|] eqn:E;
  [refine SFTrue | refine (exist (λ (b2 : SFBool_u), SFBool_wf b2 ∧ True) b2 ltac:(solver))].
Defined.

Inductive SFBit_u: Type :=
  | B0_u: SFBit_u | B1_u: SFBit_u.

Fixpoint SFBit_eq (x y : SFBit_u): bool :=
  match (x, y) with | (B0_u, B0_u) => true | (B1_u, B1_u) => true | (_, _) => false end.

Theorem SFBit_eq_refl : ∀ (x : SFBit_u), is_true (SFBit_eq x x).
Proof.
  eq_refl_rec.
Qed.

#[global] Hint Resolve SFBit_eq_refl: eq_hint_db.

Theorem SFBit_eqb_eq : ∀ (s t : SFBit_u), is_true (SFBit_eq s t) → s = t.
Proof.
  eqb_eq_lem.
Qed.

#[global] Hint Resolve SFBit_eqb_eq: eq_hint_db.

#[global] Instance leibnitz_eq_SFBit: LeibnitzEqB := {
    equalB' := SFBit_eq;
    refl' := SFBit_eq_refl;
    eqb_eq' := SFBit_eqb_eq }.

Fixpoint SFBit_wf (x : SFBit_u): Prop :=
  match x with | B0_u => True | B1_u => True end.

Theorem SFBit_wf_ref [p : SFBit_u → Prop] (tm : {v: SFBit_u | SFBit_wf v ∧ p v}): SFBit_wf ⌊ tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation SFBit := {x: SFBit_u | SFBit_wf x ∧ True}.

Definition B0_lem : SFBit_wf B0_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition B0 : SFBit :=
  exist _ B0_u B0_lem.

Definition B1_lem : SFBit_wf B1_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition B1 : SFBit :=
  exist _ B1_u B1_lem.

#[global] Hint Resolve SFBit_wf_ref: wf_constr_db.

#[global] Hint Unfold SFBit_wf: wf_constr_db.

#[global] Hint Resolve SFBit_eq: ref_constr_db.

#[global] Hint Unfold B0: ref_constr_db.

#[global] Hint Unfold B1: ref_constr_db.

Inductive SFBin_u: Type :=
  | Bin0_u: SFBin_u → SFBin_u | Bin1_u: SFBin_u → SFBin_u | Z_u: SFBin_u.

Fixpoint SFBin_eq (x y : SFBin_u): bool :=
  match (x, y) with
  | (Bin0_u n, Bin0_u n') => true && SFBin_eq n n'
  | (Bin1_u n, Bin1_u n') => true && SFBin_eq n n'
  | (Z_u, Z_u) => true
  | (_, _) => false
  end.

Theorem SFBin_eq_refl : ∀ (x : SFBin_u), is_true (SFBin_eq x x).
Proof.
  eq_refl_rec.
Qed.

#[global] Hint Resolve SFBin_eq_refl: eq_hint_db.

Theorem SFBin_eqb_eq : ∀ (s t : SFBin_u), is_true (SFBin_eq s t) → s = t.
Proof.
  eqb_eq_lem.
Qed.

#[global] Hint Resolve SFBin_eqb_eq: eq_hint_db.

#[global] Instance leibnitz_eq_SFBin: LeibnitzEqB := {
    equalB' := SFBin_eq;
    refl' := SFBin_eq_refl;
    eqb_eq' := SFBin_eqb_eq }.

Fixpoint SFBin_wf (x : SFBin_u): Prop :=
  match x with | Bin0_u n => SFBin_wf n ∧ True | Bin1_u n => SFBin_wf n ∧ True | Z_u => True end.

Theorem SFBin_wf_ref [p : SFBin_u → Prop] (tm : {v: SFBin_u | SFBin_wf v ∧ p v}): SFBin_wf ⌊ tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation SFBin := {x: SFBin_u | SFBin_wf x ∧ True}.

Definition Bin0_lem (n : SFBin): SFBin_wf (Bin0_u ⌊ n ⌋) ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Bin0 (n : SFBin): SFBin :=
  exist _ (Bin0_u ⌊ n ⌋) (Bin0_lem n).

Definition Bin1_lem (n : SFBin): SFBin_wf (Bin1_u ⌊ n ⌋) ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Bin1 (n : SFBin): SFBin :=
  exist _ (Bin1_u ⌊ n ⌋) (Bin1_lem n).

Definition Z_lem : SFBin_wf Z_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Z : SFBin :=
  exist _ Z_u Z_lem.

Definition wf_Bin0_n [n : SFBin_u] (p : SFBin_wf (Bin0_u n)): SFBin_wf n.
Proof.
  quicksolve.
Defined.

#[global] Hint Resolve wf_Bin0_n: ref_constr_db.

Definition wf_Bin1_n [n : SFBin_u] (p : SFBin_wf (Bin1_u n)): SFBin_wf n.
Proof.
  quicksolve.
Defined.

#[global] Hint Resolve wf_Bin1_n: ref_constr_db.

#[global] Hint Resolve SFBin_wf_ref: wf_constr_db.

#[global] Hint Unfold SFBin_wf: wf_constr_db.

#[global] Hint Resolve SFBin_eq: ref_constr_db.

#[global] Hint Unfold Bin0: ref_constr_db.

#[global] Hint Unfold Bin1: ref_constr_db.

#[global] Hint Unfold Z: ref_constr_db.

Definition bin_to_nat_spec (ds_d3gI : SFBin): Type :=
  {VV: Z | True}.

#[global] Hint Unfold bin_to_nat_spec: lia_unfold.

Definition bin_to_nat (ds_d3gI : SFBin): bin_to_nat_spec ds_d3gI.
Proof.
  destruct ds_d3gI as [ds_d3gI ds_d3gI_p].
  induction ds_d3gI as [m' IH_m'| m' IH_m'|].
  - refine (subsumptionCast
            Z
            (λ (VV : Z), True)
            (subsumptionCast Z (λ (x_1 : Z), True) (exist (λ (VV : Z), VV == 2) 2 ltac:(solver)) ltac:(solver)
             *Z IH_m' ltac:(try clear IH_m'; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Z
            (λ (VV : Z), True)
            (subsumptionCast Z (λ (x_1 : Z), True) (exist (λ (VV : Z), VV == 1) 1 ltac:(solver)) ltac:(solver)
             +Z subsumptionCast
                Z
                (λ (x_2 : Z), True)
                (subsumptionCast Z (λ (x_1 : Z), True) (exist (λ (VV : Z), VV == 2) 2 ltac:(solver)) ltac:(solver)
                 *Z IH_m' ltac:(try clear IH_m'; solver))
                ltac:(solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Z
            (λ (VV : Z), True)
            (exist (λ (VV : Z), VV == 0) 0 ltac:(solver))
            ltac:(solver)).
Defined.

Inductive bin_to_nat_rel: SFBin_u → Z → Prop :=
  | bin_to_nat_Bin0: ∀ m' (bin_to_nat_res : Z),
                     bin_to_nat_rel m' bin_to_nat_res
                     → ∀ (multZ_res : Z), multZ_rel 2 bin_to_nat_res multZ_res → bin_to_nat_rel (Bin0_u m') multZ_res
  | bin_to_nat_Bin1: ∀ m' (bin_to_nat_res : Z),
                     bin_to_nat_rel m' bin_to_nat_res
                     → ∀ (multZ_res : Z),
                       multZ_rel 2 bin_to_nat_res multZ_res
                       → ∀ (addZ_res : Z), addZ_rel 1 multZ_res addZ_res → bin_to_nat_rel (Bin1_u m') addZ_res
  | bin_to_nat_Z: bin_to_nat_rel Z_u 0.

#[global] Hint Constructors bin_to_nat_rel: core_hint_db.

#[global] Instance bin_to_nat_lookup_rel: dictionary rel bin_to_nat := {
    lookup' := bin_to_nat_rel }.

#[global] Instance bin_to_nat_getF: getFunc bin_to_nat_rel := { getF' := bin_to_nat }.

Theorem bin_to_nat_rel_funct [ds_d3gI : SFBin_u]:
  ∀ (VV VV' : Z), bin_to_nat_rel ds_d3gI VV → (bin_to_nat_rel ds_d3gI VV' → VV = VV').
Proof.
  induction ds_d3gI as [m' IH_m'| m' IH_m'|]; rel_functionhood_body.
Qed.

#[global] Hint Resolve bin_to_nat_rel_funct: f_rel_funct_db.

Theorem bin_to_nat_Bin0_lem m' bin_to_nat_Bin0_lem_res:
  bin_to_nat_rel (Bin0_u m') bin_to_nat_Bin0_lem_res
  ↔ ∃ (bin_to_nat_res : Z),
    bin_to_nat_rel m' bin_to_nat_res
    ∧ ∃ (multZ_res : Z), multZ_rel 2 bin_to_nat_res multZ_res ∧ bin_to_nat_Bin0_lem_res == multZ_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite bin_to_nat_Bin0_lem: f_rel_back.

Theorem bin_to_nat_Bin1_lem m' bin_to_nat_Bin1_lem_res:
  bin_to_nat_rel (Bin1_u m') bin_to_nat_Bin1_lem_res
  ↔ ∃ (bin_to_nat_res : Z),
    bin_to_nat_rel m' bin_to_nat_res
    ∧ ∃ (multZ_res : Z),
      multZ_rel 2 bin_to_nat_res multZ_res
      ∧ ∃ (addZ_res : Z), addZ_rel 1 multZ_res addZ_res ∧ bin_to_nat_Bin1_lem_res == addZ_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite bin_to_nat_Bin1_lem: f_rel_back.

Theorem bin_to_nat_Z_lem bin_to_nat_Z_lem_res:
  bin_to_nat_rel Z_u bin_to_nat_Z_lem_res ↔ bin_to_nat_Z_lem_res == 0.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite bin_to_nat_Z_lem: f_rel_back.

Theorem bin_to_nat_rel_ex (ds_d3gI : SFBin_u) (ds_d3gI_p : SFBin_wf ds_d3gI ∧ True):
  bin_to_nat_rel ds_d3gI ⌊ bin_to_nat (exist _ ds_d3gI ds_d3gI_p) -⌋.
Proof.
  Opaque bin_to_nat.
  existence_lemma_pre bin_to_nat;
  induction ds_d3gI as [m' IH_m'| m' IH_m'|];
  [fix_notations; pose proof (IH_m' ltac:(try clear IH_m'; solver)) as IH_34714780; try clear IH_m' |
   fix_notations; pose proof (IH_m' ltac:(try clear IH_m'; solver)) as IH_34714780; try clear IH_m' |
   fix_notations];
  simpl in *.
  Transparent bin_to_nat.
  all: (existence_lemma_quicksolve bin_to_nat; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve bin_to_nat_rel_ex: rel_ax_db.

#[global] Opaque bin_to_nat.

Theorem bin_to_nat__bin_to_nat_rel_rw
  (ds_d3gI : SFBin_u) (ds_d3gI_p : SFBin_wf ds_d3gI ∧ True) (VV : Z):
  ⌊ bin_to_nat (exist _ ds_d3gI ds_d3gI_p) -⌋ = VV ↔ bin_to_nat_rel ds_d3gI VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite bin_to_nat__bin_to_nat_rel_rw: f_rel_funct_db.

#[global] Hint Resolve bin_to_nat__bin_to_nat_rel_rw: rel_ax_db.

#[global] Instance bin_to_nat_lookup_rw: dictionary rwLem bin_to_nat := {
    lookup' := bin_to_nat__bin_to_nat_rel_rw }.

Theorem bin_to_nat__bin_to_nat_rel (ds_d3gI : SFBin) (VV : Z):
  ⌊ bin_to_nat ds_d3gI -⌋ = VV ↔ bin_to_nat_rel ⌊ ds_d3gI ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite bin_to_nat__bin_to_nat_rel: f_rel_funct_db.

Theorem bin_to_nat__bin_to_nat_rel' (ds_d3gI_u : SFBin_u) (ds_d3gI : SFBin) (VV : Z):
  ds_d3gI_u = ⌊ ds_d3gI ⌋ → ⌊ bin_to_nat ds_d3gI -⌋ = VV ↔ bin_to_nat_rel ds_d3gI_u VV.
Proof.
  intros ->. refine (bin_to_nat__bin_to_nat_rel ds_d3gI VV).
Qed.

#[global] Hint Resolve bin_to_nat__bin_to_nat_rel': f_rel_funct_db.

Theorem bin_to_nat_rel_mk (ds_d3gI : SFBin_u) (ds_d3gI_p : SFBin_wf ds_d3gI ∧ True):
  {VV: _ | bin_to_nat_rel ds_d3gI VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, bin_to_nat_rel ds_d3gI VV)
          (bin_to_nat (exist _ ds_d3gI ds_d3gI_p))
          _);
  rewrite <- bin_to_nat__bin_to_nat_rel';
  quicksolve.
Qed.

#[global] Hint Resolve bin_to_nat_rel_mk: f_rel_funct_db.

#[global] Instance bin_to_nat_pack:
  @Pack
  (SFBin ::RT λ (ds_d3gI : SFBin), nilRT)
  (SFBin_u ::UT nilUT)
  ltac:(mkProjectsArgListTG ((SFBin ::RT λ (ds_d3gI : SFBin), nilRT)) ((SFBin_u ::UT nilUT)))
  Z
  (λ (x_23528959 : ArgList (SFBin ::RT λ (ds_d3gI : SFBin), nilRT)) (v_x_23528959 : Z),
   ltac:(flattenP (λ (ds_d3gI : SFBin) (VV : Z), True) x_23528959 v_x_23528959)).
Proof.
  buildPackG bin_to_nat bin_to_nat_rel bin_to_nat__bin_to_nat_rel bin_to_nat_rel_funct.
Defined.

#[global] Instance bin_to_nat_upack: @uPack (SFBin_u ::UT nilUT) Z.
Proof.
  buildUPackG bin_to_nat_rel bin_to_nat_rel_funct.
Defined.

Definition test_bin_incr4_spec : Type :=
  {{∃ (bin_to_nat_res : Z),
    bin_to_nat_rel (Bin0_u (Bin1_u Z_u)) bin_to_nat_res ∧ bin_to_nat_res == 2}}.

#[global] Hint Unfold test_bin_incr4_spec: lia_unfold.

Theorem test_bin_incr4 : test_bin_incr4_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (bin_to_nat_res : Z), bin_to_nat_rel (Bin0_u (Bin1_u Z_u)) bin_to_nat_res ∧ bin_to_nat_res == 2)
          (# unit)
          ltac:(solver)).
Qed.

Definition incr_spec (ds_d3gJ : SFBin): Type :=
  SFBin.

#[global] Hint Unfold incr_spec: lia_unfold.

Definition incr (ds_d3gJ : SFBin): incr_spec ds_d3gJ.
Proof.
  destruct ds_d3gJ as [ds_d3gJ ds_d3gJ_p].
  induction ds_d3gJ as [m' _| m' IH_m'|].
  - refine (Bin1 (exist (λ (n : SFBin_u), SFBin_wf n ∧ True) m' ltac:(solver))).
  - refine (Bin0 (IH_m' ltac:(try clear IH_m'; solver))).
  - refine (Bin1 Z).
Defined.

Inductive incr_rel: SFBin_u → SFBin_u → Prop :=
  | incr_Bin0: ∀ m', incr_rel (Bin0_u m') (Bin1_u m')
  | incr_Bin1: ∀ m' (incr_res : SFBin_u),
               incr_rel m' incr_res → incr_rel (Bin1_u m') (Bin0_u incr_res)
  | incr_Z: incr_rel Z_u (Bin1_u Z_u).

#[global] Hint Constructors incr_rel: core_hint_db.

#[global] Instance incr_lookup_rel: dictionary rel incr := { lookup' := incr_rel }.

#[global] Instance incr_getF: getFunc incr_rel := { getF' := incr }.

Theorem incr_rel_funct [ds_d3gJ : SFBin_u]:
  ∀ (VV VV' : SFBin_u), incr_rel ds_d3gJ VV → (incr_rel ds_d3gJ VV' → VV = VV').
Proof.
  induction ds_d3gJ as [m' _| m' IH_m'|]; rel_functionhood_body.
Qed.

#[global] Hint Resolve incr_rel_funct: f_rel_funct_db.

Theorem incr_Bin0_lem m' incr_Bin0_lem_res:
  incr_rel (Bin0_u m') incr_Bin0_lem_res ↔ incr_Bin0_lem_res == Bin1_u m'.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite incr_Bin0_lem: f_rel_back.

Theorem incr_Bin1_lem m' incr_Bin1_lem_res:
  incr_rel (Bin1_u m') incr_Bin1_lem_res
  ↔ ∃ (incr_res : SFBin_u), incr_rel m' incr_res ∧ incr_Bin1_lem_res == Bin0_u incr_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite incr_Bin1_lem: f_rel_back.

Theorem incr_Z_lem incr_Z_lem_res: incr_rel Z_u incr_Z_lem_res ↔ incr_Z_lem_res == Bin1_u Z_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite incr_Z_lem: f_rel_back.

Theorem incr_rel_ex (ds_d3gJ : SFBin_u) (ds_d3gJ_p : SFBin_wf ds_d3gJ ∧ True):
  incr_rel ds_d3gJ ⌊ incr (exist _ ds_d3gJ ds_d3gJ_p) -⌋.
Proof.
  Opaque incr.
  existence_lemma_pre incr;
  induction ds_d3gJ as [m' _| m' IH_m'|];
  [fix_notations |
   fix_notations; pose proof (IH_m' ltac:(try clear IH_m'; solver)) as IH_34714780; try clear IH_m' |
   fix_notations];
  simpl in *.
  Transparent incr.
  all: (existence_lemma_quicksolve incr; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve incr_rel_ex: rel_ax_db.

#[global] Opaque incr.

Theorem incr__incr_rel_rw (ds_d3gJ : SFBin_u) (ds_d3gJ_p : SFBin_wf ds_d3gJ ∧ True) (VV : SFBin_u):
  ⌊ incr (exist _ ds_d3gJ ds_d3gJ_p) -⌋ = VV ↔ incr_rel ds_d3gJ VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite incr__incr_rel_rw: f_rel_funct_db.

#[global] Hint Resolve incr__incr_rel_rw: rel_ax_db.

#[global] Instance incr_lookup_rw: dictionary rwLem incr := { lookup' := incr__incr_rel_rw }.

Theorem incr__incr_rel (ds_d3gJ : SFBin) (VV : SFBin_u):
  ⌊ incr ds_d3gJ -⌋ = VV ↔ incr_rel ⌊ ds_d3gJ ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite incr__incr_rel: f_rel_funct_db.

Theorem incr__incr_rel' (ds_d3gJ_u : SFBin_u) (ds_d3gJ : SFBin) (VV : SFBin_u):
  ds_d3gJ_u = ⌊ ds_d3gJ ⌋ → ⌊ incr ds_d3gJ -⌋ = VV ↔ incr_rel ds_d3gJ_u VV.
Proof.
  intros ->. refine (incr__incr_rel ds_d3gJ VV).
Qed.

#[global] Hint Resolve incr__incr_rel': f_rel_funct_db.

Theorem incr_rel_mk (ds_d3gJ : SFBin_u) (ds_d3gJ_p : SFBin_wf ds_d3gJ ∧ True):
  {VV: _ | incr_rel ds_d3gJ VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, incr_rel ds_d3gJ VV) (incr (exist _ ds_d3gJ ds_d3gJ_p)) _);
  rewrite <- incr__incr_rel';
  quicksolve.
Qed.

#[global] Hint Resolve incr_rel_mk: f_rel_funct_db.

#[global] Instance incr_pack:
  @Pack
  (SFBin ::RT λ (ds_d3gJ : SFBin), nilRT)
  (SFBin_u ::UT nilUT)
  ltac:(mkProjectsArgListTG ((SFBin ::RT λ (ds_d3gJ : SFBin), nilRT)) ((SFBin_u ::UT nilUT)))
  SFBin_u
  (λ (x_68663135 : ArgList (SFBin ::RT λ (ds_d3gJ : SFBin), nilRT)) (v_x_68663135 : SFBin_u),
   ltac:(flattenP (λ (ds_d3gJ : SFBin) (VV : SFBin_u), SFBin_wf VV ∧ True) x_68663135 v_x_68663135)).
Proof.
  buildPackG incr incr_rel incr__incr_rel incr_rel_funct.
Defined.

#[global] Instance incr_upack: @uPack (SFBin_u ::UT nilUT) SFBin_u.
Proof.
  buildUPackG incr_rel incr_rel_funct.
Defined.

Definition test_bin_incr1_spec : Type :=
  {{∃ (incr_res : SFBin_u), incr_rel (Bin1_u Z_u) incr_res ∧ incr_res == Bin0_u (Bin1_u Z_u)}}.

#[global] Hint Unfold test_bin_incr1_spec: lia_unfold.

Theorem test_bin_incr1 : test_bin_incr1_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (incr_res : SFBin_u), incr_rel (Bin1_u Z_u) incr_res ∧ incr_res == Bin0_u (Bin1_u Z_u))
          (# unit)
          ltac:(solver)).
Qed.

Definition test_bin_incr2_spec : Type :=
  {{∃ (incr_res : SFBin_u),
    incr_rel (Bin0_u (Bin1_u Z_u)) incr_res ∧ incr_res == Bin1_u (Bin1_u Z_u)}}.

#[global] Hint Unfold test_bin_incr2_spec: lia_unfold.

Theorem test_bin_incr2 : test_bin_incr2_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (incr_res : SFBin_u), incr_rel (Bin0_u (Bin1_u Z_u)) incr_res ∧ incr_res == Bin1_u (Bin1_u Z_u))
          (# unit)
          ltac:(solver)).
Qed.

Definition test_bin_incr3_spec : Type :=
  {{∃ (incr_res : SFBin_u),
    incr_rel (Bin1_u (Bin1_u Z_u)) incr_res ∧ incr_res == Bin0_u (Bin0_u (Bin1_u Z_u))}}.

#[global] Hint Unfold test_bin_incr3_spec: lia_unfold.

Theorem test_bin_incr3 : test_bin_incr3_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (incr_res : SFBin_u),
           incr_rel (Bin1_u (Bin1_u Z_u)) incr_res ∧ incr_res == Bin0_u (Bin0_u (Bin1_u Z_u)))
          (# unit)
          ltac:(solver)).
Qed.

Definition test_bin_incr5_spec : Type :=
  {{∃ (incr_res : SFBin_u),
    incr_rel (Bin1_u Z_u) incr_res
    ∧ ∃ (bin_to_nat_res : Z),
      bin_to_nat_rel incr_res bin_to_nat_res
      ∧ ∃ (bin_to_nat_res_2 : Z),
        bin_to_nat_rel (Bin1_u Z_u) bin_to_nat_res_2
        ∧ ∃ (addZ_res : Z), addZ_rel 1 bin_to_nat_res_2 addZ_res ∧ bin_to_nat_res == addZ_res}}.

#[global] Hint Unfold test_bin_incr5_spec: lia_unfold.

Theorem test_bin_incr5 : test_bin_incr5_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (incr_res : SFBin_u),
           incr_rel (Bin1_u Z_u) incr_res
           ∧ ∃ (bin_to_nat_res : Z),
             bin_to_nat_rel incr_res bin_to_nat_res
             ∧ ∃ (bin_to_nat_res_2 : Z),
               bin_to_nat_rel (Bin1_u Z_u) bin_to_nat_res_2
               ∧ ∃ (addZ_res : Z), addZ_rel 1 bin_to_nat_res_2 addZ_res ∧ bin_to_nat_res == addZ_res)
          (# unit)
          ltac:(solver)).
Qed.

Definition test_bin_incr6_spec : Type :=
  {{∃ (incr_res : SFBin_u),
    incr_rel (Bin1_u Z_u) incr_res
    ∧ ∃ (incr_res_2 : SFBin_u),
      incr_rel incr_res incr_res_2
      ∧ ∃ (bin_to_nat_res : Z),
        bin_to_nat_rel incr_res_2 bin_to_nat_res
        ∧ ∃ (bin_to_nat_res_2 : Z),
          bin_to_nat_rel (Bin1_u Z_u) bin_to_nat_res_2
          ∧ ∃ (addZ_res : Z), addZ_rel 2 bin_to_nat_res_2 addZ_res ∧ bin_to_nat_res == addZ_res}}.

#[global] Hint Unfold test_bin_incr6_spec: lia_unfold.

Theorem test_bin_incr6 : test_bin_incr6_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (incr_res : SFBin_u),
           incr_rel (Bin1_u Z_u) incr_res
           ∧ ∃ (incr_res_2 : SFBin_u),
             incr_rel incr_res incr_res_2
             ∧ ∃ (bin_to_nat_res : Z),
               bin_to_nat_rel incr_res_2 bin_to_nat_res
               ∧ ∃ (bin_to_nat_res_2 : Z),
                 bin_to_nat_rel (Bin1_u Z_u) bin_to_nat_res_2
                 ∧ ∃ (addZ_res : Z), addZ_rel 2 bin_to_nat_res_2 addZ_res ∧ bin_to_nat_res == addZ_res)
          (# unit)
          ltac:(solver)).
Qed.

Inductive RGB_u: Type :=
  | Blue_u: RGB_u | Green_u: RGB_u | Red_u: RGB_u.

Fixpoint RGB_eq (x y : RGB_u): bool :=
  match (x, y) with
  | (Blue_u, Blue_u) => true
  | (Green_u, Green_u) => true
  | (Red_u, Red_u) => true
  | (_, _) => false
  end.

Theorem RGB_eq_refl : ∀ (x : RGB_u), is_true (RGB_eq x x).
Proof.
  eq_refl_rec.
Qed.

#[global] Hint Resolve RGB_eq_refl: eq_hint_db.

Theorem RGB_eqb_eq : ∀ (s t : RGB_u), is_true (RGB_eq s t) → s = t.
Proof.
  eqb_eq_lem.
Qed.

#[global] Hint Resolve RGB_eqb_eq: eq_hint_db.

#[global] Instance leibnitz_eq_RGB: LeibnitzEqB := {
    equalB' := RGB_eq;
    refl' := RGB_eq_refl;
    eqb_eq' := RGB_eqb_eq }.

Fixpoint RGB_wf (x : RGB_u): Prop :=
  match x with | Blue_u => True | Green_u => True | Red_u => True end.

Theorem RGB_wf_ref [p : RGB_u → Prop] (tm : {v: RGB_u | RGB_wf v ∧ p v}): RGB_wf ⌊ tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation RGB := {x: RGB_u | RGB_wf x ∧ True}.

Definition Blue_lem : RGB_wf Blue_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Blue : RGB :=
  exist _ Blue_u Blue_lem.

Definition Green_lem : RGB_wf Green_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Green : RGB :=
  exist _ Green_u Green_lem.

Definition Red_lem : RGB_wf Red_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Red : RGB :=
  exist _ Red_u Red_lem.

#[global] Hint Resolve RGB_wf_ref: wf_constr_db.

#[global] Hint Unfold RGB_wf: wf_constr_db.

#[global] Hint Resolve RGB_eq: ref_constr_db.

#[global] Hint Unfold Blue: ref_constr_db.

#[global] Hint Unfold Green: ref_constr_db.

#[global] Hint Unfold Red: ref_constr_db.

Inductive OtherNat_u: Type :=
  | Stop_u: OtherNat_u | Tick_u: OtherNat_u → OtherNat_u.

Fixpoint OtherNat_eq (x y : OtherNat_u): bool :=
  match (x, y) with
  | (Stop_u, Stop_u) => true
  | (Tick_u VV, Tick_u VV') => true && OtherNat_eq VV VV'
  | (_, _) => false
  end.

Theorem OtherNat_eq_refl : ∀ (x : OtherNat_u), is_true (OtherNat_eq x x).
Proof.
  eq_refl_rec.
Qed.

#[global] Hint Resolve OtherNat_eq_refl: eq_hint_db.

Theorem OtherNat_eqb_eq : ∀ (s t : OtherNat_u), is_true (OtherNat_eq s t) → s = t.
Proof.
  eqb_eq_lem.
Qed.

#[global] Hint Resolve OtherNat_eqb_eq: eq_hint_db.

#[global] Instance leibnitz_eq_OtherNat: LeibnitzEqB := {
    equalB' := OtherNat_eq;
    refl' := OtherNat_eq_refl;
    eqb_eq' := OtherNat_eqb_eq }.

Fixpoint OtherNat_wf (x : OtherNat_u): Prop :=
  match x with | Stop_u => True | Tick_u VV => OtherNat_wf VV ∧ True end.

Theorem OtherNat_wf_ref [p : OtherNat_u → Prop] (tm : {v: OtherNat_u | OtherNat_wf v ∧ p v}):
  OtherNat_wf ⌊ tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation OtherNat := {x: OtherNat_u | OtherNat_wf x ∧ True}.

Definition Stop_lem : OtherNat_wf Stop_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Stop : OtherNat :=
  exist _ Stop_u Stop_lem.

Definition Tick_lem (VV : OtherNat): OtherNat_wf (Tick_u ⌊ VV ⌋) ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Tick (VV : OtherNat): OtherNat :=
  exist _ (Tick_u ⌊ VV ⌋) (Tick_lem VV).

Definition wf_Tick_VV [VV : OtherNat_u] (p : OtherNat_wf (Tick_u VV)): OtherNat_wf VV.
Proof.
  quicksolve.
Defined.

#[global] Hint Resolve wf_Tick_VV: ref_constr_db.

#[global] Hint Resolve OtherNat_wf_ref: wf_constr_db.

#[global] Hint Unfold OtherNat_wf: wf_constr_db.

#[global] Hint Resolve OtherNat_eq: ref_constr_db.

#[global] Hint Unfold Stop: ref_constr_db.

#[global] Hint Unfold Tick: ref_constr_db.

Inductive Nibble_u: Type :=
  | Bits_u: SFBit_u → SFBit_u → SFBit_u → SFBit_u → Nibble_u.

Fixpoint Nibble_eq (x y : Nibble_u): bool :=
  match (x, y) with
  | (Bits_u VV VV_ VV__ VV___, Bits_u VV' VV_' VV__' VV___') => (((true && (VV ==? VV'))
                                                                  && (VV_ ==? VV_'))
                                                                 && (VV__ ==? VV__'))
                                                                && (VV___ ==? VV___')
  end.

Theorem Nibble_eq_refl : ∀ (x : Nibble_u), is_true (Nibble_eq x x).
Proof.
  eq_refl_rec.
Qed.

#[global] Hint Resolve Nibble_eq_refl: eq_hint_db.

Theorem Nibble_eqb_eq : ∀ (s t : Nibble_u), is_true (Nibble_eq s t) → s = t.
Proof.
  eqb_eq_lem.
Qed.

#[global] Hint Resolve Nibble_eqb_eq: eq_hint_db.

#[global] Instance leibnitz_eq_Nibble: LeibnitzEqB := {
    equalB' := Nibble_eq;
    refl' := Nibble_eq_refl;
    eqb_eq' := Nibble_eqb_eq }.

Fixpoint Nibble_wf (x : Nibble_u): Prop :=
  match x with
  | Bits_u VV VV_ VV__ VV___ => (((SFBit_wf VV ∧ True) ∧ (SFBit_wf VV_ ∧ True))
                                 ∧ (SFBit_wf VV__ ∧ True))
                                ∧ (SFBit_wf VV___ ∧ True)
  end.

Theorem Nibble_wf_ref [p : Nibble_u → Prop] (tm : {v: Nibble_u | Nibble_wf v ∧ p v}):
  Nibble_wf ⌊ tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation Nibble := {x: Nibble_u | Nibble_wf x ∧ True}.

Definition Bits_lem (VV VV_ VV__ VV___ : SFBit):
  Nibble_wf (Bits_u ⌊ VV ⌋ ⌊ VV_ ⌋ ⌊ VV__ ⌋ ⌊ VV___ ⌋) ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Bits (VV VV_ VV__ VV___ : SFBit): Nibble :=
  exist _ (Bits_u ⌊ VV ⌋ ⌊ VV_ ⌋ ⌊ VV__ ⌋ ⌊ VV___ ⌋) (Bits_lem VV VV_ VV__ VV___).

Definition wf_Bits_VV [VV VV_ VV__ VV___ : SFBit_u] (p : Nibble_wf (Bits_u VV VV_ VV__ VV___)):
  SFBit_wf VV.
Proof.
  quicksolve.
Defined.

#[global] Hint Resolve wf_Bits_VV: ref_constr_db.

Definition wf_Bits_VV_ [VV VV_ VV__ VV___ : SFBit_u] (p : Nibble_wf (Bits_u VV VV_ VV__ VV___)):
  SFBit_wf VV_.
Proof.
  quicksolve.
Defined.

#[global] Hint Resolve wf_Bits_VV_: ref_constr_db.

Definition wf_Bits_VV__ [VV VV_ VV__ VV___ : SFBit_u] (p : Nibble_wf (Bits_u VV VV_ VV__ VV___)):
  SFBit_wf VV__.
Proof.
  quicksolve.
Defined.

#[global] Hint Resolve wf_Bits_VV__: ref_constr_db.

Definition wf_Bits_VV___ [VV VV_ VV__ VV___ : SFBit_u] (p : Nibble_wf (Bits_u VV VV_ VV__ VV___)):
  SFBit_wf VV___.
Proof.
  quicksolve.
Defined.

#[global] Hint Resolve wf_Bits_VV___: ref_constr_db.

#[global] Hint Resolve Nibble_wf_ref: wf_constr_db.

#[global] Hint Unfold Nibble_wf: wf_constr_db.

#[global] Hint Resolve Nibble_eq: ref_constr_db.

#[global] Hint Unfold Bits: ref_constr_db.

Definition allzero_spec (ds_d3in : Nibble): Type :=
  SFBool.

#[global] Hint Unfold allzero_spec: lia_unfold.

Definition allzero (ds_d3in : Nibble): allzero_spec ds_d3in.
Proof.
  destruct ds_d3in as [ds_d3in ds_d3in_p].
  destruct ds_d3in as [ds_d3io ds_d3ip ds_d3iq ds_d3ir].
  - destruct ds_d3io as [|].
    + destruct ds_d3ip as [|].
      ** destruct ds_d3iq as [|].
         ** destruct ds_d3ir as [|].
            ** refine SFTrue.
            ** refine SFFalse.
         ** refine SFFalse.
      ** refine SFFalse.
    + refine SFFalse.
Defined.

Inductive MyNat_u: Type :=
  | O_u: MyNat_u | S_u: MyNat_u → MyNat_u.

Fixpoint MyNat_eq (x y : MyNat_u): bool :=
  match (x, y) with
  | (O_u, O_u) => true
  | (S_u VV, S_u VV') => true && MyNat_eq VV VV'
  | (_, _) => false
  end.

Theorem MyNat_eq_refl : ∀ (x : MyNat_u), is_true (MyNat_eq x x).
Proof.
  eq_refl_rec.
Qed.

#[global] Hint Resolve MyNat_eq_refl: eq_hint_db.

Theorem MyNat_eqb_eq : ∀ (s t : MyNat_u), is_true (MyNat_eq s t) → s = t.
Proof.
  eqb_eq_lem.
Qed.

#[global] Hint Resolve MyNat_eqb_eq: eq_hint_db.

#[global] Instance leibnitz_eq_MyNat: LeibnitzEqB := {
    equalB' := MyNat_eq;
    refl' := MyNat_eq_refl;
    eqb_eq' := MyNat_eqb_eq }.

Fixpoint MyNat_wf (x : MyNat_u): Prop :=
  match x with | O_u => True | S_u VV => MyNat_wf VV ∧ True end.

Theorem MyNat_wf_ref [p : MyNat_u → Prop] (tm : {v: MyNat_u | MyNat_wf v ∧ p v}): MyNat_wf ⌊ tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation MyNat := {x: MyNat_u | MyNat_wf x ∧ True}.

Definition O_lem : MyNat_wf O_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition O : MyNat :=
  exist _ O_u O_lem.

Definition S_lem (VV : MyNat): MyNat_wf (S_u ⌊ VV ⌋) ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition S (VV : MyNat): MyNat :=
  exist _ (S_u ⌊ VV ⌋) (S_lem VV).

Definition wf_S_VV [VV : MyNat_u] (p : MyNat_wf (S_u VV)): MyNat_wf VV.
Proof.
  quicksolve.
Defined.

#[global] Hint Resolve wf_S_VV: ref_constr_db.

#[global] Hint Resolve MyNat_wf_ref: wf_constr_db.

#[global] Hint Unfold MyNat_wf: wf_constr_db.

#[global] Hint Resolve MyNat_eq: ref_constr_db.

#[global] Hint Unfold O: ref_constr_db.

#[global] Hint Unfold S: ref_constr_db.

Inductive Natprod_u: Type :=
  | Pair_u: MyNat_u → MyNat_u → Natprod_u.

Fixpoint Natprod_eq (x y : Natprod_u): bool :=
  match (x, y) with | (Pair_u n1 n2, Pair_u n1' n2') => (true && (n1 ==? n1')) && (n2 ==? n2') end.

Theorem Natprod_eq_refl : ∀ (x : Natprod_u), is_true (Natprod_eq x x).
Proof.
  eq_refl_rec.
Qed.

#[global] Hint Resolve Natprod_eq_refl: eq_hint_db.

Theorem Natprod_eqb_eq : ∀ (s t : Natprod_u), is_true (Natprod_eq s t) → s = t.
Proof.
  eqb_eq_lem.
Qed.

#[global] Hint Resolve Natprod_eqb_eq: eq_hint_db.

#[global] Instance leibnitz_eq_Natprod: LeibnitzEqB := {
    equalB' := Natprod_eq;
    refl' := Natprod_eq_refl;
    eqb_eq' := Natprod_eqb_eq }.

Fixpoint Natprod_wf (x : Natprod_u): Prop :=
  match x with | Pair_u n1 n2 => (MyNat_wf n1 ∧ True) ∧ (MyNat_wf n2 ∧ True) end.

Theorem Natprod_wf_ref [p : Natprod_u → Prop] (tm : {v: Natprod_u | Natprod_wf v ∧ p v}):
  Natprod_wf ⌊ tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation Natprod := {x: Natprod_u | Natprod_wf x ∧ True}.

Definition Pair_lem (n1 n2 : MyNat): Natprod_wf (Pair_u ⌊ n1 ⌋ ⌊ n2 ⌋) ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Pair (n1 n2 : MyNat): Natprod :=
  exist _ (Pair_u ⌊ n1 ⌋ ⌊ n2 ⌋) (Pair_lem n1 n2).

Definition wf_Pair_n1 [n1 n2 : MyNat_u] (p : Natprod_wf (Pair_u n1 n2)): MyNat_wf n1.
Proof.
  quicksolve.
Defined.

#[global] Hint Resolve wf_Pair_n1: ref_constr_db.

Definition wf_Pair_n2 [n1 n2 : MyNat_u] (p : Natprod_wf (Pair_u n1 n2)): MyNat_wf n2.
Proof.
  quicksolve.
Defined.

#[global] Hint Resolve wf_Pair_n2: ref_constr_db.

#[global] Hint Resolve Natprod_wf_ref: wf_constr_db.

#[global] Hint Unfold Natprod_wf: wf_constr_db.

#[global] Hint Resolve Natprod_eq: ref_constr_db.

#[global] Hint Unfold Pair: ref_constr_db.

Definition swap_pair_spec (ds_d3gy : Natprod): Type :=
  Natprod.

#[global] Hint Unfold swap_pair_spec: lia_unfold.

Definition swap_pair (ds_d3gy : Natprod): swap_pair_spec ds_d3gy.
Proof.
  destruct ds_d3gy as [ds_d3gy ds_d3gy_p].
  destruct ds_d3gy as [x y].
  - refine (Pair
            (exist (λ (n2 : MyNat_u), MyNat_wf n2 ∧ True) y ltac:(solver))
            (exist (λ (n1 : MyNat_u), MyNat_wf n1 ∧ True) x ltac:(solver))).
Defined.

Inductive swap_pair_rel: Natprod_u → Natprod_u → Prop :=
  | swap_pair_Pair: ∀ x y, swap_pair_rel (Pair_u x y) (Pair_u y x).

#[global] Hint Constructors swap_pair_rel: core_hint_db.

#[global] Instance swap_pair_lookup_rel: dictionary rel swap_pair := { lookup' := swap_pair_rel }.

#[global] Instance swap_pair_getF: getFunc swap_pair_rel := { getF' := swap_pair }.

Theorem swap_pair_rel_funct [ds_d3gy : Natprod_u]:
  ∀ (VV VV' : Natprod_u), swap_pair_rel ds_d3gy VV → (swap_pair_rel ds_d3gy VV' → VV = VV').
Proof.
  destruct ds_d3gy as [x y]; rel_functionhood_body.
Qed.

#[global] Hint Resolve swap_pair_rel_funct: f_rel_funct_db.

Theorem swap_pair_Pair_lem x y swap_pair_Pair_lem_res:
  swap_pair_rel (Pair_u x y) swap_pair_Pair_lem_res ↔ swap_pair_Pair_lem_res == Pair_u y x.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite swap_pair_Pair_lem: f_rel_back.

Theorem swap_pair_rel_ex (ds_d3gy : Natprod_u) (ds_d3gy_p : Natprod_wf ds_d3gy ∧ True):
  swap_pair_rel ds_d3gy ⌊ swap_pair (exist _ ds_d3gy ds_d3gy_p) -⌋.
Proof.
  Opaque swap_pair.
  existence_lemma_pre swap_pair;
  destruct ds_d3gy as [x y];
  [fix_notations];
  simpl in *.
  Transparent swap_pair.
  all: (existence_lemma_quicksolve swap_pair; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve swap_pair_rel_ex: rel_ax_db.

#[global] Opaque swap_pair.

Theorem swap_pair__swap_pair_rel_rw
  (ds_d3gy : Natprod_u) (ds_d3gy_p : Natprod_wf ds_d3gy ∧ True) (VV : Natprod_u):
  ⌊ swap_pair (exist _ ds_d3gy ds_d3gy_p) -⌋ = VV ↔ swap_pair_rel ds_d3gy VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite swap_pair__swap_pair_rel_rw: f_rel_funct_db.

#[global] Hint Resolve swap_pair__swap_pair_rel_rw: rel_ax_db.

#[global] Instance swap_pair_lookup_rw: dictionary rwLem swap_pair := {
    lookup' := swap_pair__swap_pair_rel_rw }.

Theorem swap_pair__swap_pair_rel (ds_d3gy : Natprod) (VV : Natprod_u):
  ⌊ swap_pair ds_d3gy -⌋ = VV ↔ swap_pair_rel ⌊ ds_d3gy ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite swap_pair__swap_pair_rel: f_rel_funct_db.

Theorem swap_pair__swap_pair_rel' (ds_d3gy_u : Natprod_u) (ds_d3gy : Natprod) (VV : Natprod_u):
  ds_d3gy_u = ⌊ ds_d3gy ⌋ → ⌊ swap_pair ds_d3gy -⌋ = VV ↔ swap_pair_rel ds_d3gy_u VV.
Proof.
  intros ->. refine (swap_pair__swap_pair_rel ds_d3gy VV).
Qed.

#[global] Hint Resolve swap_pair__swap_pair_rel': f_rel_funct_db.

Theorem swap_pair_rel_mk (ds_d3gy : Natprod_u) (ds_d3gy_p : Natprod_wf ds_d3gy ∧ True):
  {VV: _ | swap_pair_rel ds_d3gy VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, swap_pair_rel ds_d3gy VV)
          (swap_pair (exist _ ds_d3gy ds_d3gy_p))
          _);
  rewrite <- swap_pair__swap_pair_rel';
  quicksolve.
Qed.

#[global] Hint Resolve swap_pair_rel_mk: f_rel_funct_db.

#[global] Instance swap_pair_pack:
  @Pack
  (Natprod ::RT λ (ds_d3gy : Natprod), nilRT)
  (Natprod_u ::UT nilUT)
  ltac:(mkProjectsArgListTG ((Natprod ::RT λ (ds_d3gy : Natprod), nilRT)) ((Natprod_u ::UT nilUT)))
  Natprod_u
  (λ (x_44325251 : ArgList (Natprod ::RT λ (ds_d3gy : Natprod), nilRT)) (v_x_44325251 : Natprod_u),
   ltac:(flattenP (λ (ds_d3gy : Natprod) (VV : Natprod_u), Natprod_wf VV ∧ True) x_44325251 v_x_44325251)).
Proof.
  buildPackG swap_pair swap_pair_rel swap_pair__swap_pair_rel swap_pair_rel_funct.
Defined.

#[global] Instance swap_pair_upack: @uPack (Natprod_u ::UT nilUT) Natprod_u.
Proof.
  buildUPackG swap_pair_rel swap_pair_rel_funct.
Defined.

Definition eqb_spec (ds_d3hR ds_d3hS : MyNat): Type :=
  SFBool.

#[global] Hint Unfold eqb_spec: lia_unfold.

Definition eqb (ds_d3hR ds_d3hS : MyNat): eqb_spec ds_d3hR ds_d3hS.
Proof.
  destruct ds_d3hR as [ds_d3hR ds_d3hR_p].
  destruct ds_d3hS as [ds_d3hS ds_d3hS_p].
  try revert ds_d3hS_p; generalize dependent ds_d3hS; induction ds_d3hR as [| n' IH_n']; intros.
  - destruct ds_d3hS as [| m'].
    + refine SFTrue.
    + refine SFFalse.
  - destruct ds_d3hS as [| m'].
    + refine SFFalse.
    + refine (IH_n' ltac:(try clear IH_n'; solver) m' ltac:(try clear IH_n'; solver)).
Defined.

Inductive eqb_rel: MyNat_u → MyNat_u → SFBool_u → Prop :=
  | eqb_O_O: eqb_rel O_u O_u SFTrue_u
  | eqb_O_S: ∀ m', eqb_rel O_u (S_u m') SFFalse_u
  | eqb_S_O: ∀ n', eqb_rel (S_u n') O_u SFFalse_u
  | eqb_S_S: ∀ n' m' (eqb_res : SFBool_u), eqb_rel n' m' eqb_res → eqb_rel (S_u n') (S_u m') eqb_res.

#[global] Hint Constructors eqb_rel: core_hint_db.

#[global] Instance eqb_lookup_rel: dictionary rel eqb := { lookup' := eqb_rel }.

#[global] Instance eqb_getF: getFunc eqb_rel := { getF' := eqb }.

Theorem eqb_rel_funct [ds_d3hR ds_d3hS : MyNat_u]:
  ∀ (VV VV' : SFBool_u), eqb_rel ds_d3hR ds_d3hS VV → (eqb_rel ds_d3hR ds_d3hS VV' → VV = VV').
Proof.
  try revert ds_d3hS_p; generalize dependent ds_d3hS; induction ds_d3hR as [| n' IH_n']; intros;
  [destruct ds_d3hS as [| m'] | destruct ds_d3hS as [| m']];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve eqb_rel_funct: f_rel_funct_db.

Theorem eqb_O_O_lem eqb_O_O_lem_res: eqb_rel O_u O_u eqb_O_O_lem_res ↔ eqb_O_O_lem_res == SFTrue_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite eqb_O_O_lem: f_rel_back.

Theorem eqb_O_S_lem m' eqb_O_S_lem_res:
  eqb_rel O_u (S_u m') eqb_O_S_lem_res ↔ eqb_O_S_lem_res == SFFalse_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite eqb_O_S_lem: f_rel_back.

Theorem eqb_S_O_lem n' eqb_S_O_lem_res:
  eqb_rel (S_u n') O_u eqb_S_O_lem_res ↔ eqb_S_O_lem_res == SFFalse_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite eqb_S_O_lem: f_rel_back.

Theorem eqb_S_S_lem m' n' eqb_S_S_lem_res:
  eqb_rel (S_u n') (S_u m') eqb_S_S_lem_res
  ↔ ∃ (eqb_res : SFBool_u), eqb_rel n' m' eqb_res ∧ eqb_S_S_lem_res == eqb_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite eqb_S_S_lem: f_rel_back.

Theorem eqb_rel_ex
  (ds_d3hR : MyNat_u)
  (ds_d3hR_p : MyNat_wf ds_d3hR ∧ True)
  (ds_d3hS : MyNat_u)
  (ds_d3hS_p : MyNat_wf ds_d3hS ∧ True):
  eqb_rel ds_d3hR ds_d3hS ⌊ eqb (exist _ ds_d3hR ds_d3hR_p) (exist _ ds_d3hS ds_d3hS_p) -⌋.
Proof.
  Opaque eqb.
  existence_lemma_pre eqb;
  try revert ds_d3hS_p; generalize dependent ds_d3hS; induction ds_d3hR as [| n' IH_n']; intros;
  [destruct ds_d3hS as [| m'];
   [fix_notations | fix_notations] |
   destruct ds_d3hS as [| m'];
   [fix_notations |
    fix_notations;
    pose proof (IH_n' ltac:(try clear IH_n'; solver) m' ltac:(try clear IH_n'; solver)) as IH_11391185;
    try clear IH_n']];
  simpl in *.
  Transparent eqb.
  all: (existence_lemma_quicksolve eqb; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve eqb_rel_ex: rel_ax_db.

#[global] Opaque eqb.

Theorem eqb__eqb_rel_rw
  (ds_d3hR : MyNat_u)
  (ds_d3hR_p : MyNat_wf ds_d3hR ∧ True)
  (ds_d3hS : MyNat_u)
  (ds_d3hS_p : MyNat_wf ds_d3hS ∧ True)
  (VV : SFBool_u):
  ⌊ eqb (exist _ ds_d3hR ds_d3hR_p) (exist _ ds_d3hS ds_d3hS_p) -⌋ = VV ↔ eqb_rel ds_d3hR ds_d3hS VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite eqb__eqb_rel_rw: f_rel_funct_db.

#[global] Hint Resolve eqb__eqb_rel_rw: rel_ax_db.

#[global] Instance eqb_lookup_rw: dictionary rwLem eqb := { lookup' := eqb__eqb_rel_rw }.

Theorem eqb__eqb_rel (ds_d3hR ds_d3hS : MyNat) (VV : SFBool_u):
  ⌊ eqb ds_d3hR ds_d3hS -⌋ = VV ↔ eqb_rel ⌊ ds_d3hR ⌋ ⌊ ds_d3hS ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite eqb__eqb_rel: f_rel_funct_db.

Theorem eqb__eqb_rel' (ds_d3hR_u ds_d3hS_u : MyNat_u) (ds_d3hR ds_d3hS : MyNat) (VV : SFBool_u):
  ds_d3hR_u = ⌊ ds_d3hR ⌋
  → (ds_d3hS_u = ⌊ ds_d3hS ⌋ → ⌊ eqb ds_d3hR ds_d3hS -⌋ = VV ↔ eqb_rel ds_d3hR_u ds_d3hS_u VV).
Proof.
  intros -> ->. refine (eqb__eqb_rel ds_d3hR ds_d3hS VV).
Qed.

#[global] Hint Resolve eqb__eqb_rel': f_rel_funct_db.

Theorem eqb_rel_mk
  (ds_d3hR : MyNat_u)
  (ds_d3hR_p : MyNat_wf ds_d3hR ∧ True)
  (ds_d3hS : MyNat_u)
  (ds_d3hS_p : MyNat_wf ds_d3hS ∧ True):
  {VV: _ | eqb_rel ds_d3hR ds_d3hS VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, eqb_rel ds_d3hR ds_d3hS VV)
          (eqb (exist _ ds_d3hR ds_d3hR_p) (exist _ ds_d3hS ds_d3hS_p))
          _);
  rewrite <- eqb__eqb_rel';
  quicksolve.
Qed.

#[global] Hint Resolve eqb_rel_mk: f_rel_funct_db.

#[global] Instance eqb_pack:
  @Pack
  (MyNat ::RT λ (ds_d3hR : MyNat), MyNat ::RT λ (ds_d3hS : MyNat), nilRT)
  (MyNat_u ::UT (MyNat_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((MyNat
  ::RT λ (ds_d3hR : MyNat), MyNat ::RT λ (ds_d3hS : MyNat), nilRT)) ((MyNat_u ::UT (MyNat_u ::UT nilUT))))
  SFBool_u
  (λ (x_50200660 : ArgList (MyNat ::RT λ (ds_d3hR : MyNat), MyNat ::RT λ (ds_d3hS : MyNat), nilRT))
     (v_x_50200660 : SFBool_u),
   ltac:(flattenP (λ (ds_d3hR ds_d3hS : MyNat) (VV : SFBool_u), SFBool_wf VV ∧ True) x_50200660 v_x_50200660)).
Proof.
  buildPackG eqb eqb_rel eqb__eqb_rel eqb_rel_funct.
Defined.

#[global] Instance eqb_upack: @uPack (MyNat_u ::UT (MyNat_u ::UT nilUT)) SFBool_u.
Proof.
  buildUPackG eqb_rel eqb_rel_funct.
Defined.

Definition fstSF_spec (ds_d3gC : Natprod): Type :=
  MyNat.

#[global] Hint Unfold fstSF_spec: lia_unfold.

Definition fstSF (ds_d3gC : Natprod): fstSF_spec ds_d3gC.
Proof.
  destruct ds_d3gC as [ds_d3gC ds_d3gC_p].
  destruct ds_d3gC as [n1 n2].
  - refine (exist (λ (n1 : MyNat_u), MyNat_wf n1 ∧ True) n1 ltac:(solver)).
Defined.

Inductive fstSF_rel: Natprod_u → MyNat_u → Prop :=
  | fstSF_Pair: ∀ n1 n2, fstSF_rel (Pair_u n1 n2) n1.

#[global] Hint Constructors fstSF_rel: core_hint_db.

#[global] Instance fstSF_lookup_rel: dictionary rel fstSF := { lookup' := fstSF_rel }.

#[global] Instance fstSF_getF: getFunc fstSF_rel := { getF' := fstSF }.

Theorem fstSF_rel_funct [ds_d3gC : Natprod_u]:
  ∀ (VV VV' : MyNat_u), fstSF_rel ds_d3gC VV → (fstSF_rel ds_d3gC VV' → VV = VV').
Proof.
  destruct ds_d3gC as [n1 n2]; rel_functionhood_body.
Qed.

#[global] Hint Resolve fstSF_rel_funct: f_rel_funct_db.

Theorem fstSF_Pair_lem n1 n2 fstSF_Pair_lem_res:
  fstSF_rel (Pair_u n1 n2) fstSF_Pair_lem_res ↔ fstSF_Pair_lem_res == n1.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite fstSF_Pair_lem: f_rel_back.

Theorem fstSF_rel_ex (ds_d3gC : Natprod_u) (ds_d3gC_p : Natprod_wf ds_d3gC ∧ True):
  fstSF_rel ds_d3gC ⌊ fstSF (exist _ ds_d3gC ds_d3gC_p) -⌋.
Proof.
  Opaque fstSF.
  existence_lemma_pre fstSF;
  destruct ds_d3gC as [n1 n2];
  [fix_notations];
  simpl in *.
  Transparent fstSF.
  all: (existence_lemma_quicksolve fstSF; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve fstSF_rel_ex: rel_ax_db.

#[global] Opaque fstSF.

Theorem fstSF__fstSF_rel_rw
  (ds_d3gC : Natprod_u) (ds_d3gC_p : Natprod_wf ds_d3gC ∧ True) (VV : MyNat_u):
  ⌊ fstSF (exist _ ds_d3gC ds_d3gC_p) -⌋ = VV ↔ fstSF_rel ds_d3gC VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite fstSF__fstSF_rel_rw: f_rel_funct_db.

#[global] Hint Resolve fstSF__fstSF_rel_rw: rel_ax_db.

#[global] Instance fstSF_lookup_rw: dictionary rwLem fstSF := { lookup' := fstSF__fstSF_rel_rw }.

Theorem fstSF__fstSF_rel (ds_d3gC : Natprod) (VV : MyNat_u):
  ⌊ fstSF ds_d3gC -⌋ = VV ↔ fstSF_rel ⌊ ds_d3gC ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite fstSF__fstSF_rel: f_rel_funct_db.

Theorem fstSF__fstSF_rel' (ds_d3gC_u : Natprod_u) (ds_d3gC : Natprod) (VV : MyNat_u):
  ds_d3gC_u = ⌊ ds_d3gC ⌋ → ⌊ fstSF ds_d3gC -⌋ = VV ↔ fstSF_rel ds_d3gC_u VV.
Proof.
  intros ->. refine (fstSF__fstSF_rel ds_d3gC VV).
Qed.

#[global] Hint Resolve fstSF__fstSF_rel': f_rel_funct_db.

Theorem fstSF_rel_mk (ds_d3gC : Natprod_u) (ds_d3gC_p : Natprod_wf ds_d3gC ∧ True):
  {VV: _ | fstSF_rel ds_d3gC VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, fstSF_rel ds_d3gC VV) (fstSF (exist _ ds_d3gC ds_d3gC_p)) _);
  rewrite <- fstSF__fstSF_rel';
  quicksolve.
Qed.

#[global] Hint Resolve fstSF_rel_mk: f_rel_funct_db.

#[global] Instance fstSF_pack:
  @Pack
  (Natprod ::RT λ (ds_d3gC : Natprod), nilRT)
  (Natprod_u ::UT nilUT)
  ltac:(mkProjectsArgListTG ((Natprod ::RT λ (ds_d3gC : Natprod), nilRT)) ((Natprod_u ::UT nilUT)))
  MyNat_u
  (λ (x_85434102 : ArgList (Natprod ::RT λ (ds_d3gC : Natprod), nilRT)) (v_x_85434102 : MyNat_u),
   ltac:(flattenP (λ (ds_d3gC : Natprod) (VV : MyNat_u), MyNat_wf VV ∧ True) x_85434102 v_x_85434102)).
Proof.
  buildPackG fstSF fstSF_rel fstSF__fstSF_rel fstSF_rel_funct.
Defined.

#[global] Instance fstSF_upack: @uPack (Natprod_u ::UT nilUT) MyNat_u.
Proof.
  buildUPackG fstSF_rel fstSF_rel_funct.
Defined.

Definition leb_spec (ds_d3hP ds_d3hQ : MyNat): Type :=
  SFBool.

#[global] Hint Unfold leb_spec: lia_unfold.

Definition leb (ds_d3hP ds_d3hQ : MyNat): leb_spec ds_d3hP ds_d3hQ.
Proof.
  destruct ds_d3hP as [ds_d3hP ds_d3hP_p].
  destruct ds_d3hQ as [ds_d3hQ ds_d3hQ_p].
  try revert ds_d3hQ_p; generalize dependent ds_d3hQ; induction ds_d3hP as [| n' IH_n']; intros.
  - refine SFTrue.
  - destruct ds_d3hQ as [| m'].
    + refine SFFalse.
    + refine (IH_n' ltac:(try clear IH_n'; solver) m' ltac:(try clear IH_n'; solver)).
Defined.

Inductive leb_rel: MyNat_u → MyNat_u → SFBool_u → Prop :=
  | leb_O_x: ∀ ds_d3hQ, leb_rel O_u ds_d3hQ SFTrue_u
  | leb_S_O: ∀ n', leb_rel (S_u n') O_u SFFalse_u
  | leb_S_S: ∀ n' m' (leb_res : SFBool_u), leb_rel n' m' leb_res → leb_rel (S_u n') (S_u m') leb_res.

#[global] Hint Constructors leb_rel: core_hint_db.

#[global] Instance leb_lookup_rel: dictionary rel leb := { lookup' := leb_rel }.

#[global] Instance leb_getF: getFunc leb_rel := { getF' := leb }.

Theorem leb_rel_funct [ds_d3hP ds_d3hQ : MyNat_u]:
  ∀ (VV VV' : SFBool_u), leb_rel ds_d3hP ds_d3hQ VV → (leb_rel ds_d3hP ds_d3hQ VV' → VV = VV').
Proof.
  try revert ds_d3hQ_p; generalize dependent ds_d3hQ; induction ds_d3hP as [| n' IH_n']; intros;
  [ | destruct ds_d3hQ as [| m']];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve leb_rel_funct: f_rel_funct_db.

Theorem leb_O_x_lem ds_d3hQ leb_O_x_lem_res:
  leb_rel O_u ds_d3hQ leb_O_x_lem_res ↔ leb_O_x_lem_res == SFTrue_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite leb_O_x_lem: f_rel_back.

Theorem leb_S_O_lem n' leb_S_O_lem_res:
  leb_rel (S_u n') O_u leb_S_O_lem_res ↔ leb_S_O_lem_res == SFFalse_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite leb_S_O_lem: f_rel_back.

Theorem leb_S_S_lem m' n' leb_S_S_lem_res:
  leb_rel (S_u n') (S_u m') leb_S_S_lem_res
  ↔ ∃ (leb_res : SFBool_u), leb_rel n' m' leb_res ∧ leb_S_S_lem_res == leb_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite leb_S_S_lem: f_rel_back.

Theorem leb_rel_ex
  (ds_d3hP : MyNat_u)
  (ds_d3hP_p : MyNat_wf ds_d3hP ∧ True)
  (ds_d3hQ : MyNat_u)
  (ds_d3hQ_p : MyNat_wf ds_d3hQ ∧ True):
  leb_rel ds_d3hP ds_d3hQ ⌊ leb (exist _ ds_d3hP ds_d3hP_p) (exist _ ds_d3hQ ds_d3hQ_p) -⌋.
Proof.
  Opaque leb.
  existence_lemma_pre leb;
  try revert ds_d3hQ_p; generalize dependent ds_d3hQ; induction ds_d3hP as [| n' IH_n']; intros;
  [fix_notations |
   destruct ds_d3hQ as [| m'];
   [fix_notations |
    fix_notations;
    pose proof (IH_n' ltac:(try clear IH_n'; solver) m' ltac:(try clear IH_n'; solver)) as IH_11391185;
    try clear IH_n']];
  simpl in *.
  Transparent leb.
  all: (existence_lemma_quicksolve leb; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve leb_rel_ex: rel_ax_db.

#[global] Opaque leb.

Theorem leb__leb_rel_rw
  (ds_d3hP : MyNat_u)
  (ds_d3hP_p : MyNat_wf ds_d3hP ∧ True)
  (ds_d3hQ : MyNat_u)
  (ds_d3hQ_p : MyNat_wf ds_d3hQ ∧ True)
  (VV : SFBool_u):
  ⌊ leb (exist _ ds_d3hP ds_d3hP_p) (exist _ ds_d3hQ ds_d3hQ_p) -⌋ = VV ↔ leb_rel ds_d3hP ds_d3hQ VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite leb__leb_rel_rw: f_rel_funct_db.

#[global] Hint Resolve leb__leb_rel_rw: rel_ax_db.

#[global] Instance leb_lookup_rw: dictionary rwLem leb := { lookup' := leb__leb_rel_rw }.

Theorem leb__leb_rel (ds_d3hP ds_d3hQ : MyNat) (VV : SFBool_u):
  ⌊ leb ds_d3hP ds_d3hQ -⌋ = VV ↔ leb_rel ⌊ ds_d3hP ⌋ ⌊ ds_d3hQ ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite leb__leb_rel: f_rel_funct_db.

Theorem leb__leb_rel' (ds_d3hP_u ds_d3hQ_u : MyNat_u) (ds_d3hP ds_d3hQ : MyNat) (VV : SFBool_u):
  ds_d3hP_u = ⌊ ds_d3hP ⌋
  → (ds_d3hQ_u = ⌊ ds_d3hQ ⌋ → ⌊ leb ds_d3hP ds_d3hQ -⌋ = VV ↔ leb_rel ds_d3hP_u ds_d3hQ_u VV).
Proof.
  intros -> ->. refine (leb__leb_rel ds_d3hP ds_d3hQ VV).
Qed.

#[global] Hint Resolve leb__leb_rel': f_rel_funct_db.

Theorem leb_rel_mk
  (ds_d3hP : MyNat_u)
  (ds_d3hP_p : MyNat_wf ds_d3hP ∧ True)
  (ds_d3hQ : MyNat_u)
  (ds_d3hQ_p : MyNat_wf ds_d3hQ ∧ True):
  {VV: _ | leb_rel ds_d3hP ds_d3hQ VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, leb_rel ds_d3hP ds_d3hQ VV)
          (leb (exist _ ds_d3hP ds_d3hP_p) (exist _ ds_d3hQ ds_d3hQ_p))
          _);
  rewrite <- leb__leb_rel';
  quicksolve.
Qed.

#[global] Hint Resolve leb_rel_mk: f_rel_funct_db.

#[global] Instance leb_pack:
  @Pack
  (MyNat ::RT λ (ds_d3hP : MyNat), MyNat ::RT λ (ds_d3hQ : MyNat), nilRT)
  (MyNat_u ::UT (MyNat_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((MyNat
  ::RT λ (ds_d3hP : MyNat), MyNat ::RT λ (ds_d3hQ : MyNat), nilRT)) ((MyNat_u ::UT (MyNat_u ::UT nilUT))))
  SFBool_u
  (λ (x_71676628 : ArgList (MyNat ::RT λ (ds_d3hP : MyNat), MyNat ::RT λ (ds_d3hQ : MyNat), nilRT))
     (v_x_71676628 : SFBool_u),
   ltac:(flattenP (λ (ds_d3hP ds_d3hQ : MyNat) (VV : SFBool_u), SFBool_wf VV ∧ True) x_71676628 v_x_71676628)).
Proof.
  buildPackG leb leb_rel leb__leb_rel leb_rel_funct.
Defined.

#[global] Instance leb_upack: @uPack (MyNat_u ::UT (MyNat_u ::UT nilUT)) SFBool_u.
Proof.
  buildUPackG leb_rel leb_rel_funct.
Defined.

Definition ltb_spec (ds_d3hN ds_d3hO : MyNat): Type :=
  SFBool.

#[global] Hint Unfold ltb_spec: lia_unfold.

Definition ltb (ds_d3hN ds_d3hO : MyNat): ltb_spec ds_d3hN ds_d3hO.
Proof.
  destruct ds_d3hN as [ds_d3hN ds_d3hN_p].
  destruct ds_d3hO as [ds_d3hO ds_d3hO_p].
  try revert ds_d3hO_p; generalize dependent ds_d3hO; induction ds_d3hN as [| n' IH_n']; intros.
  - destruct ds_d3hO as [| m'].
    + refine SFFalse.
    + refine SFTrue.
  - destruct ds_d3hO as [| m'].
    + refine SFFalse.
    + refine (IH_n' ltac:(try clear IH_n'; solver) m' ltac:(try clear IH_n'; solver)).
Defined.

Inductive ltb_rel: MyNat_u → MyNat_u → SFBool_u → Prop :=
  | ltb_O_O: ltb_rel O_u O_u SFFalse_u
  | ltb_O_S: ∀ m', ltb_rel O_u (S_u m') SFTrue_u
  | ltb_S_O: ∀ n', ltb_rel (S_u n') O_u SFFalse_u
  | ltb_S_S: ∀ n' m' (ltb_res : SFBool_u), ltb_rel n' m' ltb_res → ltb_rel (S_u n') (S_u m') ltb_res.

#[global] Hint Constructors ltb_rel: core_hint_db.

#[global] Instance ltb_lookup_rel: dictionary rel ltb := { lookup' := ltb_rel }.

#[global] Instance ltb_getF: getFunc ltb_rel := { getF' := ltb }.

Theorem ltb_rel_funct [ds_d3hN ds_d3hO : MyNat_u]:
  ∀ (VV VV' : SFBool_u), ltb_rel ds_d3hN ds_d3hO VV → (ltb_rel ds_d3hN ds_d3hO VV' → VV = VV').
Proof.
  try revert ds_d3hO_p; generalize dependent ds_d3hO; induction ds_d3hN as [| n' IH_n']; intros;
  [destruct ds_d3hO as [| m'] | destruct ds_d3hO as [| m']];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve ltb_rel_funct: f_rel_funct_db.

Theorem ltb_O_O_lem ltb_O_O_lem_res: ltb_rel O_u O_u ltb_O_O_lem_res ↔ ltb_O_O_lem_res == SFFalse_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite ltb_O_O_lem: f_rel_back.

Theorem ltb_O_S_lem m' ltb_O_S_lem_res:
  ltb_rel O_u (S_u m') ltb_O_S_lem_res ↔ ltb_O_S_lem_res == SFTrue_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite ltb_O_S_lem: f_rel_back.

Theorem ltb_S_O_lem n' ltb_S_O_lem_res:
  ltb_rel (S_u n') O_u ltb_S_O_lem_res ↔ ltb_S_O_lem_res == SFFalse_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite ltb_S_O_lem: f_rel_back.

Theorem ltb_S_S_lem m' n' ltb_S_S_lem_res:
  ltb_rel (S_u n') (S_u m') ltb_S_S_lem_res
  ↔ ∃ (ltb_res : SFBool_u), ltb_rel n' m' ltb_res ∧ ltb_S_S_lem_res == ltb_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite ltb_S_S_lem: f_rel_back.

Theorem ltb_rel_ex
  (ds_d3hN : MyNat_u)
  (ds_d3hN_p : MyNat_wf ds_d3hN ∧ True)
  (ds_d3hO : MyNat_u)
  (ds_d3hO_p : MyNat_wf ds_d3hO ∧ True):
  ltb_rel ds_d3hN ds_d3hO ⌊ ltb (exist _ ds_d3hN ds_d3hN_p) (exist _ ds_d3hO ds_d3hO_p) -⌋.
Proof.
  Opaque ltb.
  existence_lemma_pre ltb;
  try revert ds_d3hO_p; generalize dependent ds_d3hO; induction ds_d3hN as [| n' IH_n']; intros;
  [destruct ds_d3hO as [| m'];
   [fix_notations | fix_notations] |
   destruct ds_d3hO as [| m'];
   [fix_notations |
    fix_notations;
    pose proof (IH_n' ltac:(try clear IH_n'; solver) m' ltac:(try clear IH_n'; solver)) as IH_11391185;
    try clear IH_n']];
  simpl in *.
  Transparent ltb.
  all: (existence_lemma_quicksolve ltb; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve ltb_rel_ex: rel_ax_db.

#[global] Opaque ltb.

Theorem ltb__ltb_rel_rw
  (ds_d3hN : MyNat_u)
  (ds_d3hN_p : MyNat_wf ds_d3hN ∧ True)
  (ds_d3hO : MyNat_u)
  (ds_d3hO_p : MyNat_wf ds_d3hO ∧ True)
  (VV : SFBool_u):
  ⌊ ltb (exist _ ds_d3hN ds_d3hN_p) (exist _ ds_d3hO ds_d3hO_p) -⌋ = VV ↔ ltb_rel ds_d3hN ds_d3hO VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite ltb__ltb_rel_rw: f_rel_funct_db.

#[global] Hint Resolve ltb__ltb_rel_rw: rel_ax_db.

#[global] Instance ltb_lookup_rw: dictionary rwLem ltb := { lookup' := ltb__ltb_rel_rw }.

Theorem ltb__ltb_rel (ds_d3hN ds_d3hO : MyNat) (VV : SFBool_u):
  ⌊ ltb ds_d3hN ds_d3hO -⌋ = VV ↔ ltb_rel ⌊ ds_d3hN ⌋ ⌊ ds_d3hO ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite ltb__ltb_rel: f_rel_funct_db.

Theorem ltb__ltb_rel' (ds_d3hN_u ds_d3hO_u : MyNat_u) (ds_d3hN ds_d3hO : MyNat) (VV : SFBool_u):
  ds_d3hN_u = ⌊ ds_d3hN ⌋
  → (ds_d3hO_u = ⌊ ds_d3hO ⌋ → ⌊ ltb ds_d3hN ds_d3hO -⌋ = VV ↔ ltb_rel ds_d3hN_u ds_d3hO_u VV).
Proof.
  intros -> ->. refine (ltb__ltb_rel ds_d3hN ds_d3hO VV).
Qed.

#[global] Hint Resolve ltb__ltb_rel': f_rel_funct_db.

Theorem ltb_rel_mk
  (ds_d3hN : MyNat_u)
  (ds_d3hN_p : MyNat_wf ds_d3hN ∧ True)
  (ds_d3hO : MyNat_u)
  (ds_d3hO_p : MyNat_wf ds_d3hO ∧ True):
  {VV: _ | ltb_rel ds_d3hN ds_d3hO VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, ltb_rel ds_d3hN ds_d3hO VV)
          (ltb (exist _ ds_d3hN ds_d3hN_p) (exist _ ds_d3hO ds_d3hO_p))
          _);
  rewrite <- ltb__ltb_rel';
  quicksolve.
Qed.

#[global] Hint Resolve ltb_rel_mk: f_rel_funct_db.

#[global] Instance ltb_pack:
  @Pack
  (MyNat ::RT λ (ds_d3hN : MyNat), MyNat ::RT λ (ds_d3hO : MyNat), nilRT)
  (MyNat_u ::UT (MyNat_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((MyNat
  ::RT λ (ds_d3hN : MyNat), MyNat ::RT λ (ds_d3hO : MyNat), nilRT)) ((MyNat_u ::UT (MyNat_u ::UT nilUT))))
  SFBool_u
  (λ (x_79245289 : ArgList (MyNat ::RT λ (ds_d3hN : MyNat), MyNat ::RT λ (ds_d3hO : MyNat), nilRT))
     (v_x_79245289 : SFBool_u),
   ltac:(flattenP (λ (ds_d3hN ds_d3hO : MyNat) (VV : SFBool_u), SFBool_wf VV ∧ True) x_79245289 v_x_79245289)).
Proof.
  buildPackG ltb ltb_rel ltb__ltb_rel ltb_rel_funct.
Defined.

#[global] Instance ltb_upack: @uPack (MyNat_u ::UT (MyNat_u ::UT nilUT)) SFBool_u.
Proof.
  buildUPackG ltb_rel ltb_rel_funct.
Defined.

Definition minus_spec (ds_d3hT ds_d3hU : MyNat): Type :=
  MyNat.

#[global] Hint Unfold minus_spec: lia_unfold.

Definition minus (ds_d3hT ds_d3hU : MyNat): minus_spec ds_d3hT ds_d3hU.
Proof.
  destruct ds_d3hT as [ds_d3hT ds_d3hT_p].
  destruct ds_d3hU as [ds_d3hU ds_d3hU_p].
  try revert ds_d3hU_p; generalize dependent ds_d3hU;
  induction ds_d3hT as [| ds_d3hV IH_ds_d3hV];
  intros.
  - refine O.
  - destruct ds_d3hU as [| m'].
    + refine (S (exist (λ (VV : MyNat_u), MyNat_wf VV ∧ True) ds_d3hV ltac:(solver))).
    + refine (IH_ds_d3hV ltac:(try clear IH_ds_d3hV; solver) m' ltac:(try clear IH_ds_d3hV; solver)).
Defined.

Inductive minus_rel: MyNat_u → MyNat_u → MyNat_u → Prop :=
  | minus_O_x: ∀ ds_d3hU, minus_rel O_u ds_d3hU O_u
  | minus_S_O: ∀ ds_d3hV, minus_rel (S_u ds_d3hV) O_u (S_u ds_d3hV)
  | minus_S_S: ∀ ds_d3hV m' (minus_res : MyNat_u),
               minus_rel ds_d3hV m' minus_res → minus_rel (S_u ds_d3hV) (S_u m') minus_res.

#[global] Hint Constructors minus_rel: core_hint_db.

#[global] Instance minus_lookup_rel: dictionary rel minus := { lookup' := minus_rel }.

#[global] Instance minus_getF: getFunc minus_rel := { getF' := minus }.

Theorem minus_rel_funct [ds_d3hT ds_d3hU : MyNat_u]:
  ∀ (VV VV' : MyNat_u), minus_rel ds_d3hT ds_d3hU VV → (minus_rel ds_d3hT ds_d3hU VV' → VV = VV').
Proof.
  try revert ds_d3hU_p; generalize dependent ds_d3hU;
  induction ds_d3hT as [| ds_d3hV IH_ds_d3hV];
  intros;
  [ | destruct ds_d3hU as [| m']];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve minus_rel_funct: f_rel_funct_db.

Theorem minus_O_x_lem ds_d3hU minus_O_x_lem_res:
  minus_rel O_u ds_d3hU minus_O_x_lem_res ↔ minus_O_x_lem_res == O_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite minus_O_x_lem: f_rel_back.

Theorem minus_S_O_lem ds_d3hV minus_S_O_lem_res:
  minus_rel (S_u ds_d3hV) O_u minus_S_O_lem_res ↔ minus_S_O_lem_res == S_u ds_d3hV.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite minus_S_O_lem: f_rel_back.

Theorem minus_S_S_lem ds_d3hV m' minus_S_S_lem_res:
  minus_rel (S_u ds_d3hV) (S_u m') minus_S_S_lem_res
  ↔ ∃ (minus_res : MyNat_u), minus_rel ds_d3hV m' minus_res ∧ minus_S_S_lem_res == minus_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite minus_S_S_lem: f_rel_back.

Theorem minus_rel_ex
  (ds_d3hT : MyNat_u)
  (ds_d3hT_p : MyNat_wf ds_d3hT ∧ True)
  (ds_d3hU : MyNat_u)
  (ds_d3hU_p : MyNat_wf ds_d3hU ∧ True):
  minus_rel ds_d3hT ds_d3hU ⌊ minus (exist _ ds_d3hT ds_d3hT_p) (exist _ ds_d3hU ds_d3hU_p) -⌋.
Proof.
  Opaque minus.
  existence_lemma_pre minus;
  try revert ds_d3hU_p; generalize dependent ds_d3hU;
  induction ds_d3hT as [| ds_d3hV IH_ds_d3hV];
  intros;
  [fix_notations |
   destruct ds_d3hU as [| m'];
   [fix_notations |
    fix_notations;
    pose proof (IH_ds_d3hV
                ltac:(try clear IH_ds_d3hV; solver)
                m'
                ltac:(try clear IH_ds_d3hV; solver)) as IH_25749285;
    try clear IH_ds_d3hV]];
  simpl in *.
  Transparent minus.
  all: (existence_lemma_quicksolve minus; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve minus_rel_ex: rel_ax_db.

#[global] Opaque minus.

Theorem minus__minus_rel_rw
  (ds_d3hT : MyNat_u)
  (ds_d3hT_p : MyNat_wf ds_d3hT ∧ True)
  (ds_d3hU : MyNat_u)
  (ds_d3hU_p : MyNat_wf ds_d3hU ∧ True)
  (VV : MyNat_u):
  ⌊ minus (exist _ ds_d3hT ds_d3hT_p) (exist _ ds_d3hU ds_d3hU_p) -⌋ = VV
  ↔ minus_rel ds_d3hT ds_d3hU VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite minus__minus_rel_rw: f_rel_funct_db.

#[global] Hint Resolve minus__minus_rel_rw: rel_ax_db.

#[global] Instance minus_lookup_rw: dictionary rwLem minus := { lookup' := minus__minus_rel_rw }.

Theorem minus__minus_rel (ds_d3hT ds_d3hU : MyNat) (VV : MyNat_u):
  ⌊ minus ds_d3hT ds_d3hU -⌋ = VV ↔ minus_rel ⌊ ds_d3hT ⌋ ⌊ ds_d3hU ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite minus__minus_rel: f_rel_funct_db.

Theorem minus__minus_rel' (ds_d3hT_u ds_d3hU_u : MyNat_u) (ds_d3hT ds_d3hU : MyNat) (VV : MyNat_u):
  ds_d3hT_u = ⌊ ds_d3hT ⌋
  → (ds_d3hU_u = ⌊ ds_d3hU ⌋ → ⌊ minus ds_d3hT ds_d3hU -⌋ = VV ↔ minus_rel ds_d3hT_u ds_d3hU_u VV).
Proof.
  intros -> ->. refine (minus__minus_rel ds_d3hT ds_d3hU VV).
Qed.

#[global] Hint Resolve minus__minus_rel': f_rel_funct_db.

Theorem minus_rel_mk
  (ds_d3hT : MyNat_u)
  (ds_d3hT_p : MyNat_wf ds_d3hT ∧ True)
  (ds_d3hU : MyNat_u)
  (ds_d3hU_p : MyNat_wf ds_d3hU ∧ True):
  {VV: _ | minus_rel ds_d3hT ds_d3hU VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, minus_rel ds_d3hT ds_d3hU VV)
          (minus (exist _ ds_d3hT ds_d3hT_p) (exist _ ds_d3hU ds_d3hU_p))
          _);
  rewrite <- minus__minus_rel';
  quicksolve.
Qed.

#[global] Hint Resolve minus_rel_mk: f_rel_funct_db.

#[global] Instance minus_pack:
  @Pack
  (MyNat ::RT λ (ds_d3hT : MyNat), MyNat ::RT λ (ds_d3hU : MyNat), nilRT)
  (MyNat_u ::UT (MyNat_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((MyNat
  ::RT λ (ds_d3hT : MyNat), MyNat ::RT λ (ds_d3hU : MyNat), nilRT)) ((MyNat_u ::UT (MyNat_u ::UT nilUT))))
  MyNat_u
  (λ (x_23017964 : ArgList (MyNat ::RT λ (ds_d3hT : MyNat), MyNat ::RT λ (ds_d3hU : MyNat), nilRT))
     (v_x_23017964 : MyNat_u),
   ltac:(flattenP (λ (ds_d3hT ds_d3hU : MyNat) (VV : MyNat_u), MyNat_wf VV ∧ True) x_23017964 v_x_23017964)).
Proof.
  buildPackG minus minus_rel minus__minus_rel minus_rel_funct.
Defined.

#[global] Instance minus_upack: @uPack (MyNat_u ::UT (MyNat_u ::UT nilUT)) MyNat_u.
Proof.
  buildUPackG minus_rel minus_rel_funct.
Defined.

Definition minus_n_n_spec (ds_d3gF : MyNat): Type :=
  {{∃ (minus_res : MyNat_u), minus_rel ⌊ ds_d3gF ⌋ ⌊ ds_d3gF ⌋ minus_res ∧ minus_res == O_u}}.

#[global] Hint Unfold minus_n_n_spec: lia_unfold.

Theorem minus_n_n (ds_d3gF : MyNat): minus_n_n_spec ds_d3gF.
Proof.
  destruct ds_d3gF as [ds_d3gF ds_d3gF_p].
  induction ds_d3gF as [| n' IH_n'].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (minus_res : MyNat_u), minus_rel O_u O_u minus_res ∧ minus_res == O_u)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (minus_res : MyNat_u), minus_rel (S_u n') (S_u n') minus_res ∧ minus_res == O_u)
            (IH_n' ltac:(try clear IH_n'; solver))
            ltac:(solver)).
Qed.

Definition minustwo_spec (ds_d3ik : MyNat): Type :=
  MyNat.

#[global] Hint Unfold minustwo_spec: lia_unfold.

Definition minustwo (ds_d3ik : MyNat): minustwo_spec ds_d3ik.
Proof.
  destruct ds_d3ik as [ds_d3ik ds_d3ik_p].
  destruct ds_d3ik as [| ds_d3il].
  - refine O.
  - destruct ds_d3il as [| n'].
    + refine O.
    + refine (exist (λ (VV : MyNat_u), MyNat_wf VV ∧ True) n' ltac:(solver)).
Defined.

Definition one_spec : Type :=
  MyNat.

#[global] Hint Unfold one_spec: lia_unfold.

Definition one : one_spec.
Proof.
  refine (S O).
Defined.

Definition plus_spec (ds_d3i8 m : MyNat): Type :=
  MyNat.

#[global] Hint Unfold plus_spec: lia_unfold.

Definition plus (ds_d3i8 m : MyNat): plus_spec ds_d3i8 m.
Proof.
  destruct ds_d3i8 as [ds_d3i8 ds_d3i8_p].
  destruct m as [m m_p].
  try revert m_p; generalize dependent m; induction ds_d3i8 as [| n' IH_n']; intros.
  - refine (exist (λ (m : MyNat_u), MyNat_wf m ∧ True) m ltac:(solver)).
  - refine (S (IH_n' ltac:(try clear IH_n'; solver) m ltac:(try clear IH_n'; solver))).
Defined.

Inductive plus_rel: MyNat_u → MyNat_u → MyNat_u → Prop :=
  | plus_O_x: ∀ m, plus_rel O_u m m
  | plus_S_x: ∀ n' m (plus_res : MyNat_u),
              plus_rel n' m plus_res → plus_rel (S_u n') m (S_u plus_res).

#[global] Hint Constructors plus_rel: core_hint_db.

#[global] Instance plus_lookup_rel: dictionary rel plus := { lookup' := plus_rel }.

#[global] Instance plus_getF: getFunc plus_rel := { getF' := plus }.

Theorem plus_rel_funct [ds_d3i8 m : MyNat_u]:
  ∀ (VV VV' : MyNat_u), plus_rel ds_d3i8 m VV → (plus_rel ds_d3i8 m VV' → VV = VV').
Proof.
  try revert m_p; generalize dependent m; induction ds_d3i8 as [| n' IH_n']; intros;
  rel_functionhood_body.
Qed.

#[global] Hint Resolve plus_rel_funct: f_rel_funct_db.

Theorem plus_O_x_lem m plus_O_x_lem_res: plus_rel O_u m plus_O_x_lem_res ↔ plus_O_x_lem_res == m.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite plus_O_x_lem: f_rel_back.

Theorem plus_S_x_lem m n' plus_S_x_lem_res:
  plus_rel (S_u n') m plus_S_x_lem_res
  ↔ ∃ (plus_res : MyNat_u), plus_rel n' m plus_res ∧ plus_S_x_lem_res == S_u plus_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite plus_S_x_lem: f_rel_back.

Theorem plus_rel_ex
  (ds_d3i8 : MyNat_u) (ds_d3i8_p : MyNat_wf ds_d3i8 ∧ True) (m : MyNat_u) (m_p : MyNat_wf m ∧ True):
  plus_rel ds_d3i8 m ⌊ plus (exist _ ds_d3i8 ds_d3i8_p) (exist _ m m_p) -⌋.
Proof.
  Opaque plus.
  existence_lemma_pre plus;
  try revert m_p; generalize dependent m; induction ds_d3i8 as [| n' IH_n']; intros;
  [fix_notations |
   fix_notations;
   pose proof (IH_n' ltac:(try clear IH_n'; solver) m ltac:(try clear IH_n'; solver)) as IH_47989236;
   try clear IH_n'];
  simpl in *.
  Transparent plus.
  all: (existence_lemma_quicksolve plus; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve plus_rel_ex: rel_ax_db.

#[global] Opaque plus.

Theorem plus__plus_rel_rw
  (ds_d3i8 : MyNat_u)
  (ds_d3i8_p : MyNat_wf ds_d3i8 ∧ True)
  (m : MyNat_u)
  (m_p : MyNat_wf m ∧ True)
  (VV : MyNat_u):
  ⌊ plus (exist _ ds_d3i8 ds_d3i8_p) (exist _ m m_p) -⌋ = VV ↔ plus_rel ds_d3i8 m VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite plus__plus_rel_rw: f_rel_funct_db.

#[global] Hint Resolve plus__plus_rel_rw: rel_ax_db.

#[global] Instance plus_lookup_rw: dictionary rwLem plus := { lookup' := plus__plus_rel_rw }.

Theorem plus__plus_rel (ds_d3i8 m : MyNat) (VV : MyNat_u):
  ⌊ plus ds_d3i8 m -⌋ = VV ↔ plus_rel ⌊ ds_d3i8 ⌋ ⌊ m ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite plus__plus_rel: f_rel_funct_db.

Theorem plus__plus_rel' (ds_d3i8_u m_u : MyNat_u) (ds_d3i8 m : MyNat) (VV : MyNat_u):
  ds_d3i8_u = ⌊ ds_d3i8 ⌋ → (m_u = ⌊ m ⌋ → ⌊ plus ds_d3i8 m -⌋ = VV ↔ plus_rel ds_d3i8_u m_u VV).
Proof.
  intros -> ->. refine (plus__plus_rel ds_d3i8 m VV).
Qed.

#[global] Hint Resolve plus__plus_rel': f_rel_funct_db.

Theorem plus_rel_mk
  (ds_d3i8 : MyNat_u) (ds_d3i8_p : MyNat_wf ds_d3i8 ∧ True) (m : MyNat_u) (m_p : MyNat_wf m ∧ True):
  {VV: _ | plus_rel ds_d3i8 m VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, plus_rel ds_d3i8 m VV)
          (plus (exist _ ds_d3i8 ds_d3i8_p) (exist _ m m_p))
          _);
  rewrite <- plus__plus_rel';
  quicksolve.
Qed.

#[global] Hint Resolve plus_rel_mk: f_rel_funct_db.

#[global] Instance plus_pack:
  @Pack
  (MyNat ::RT λ (ds_d3i8 : MyNat), MyNat ::RT λ (m : MyNat), nilRT)
  (MyNat_u ::UT (MyNat_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((MyNat ::RT λ (ds_d3i8 : MyNat), MyNat ::RT λ (m : MyNat), nilRT)) ((MyNat_u ::UT (MyNat_u ::UT nilUT))))
  MyNat_u
  (λ (x_16277600 : ArgList (MyNat ::RT λ (ds_d3i8 : MyNat), MyNat ::RT λ (m : MyNat), nilRT))
     (v_x_16277600 : MyNat_u),
   ltac:(flattenP (λ (ds_d3i8 m : MyNat) (VV : MyNat_u), MyNat_wf VV ∧ True) x_16277600 v_x_16277600)).
Proof.
  buildPackG plus plus_rel plus__plus_rel plus_rel_funct.
Defined.

#[global] Instance plus_upack: @uPack (MyNat_u ::UT (MyNat_u ::UT nilUT)) MyNat_u.
Proof.
  buildUPackG plus_rel plus_rel_funct.
Defined.

Definition add_0_r_spec (ds_d3gG : MyNat): Type :=
  {{∃ (plus_res : MyNat_u), plus_rel ⌊ ds_d3gG ⌋ O_u plus_res ∧ plus_res == ⌊ ds_d3gG ⌋}}.

#[global] Hint Unfold add_0_r_spec: lia_unfold.

Theorem add_0_r (ds_d3gG : MyNat): add_0_r_spec ds_d3gG.
Proof.
  destruct ds_d3gG as [ds_d3gG ds_d3gG_p].
  induction ds_d3gG as [| n' IH_n'].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (plus_res : MyNat_u), plus_rel O_u O_u plus_res ∧ plus_res == O_u)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (plus_res : MyNat_u), plus_rel (S_u n') O_u plus_res ∧ plus_res == S_u n')
            (IH_n' ltac:(try clear IH_n'; solver))
            ltac:(solver)).
Qed.

Definition add_assoc_spec (ds_d3hH ds_d3hI ds_d3hJ : MyNat): Type :=
  {{∃ (plus_res : MyNat_u),
    plus_rel ⌊ ds_d3hI ⌋ ⌊ ds_d3hJ ⌋ plus_res
    ∧ ∃ (plus_res_2 : MyNat_u),
      plus_rel ⌊ ds_d3hH ⌋ plus_res plus_res_2
      ∧ ∃ (plus_res_3 : MyNat_u),
        plus_rel ⌊ ds_d3hH ⌋ ⌊ ds_d3hI ⌋ plus_res_3
        ∧ ∃ (plus_res_4 : MyNat_u),
          plus_rel plus_res_3 ⌊ ds_d3hJ ⌋ plus_res_4 ∧ plus_res_2 == plus_res_4}}.

#[global] Hint Unfold add_assoc_spec: lia_unfold.

Theorem add_assoc (ds_d3hH ds_d3hI ds_d3hJ : MyNat): add_assoc_spec ds_d3hH ds_d3hI ds_d3hJ.
Proof.
  destruct ds_d3hH as [ds_d3hH ds_d3hH_p].
  destruct ds_d3hI as [ds_d3hI ds_d3hI_p].
  destruct ds_d3hJ as [ds_d3hJ ds_d3hJ_p].
  try revert ds_d3hJ_p; generalize dependent ds_d3hJ;
  try revert ds_d3hI_p; generalize dependent ds_d3hI;
  induction ds_d3hH as [| n' IH_n'];
  intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (plus_res : MyNat_u),
             plus_rel ds_d3hI ds_d3hJ plus_res
             ∧ ∃ (plus_res_2 : MyNat_u),
               plus_rel O_u plus_res plus_res_2
               ∧ ∃ (plus_res_3 : MyNat_u),
                 plus_rel O_u ds_d3hI plus_res_3
                 ∧ ∃ (plus_res_4 : MyNat_u), plus_rel plus_res_3 ds_d3hJ plus_res_4 ∧ plus_res_2 == plus_res_4)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (plus_res : MyNat_u),
             plus_rel ds_d3hI ds_d3hJ plus_res
             ∧ ∃ (plus_res_2 : MyNat_u),
               plus_rel (S_u n') plus_res plus_res_2
               ∧ ∃ (plus_res_3 : MyNat_u),
                 plus_rel (S_u n') ds_d3hI plus_res_3
                 ∧ ∃ (plus_res_4 : MyNat_u), plus_rel plus_res_3 ds_d3hJ plus_res_4 ∧ plus_res_2 == plus_res_4)
            (IH_n'
             ltac:(try clear IH_n'; solver)
             ds_d3hI
             ltac:(try clear IH_n'; solver)
             ds_d3hJ
             ltac:(try clear IH_n'; solver))
            ltac:(solver)).
Qed.

Definition add_succ_r_spec (ds_d3hK ds_d3hL : MyNat): Type :=
  {{∃ (plus_res : MyNat_u),
    plus_rel ⌊ ds_d3hK ⌋ (S_u ⌊ ds_d3hL ⌋) plus_res
    ∧ ∃ (plus_res_2 : MyNat_u),
      plus_rel ⌊ ds_d3hK ⌋ ⌊ ds_d3hL ⌋ plus_res_2 ∧ plus_res == S_u plus_res_2}}.

#[global] Hint Unfold add_succ_r_spec: lia_unfold.

Theorem add_succ_r (ds_d3hK ds_d3hL : MyNat): add_succ_r_spec ds_d3hK ds_d3hL.
Proof.
  destruct ds_d3hK as [ds_d3hK ds_d3hK_p].
  destruct ds_d3hL as [ds_d3hL ds_d3hL_p].
  try revert ds_d3hL_p; generalize dependent ds_d3hL; induction ds_d3hK as [| n' IH_n']; intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (plus_res : MyNat_u),
             plus_rel O_u (S_u ds_d3hL) plus_res
             ∧ ∃ (plus_res_2 : MyNat_u), plus_rel O_u ds_d3hL plus_res_2 ∧ plus_res == S_u plus_res_2)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (plus_res : MyNat_u),
             plus_rel (S_u n') (S_u ds_d3hL) plus_res
             ∧ ∃ (plus_res_2 : MyNat_u), plus_rel (S_u n') ds_d3hL plus_res_2 ∧ plus_res == S_u plus_res_2)
            (IH_n' ltac:(try clear IH_n'; solver) ds_d3hL ltac:(try clear IH_n'; solver))
            ltac:(solver)).
Qed.

Definition mult_spec (ds_d3ia ds_d3ib : MyNat): Type :=
  MyNat.

#[global] Hint Unfold mult_spec: lia_unfold.

Definition mult (ds_d3ia ds_d3ib : MyNat): mult_spec ds_d3ia ds_d3ib.
Proof.
  destruct ds_d3ia as [ds_d3ia ds_d3ia_p].
  destruct ds_d3ib as [ds_d3ib ds_d3ib_p].
  try revert ds_d3ib_p; generalize dependent ds_d3ib; induction ds_d3ia as [| n' IH_n']; intros.
  - refine O.
  - refine (plus
            (exist (λ (ds_d3ib : MyNat_u), MyNat_wf ds_d3ib ∧ True) ds_d3ib ltac:(solver))
            (IH_n' ltac:(try clear IH_n'; solver) ds_d3ib ltac:(try clear IH_n'; solver))).
Defined.

Inductive mult_rel: MyNat_u → MyNat_u → MyNat_u → Prop :=
  | mult_O_x: ∀ ds_d3ib, mult_rel O_u ds_d3ib O_u
  | mult_S_x: ∀ n' ds_d3ib (mult_res : MyNat_u),
              mult_rel n' ds_d3ib mult_res
              → ∀ (plus_res : MyNat_u), plus_rel ds_d3ib mult_res plus_res → mult_rel (S_u n') ds_d3ib plus_res.

#[global] Hint Constructors mult_rel: core_hint_db.

#[global] Instance mult_lookup_rel: dictionary rel mult := { lookup' := mult_rel }.

#[global] Instance mult_getF: getFunc mult_rel := { getF' := mult }.

Theorem mult_rel_funct [ds_d3ia ds_d3ib : MyNat_u]:
  ∀ (VV VV' : MyNat_u), mult_rel ds_d3ia ds_d3ib VV → (mult_rel ds_d3ia ds_d3ib VV' → VV = VV').
Proof.
  try revert ds_d3ib_p; generalize dependent ds_d3ib; induction ds_d3ia as [| n' IH_n']; intros;
  rel_functionhood_body.
Qed.

#[global] Hint Resolve mult_rel_funct: f_rel_funct_db.

Theorem mult_O_x_lem ds_d3ib mult_O_x_lem_res:
  mult_rel O_u ds_d3ib mult_O_x_lem_res ↔ mult_O_x_lem_res == O_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite mult_O_x_lem: f_rel_back.

Theorem mult_S_x_lem ds_d3ib n' mult_S_x_lem_res:
  mult_rel (S_u n') ds_d3ib mult_S_x_lem_res
  ↔ ∃ (mult_res : MyNat_u),
    mult_rel n' ds_d3ib mult_res
    ∧ ∃ (plus_res : MyNat_u), plus_rel ds_d3ib mult_res plus_res ∧ mult_S_x_lem_res == plus_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite mult_S_x_lem: f_rel_back.

Theorem mult_rel_ex
  (ds_d3ia : MyNat_u)
  (ds_d3ia_p : MyNat_wf ds_d3ia ∧ True)
  (ds_d3ib : MyNat_u)
  (ds_d3ib_p : MyNat_wf ds_d3ib ∧ True):
  mult_rel ds_d3ia ds_d3ib ⌊ mult (exist _ ds_d3ia ds_d3ia_p) (exist _ ds_d3ib ds_d3ib_p) -⌋.
Proof.
  Opaque mult.
  existence_lemma_pre mult;
  try revert ds_d3ib_p; generalize dependent ds_d3ib; induction ds_d3ia as [| n' IH_n']; intros;
  [fix_notations |
   fix_notations;
   pose proof (IH_n'
               ltac:(try clear IH_n'; solver)
               ds_d3ib
               ltac:(try clear IH_n'; solver)) as IH_70239137;
   try clear IH_n'];
  simpl in *.
  Transparent mult.
  all: (existence_lemma_quicksolve mult; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve mult_rel_ex: rel_ax_db.

#[global] Opaque mult.

Theorem mult__mult_rel_rw
  (ds_d3ia : MyNat_u)
  (ds_d3ia_p : MyNat_wf ds_d3ia ∧ True)
  (ds_d3ib : MyNat_u)
  (ds_d3ib_p : MyNat_wf ds_d3ib ∧ True)
  (VV : MyNat_u):
  ⌊ mult (exist _ ds_d3ia ds_d3ia_p) (exist _ ds_d3ib ds_d3ib_p) -⌋ = VV
  ↔ mult_rel ds_d3ia ds_d3ib VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite mult__mult_rel_rw: f_rel_funct_db.

#[global] Hint Resolve mult__mult_rel_rw: rel_ax_db.

#[global] Instance mult_lookup_rw: dictionary rwLem mult := { lookup' := mult__mult_rel_rw }.

Theorem mult__mult_rel (ds_d3ia ds_d3ib : MyNat) (VV : MyNat_u):
  ⌊ mult ds_d3ia ds_d3ib -⌋ = VV ↔ mult_rel ⌊ ds_d3ia ⌋ ⌊ ds_d3ib ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite mult__mult_rel: f_rel_funct_db.

Theorem mult__mult_rel' (ds_d3ia_u ds_d3ib_u : MyNat_u) (ds_d3ia ds_d3ib : MyNat) (VV : MyNat_u):
  ds_d3ia_u = ⌊ ds_d3ia ⌋
  → (ds_d3ib_u = ⌊ ds_d3ib ⌋ → ⌊ mult ds_d3ia ds_d3ib -⌋ = VV ↔ mult_rel ds_d3ia_u ds_d3ib_u VV).
Proof.
  intros -> ->. refine (mult__mult_rel ds_d3ia ds_d3ib VV).
Qed.

#[global] Hint Resolve mult__mult_rel': f_rel_funct_db.

Theorem mult_rel_mk
  (ds_d3ia : MyNat_u)
  (ds_d3ia_p : MyNat_wf ds_d3ia ∧ True)
  (ds_d3ib : MyNat_u)
  (ds_d3ib_p : MyNat_wf ds_d3ib ∧ True):
  {VV: _ | mult_rel ds_d3ia ds_d3ib VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, mult_rel ds_d3ia ds_d3ib VV)
          (mult (exist _ ds_d3ia ds_d3ia_p) (exist _ ds_d3ib ds_d3ib_p))
          _);
  rewrite <- mult__mult_rel';
  quicksolve.
Qed.

#[global] Hint Resolve mult_rel_mk: f_rel_funct_db.

#[global] Instance mult_pack:
  @Pack
  (MyNat ::RT λ (ds_d3ia : MyNat), MyNat ::RT λ (ds_d3ib : MyNat), nilRT)
  (MyNat_u ::UT (MyNat_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((MyNat
  ::RT λ (ds_d3ia : MyNat), MyNat ::RT λ (ds_d3ib : MyNat), nilRT)) ((MyNat_u ::UT (MyNat_u ::UT nilUT))))
  MyNat_u
  (λ (x_18527579 : ArgList (MyNat ::RT λ (ds_d3ia : MyNat), MyNat ::RT λ (ds_d3ib : MyNat), nilRT))
     (v_x_18527579 : MyNat_u),
   ltac:(flattenP (λ (ds_d3ia ds_d3ib : MyNat) (VV : MyNat_u), MyNat_wf VV ∧ True) x_18527579 v_x_18527579)).
Proof.
  buildPackG mult mult_rel mult__mult_rel mult_rel_funct.
Defined.

#[global] Instance mult_upack: @uPack (MyNat_u ::UT (MyNat_u ::UT nilUT)) MyNat_u.
Proof.
  buildUPackG mult_rel mult_rel_funct.
Defined.

Definition factorial_spec (ds_d3if : MyNat): Type :=
  MyNat.

#[global] Hint Unfold factorial_spec: lia_unfold.

Definition factorial (ds_d3if : MyNat): factorial_spec ds_d3if.
Proof.
  destruct ds_d3if as [ds_d3if ds_d3if_p].
  induction ds_d3if as [| n' IH_n'].
  - refine (S O).
  - refine (mult
            (S (exist (λ (VV : MyNat_u), MyNat_wf VV ∧ True) n' ltac:(solver)))
            (IH_n' ltac:(try clear IH_n'; solver))).
Defined.

Inductive factorial_rel: MyNat_u → MyNat_u → Prop :=
  | factorial_O: factorial_rel O_u (S_u O_u)
  | factorial_S: ∀ n' (factorial_res : MyNat_u),
                 factorial_rel n' factorial_res
                 → ∀ (mult_res : MyNat_u),
                   mult_rel (S_u n') factorial_res mult_res → factorial_rel (S_u n') mult_res.

#[global] Hint Constructors factorial_rel: core_hint_db.

#[global] Instance factorial_lookup_rel: dictionary rel factorial := { lookup' := factorial_rel }.

#[global] Instance factorial_getF: getFunc factorial_rel := { getF' := factorial }.

Theorem factorial_rel_funct [ds_d3if : MyNat_u]:
  ∀ (VV VV' : MyNat_u), factorial_rel ds_d3if VV → (factorial_rel ds_d3if VV' → VV = VV').
Proof.
  induction ds_d3if as [| n' IH_n']; rel_functionhood_body.
Qed.

#[global] Hint Resolve factorial_rel_funct: f_rel_funct_db.

Theorem factorial_O_lem factorial_O_lem_res:
  factorial_rel O_u factorial_O_lem_res ↔ factorial_O_lem_res == S_u O_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite factorial_O_lem: f_rel_back.

Theorem factorial_S_lem n' factorial_S_lem_res:
  factorial_rel (S_u n') factorial_S_lem_res
  ↔ ∃ (factorial_res : MyNat_u),
    factorial_rel n' factorial_res
    ∧ ∃ (mult_res : MyNat_u),
      mult_rel (S_u n') factorial_res mult_res ∧ factorial_S_lem_res == mult_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite factorial_S_lem: f_rel_back.

Theorem factorial_rel_ex (ds_d3if : MyNat_u) (ds_d3if_p : MyNat_wf ds_d3if ∧ True):
  factorial_rel ds_d3if ⌊ factorial (exist _ ds_d3if ds_d3if_p) -⌋.
Proof.
  Opaque factorial.
  existence_lemma_pre factorial;
  induction ds_d3if as [| n' IH_n'];
  [fix_notations |
   fix_notations; pose proof (IH_n' ltac:(try clear IH_n'; solver)) as IH_36186333; try clear IH_n'];
  simpl in *.
  Transparent factorial.
  all: (existence_lemma_quicksolve factorial; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve factorial_rel_ex: rel_ax_db.

#[global] Opaque factorial.

Theorem factorial__factorial_rel_rw
  (ds_d3if : MyNat_u) (ds_d3if_p : MyNat_wf ds_d3if ∧ True) (VV : MyNat_u):
  ⌊ factorial (exist _ ds_d3if ds_d3if_p) -⌋ = VV ↔ factorial_rel ds_d3if VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite factorial__factorial_rel_rw: f_rel_funct_db.

#[global] Hint Resolve factorial__factorial_rel_rw: rel_ax_db.

#[global] Instance factorial_lookup_rw: dictionary rwLem factorial := {
    lookup' := factorial__factorial_rel_rw }.

Theorem factorial__factorial_rel (ds_d3if : MyNat) (VV : MyNat_u):
  ⌊ factorial ds_d3if -⌋ = VV ↔ factorial_rel ⌊ ds_d3if ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite factorial__factorial_rel: f_rel_funct_db.

Theorem factorial__factorial_rel' (ds_d3if_u : MyNat_u) (ds_d3if : MyNat) (VV : MyNat_u):
  ds_d3if_u = ⌊ ds_d3if ⌋ → ⌊ factorial ds_d3if -⌋ = VV ↔ factorial_rel ds_d3if_u VV.
Proof.
  intros ->. refine (factorial__factorial_rel ds_d3if VV).
Qed.

#[global] Hint Resolve factorial__factorial_rel': f_rel_funct_db.

Theorem factorial_rel_mk (ds_d3if : MyNat_u) (ds_d3if_p : MyNat_wf ds_d3if ∧ True):
  {VV: _ | factorial_rel ds_d3if VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, factorial_rel ds_d3if VV)
          (factorial (exist _ ds_d3if ds_d3if_p))
          _);
  rewrite <- factorial__factorial_rel';
  quicksolve.
Qed.

#[global] Hint Resolve factorial_rel_mk: f_rel_funct_db.

#[global] Instance factorial_pack:
  @Pack
  (MyNat ::RT λ (ds_d3if : MyNat), nilRT)
  (MyNat_u ::UT nilUT)
  ltac:(mkProjectsArgListTG ((MyNat ::RT λ (ds_d3if : MyNat), nilRT)) ((MyNat_u ::UT nilUT)))
  MyNat_u
  (λ (x_42445493 : ArgList (MyNat ::RT λ (ds_d3if : MyNat), nilRT)) (v_x_42445493 : MyNat_u),
   ltac:(flattenP (λ (ds_d3if : MyNat) (VV : MyNat_u), MyNat_wf VV ∧ True) x_42445493 v_x_42445493)).
Proof.
  buildPackG factorial factorial_rel factorial__factorial_rel factorial_rel_funct.
Defined.

#[global] Instance factorial_upack: @uPack (MyNat_u ::UT nilUT) MyNat_u.
Proof.
  buildUPackG factorial_rel factorial_rel_funct.
Defined.

Definition mul_0_r_spec (ds_d3gE : MyNat): Type :=
  {{∃ (mult_res : MyNat_u), mult_rel ⌊ ds_d3gE ⌋ O_u mult_res ∧ mult_res == O_u}}.

#[global] Hint Unfold mul_0_r_spec: lia_unfold.

Theorem mul_0_r (ds_d3gE : MyNat): mul_0_r_spec ds_d3gE.
Proof.
  destruct ds_d3gE as [ds_d3gE ds_d3gE_p].
  induction ds_d3gE as [| n' IH_n'].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (mult_res : MyNat_u), mult_rel O_u O_u mult_res ∧ mult_res == O_u)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (mult_res : MyNat_u), mult_rel (S_u n') O_u mult_res ∧ mult_res == O_u)
            (IH_n' ltac:(try clear IH_n'; solver))
            ltac:(solver)).
Qed.

Definition mult_0_1_spec (n : MyNat): Type :=
  {{∃ (mult_res : MyNat_u), mult_rel O_u ⌊ n ⌋ mult_res ∧ mult_res == O_u}}.

#[global] Hint Unfold mult_0_1_spec: lia_unfold.

Theorem mult_0_1 (n : MyNat): mult_0_1_spec n.
Proof.
  destruct n as [n n_p].
  refine (subsumptionCast
          Unit
          (λ (VV : Unit), ∃ (mult_res : MyNat_u), mult_rel O_u n mult_res ∧ mult_res == O_u)
          (# unit)
          ltac:(solver)).
Qed.

Definition mult_n_O_spec (ds_d3hM : MyNat): Type :=
  {{∃ (mult_res : MyNat_u), mult_rel ⌊ ds_d3hM ⌋ O_u mult_res ∧ O_u == mult_res}}.

#[global] Hint Unfold mult_n_O_spec: lia_unfold.

Theorem mult_n_O (ds_d3hM : MyNat): mult_n_O_spec ds_d3hM.
Proof.
  destruct ds_d3hM as [ds_d3hM ds_d3hM_p].
  induction ds_d3hM as [| n' IH_n'].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (mult_res : MyNat_u), mult_rel O_u O_u mult_res ∧ O_u == mult_res)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (mult_res : MyNat_u), mult_rel (S_u n') O_u mult_res ∧ O_u == mult_res)
            (IH_n' ltac:(try clear IH_n'; solver))
            ltac:(solver)).
Qed.

Definition mult_n_0_m_0_spec (p q : MyNat): Type :=
  {{∃ (mult_res : MyNat_u),
    mult_rel ⌊ q ⌋ O_u mult_res
    ∧ ∃ (mult_res_2 : MyNat_u),
      mult_rel ⌊ p ⌋ O_u mult_res_2
      ∧ ∃ (plus_res : MyNat_u), plus_rel mult_res_2 mult_res plus_res ∧ plus_res == O_u}}.

#[global] Hint Unfold mult_n_0_m_0_spec: lia_unfold.

Theorem mult_n_0_m_0 (p q : MyNat): mult_n_0_m_0_spec p q.
Proof.
  destruct p as [p p_p].
  destruct q as [q q_p].
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (mult_res : MyNat_u),
           mult_rel q O_u mult_res
           ∧ ∃ (mult_res_2 : MyNat_u),
             mult_rel p O_u mult_res_2
             ∧ ∃ (plus_res : MyNat_u), plus_rel mult_res_2 mult_res plus_res ∧ plus_res == O_u)
          (let _: ∃ (mult_res : MyNat_u), mult_rel q O_u mult_res ∧ O_u == mult_res :=
           ⌈ mult_n_O (exist (λ (q : MyNat_u), MyNat_wf q ∧ True) q ltac:(solver)) ⌉ in
           mult_n_O (exist (λ (p : MyNat_u), MyNat_wf p ∧ True) p ltac:(solver)))
          ltac:(solver)).
Qed.

Definition mult_n_Sm_spec (ds_d3ii ds_d3ij : MyNat): Type :=
  {{∃ (mult_res : MyNat_u),
    mult_rel ⌊ ds_d3ii ⌋ ⌊ ds_d3ij ⌋ mult_res
    ∧ ∃ (plus_res : MyNat_u),
      plus_rel mult_res ⌊ ds_d3ii ⌋ plus_res
      ∧ ∃ (mult_res_2 : MyNat_u),
        mult_rel ⌊ ds_d3ii ⌋ (S_u ⌊ ds_d3ij ⌋) mult_res_2 ∧ plus_res == mult_res_2}}.

#[global] Hint Unfold mult_n_Sm_spec: lia_unfold.

Theorem mult_n_Sm (ds_d3ii ds_d3ij : MyNat): mult_n_Sm_spec ds_d3ii ds_d3ij.
Proof.
  destruct ds_d3ii as [ds_d3ii ds_d3ii_p].
  destruct ds_d3ij as [ds_d3ij ds_d3ij_p].
  destruct ds_d3ii as [| n'].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (mult_res : MyNat_u),
             mult_rel O_u ds_d3ij mult_res
             ∧ ∃ (plus_res : MyNat_u),
               plus_rel mult_res O_u plus_res
               ∧ ∃ (mult_res_2 : MyNat_u), mult_rel O_u (S_u ds_d3ij) mult_res_2 ∧ plus_res == mult_res_2)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (mult_res : MyNat_u),
             mult_rel (S_u n') ds_d3ij mult_res
             ∧ ∃ (plus_res : MyNat_u),
               plus_rel mult_res (S_u n') plus_res
               ∧ ∃ (mult_res_2 : MyNat_u), mult_rel (S_u n') (S_u ds_d3ij) mult_res_2 ∧ plus_res == mult_res_2)
            (let _: ∃ (plus_res : MyNat_u),
                    plus_rel
                    ⌊ plus
                      (exist (λ (ds_d3ij : MyNat_u), MyNat_wf ds_d3ij ∧ True) ds_d3ij ltac:(solver))
                      (mult
                       (exist (λ (VV : MyNat_u), MyNat_wf VV ∧ True) n' ltac:(solver))
                       (exist (λ (ds_d3ij : MyNat_u), MyNat_wf ds_d3ij ∧ True) ds_d3ij ltac:(solver))) ⌋
                    (S_u n')
                    plus_res
                    ∧ ∃ (plus_res_2 : MyNat_u),
                      plus_rel
                      ⌊ plus
                        (exist (λ (ds_d3ij : MyNat_u), MyNat_wf ds_d3ij ∧ True) ds_d3ij ltac:(solver))
                        (mult
                         (exist (λ (VV : MyNat_u), MyNat_wf VV ∧ True) n' ltac:(solver))
                         (exist (λ (ds_d3ij : MyNat_u), MyNat_wf ds_d3ij ∧ True) ds_d3ij ltac:(solver))) ⌋
                      n'
                      plus_res_2
                      ∧ plus_res == S_u plus_res_2 :=
             ⌈ add_succ_r
               (plus
                (exist (λ (ds_d3ij : MyNat_u), MyNat_wf ds_d3ij ∧ True) ds_d3ij ltac:(solver))
                (mult
                 (exist (λ (VV : MyNat_u), MyNat_wf VV ∧ True) n' ltac:(solver))
                 (exist (λ (ds_d3ij : MyNat_u), MyNat_wf ds_d3ij ∧ True) ds_d3ij ltac:(solver))))
               (exist (λ (VV : MyNat_u), MyNat_wf VV ∧ True) n' ltac:(solver)) ⌉ in
             add_assoc
             (exist (λ (ds_d3ij : MyNat_u), MyNat_wf ds_d3ij ∧ True) ds_d3ij ltac:(solver))
             (mult
              (exist (λ (VV : MyNat_u), MyNat_wf VV ∧ True) n' ltac:(solver))
              (exist (λ (ds_d3ij : MyNat_u), MyNat_wf ds_d3ij ∧ True) ds_d3ij ltac:(solver)))
             (exist (λ (VV : MyNat_u), MyNat_wf VV ∧ True) n' ltac:(solver)))
            ltac:(solver)).
Qed.

Definition mult_n_1_spec (p : MyNat): Type :=
  {{∃ (mult_res : MyNat_u), mult_rel ⌊ p ⌋ ⌊ one -⌋ mult_res ∧ mult_res == ⌊ p ⌋}}.

#[global] Hint Unfold mult_n_1_spec: lia_unfold.

Theorem mult_n_1 (p : MyNat): mult_n_1_spec p.
Proof.
  destruct p as [p p_p].
  refine (subsumptionCast
          Unit
          (λ (VV : Unit), ∃ (mult_res : MyNat_u), mult_rel p ⌊ one -⌋ mult_res ∧ mult_res == p)
          (let _: ∃ (mult_res : MyNat_u), mult_rel p O_u mult_res ∧ O_u == mult_res :=
           ⌈ mult_n_O (exist (λ (p : MyNat_u), MyNat_wf p ∧ True) p ltac:(solver)) ⌉ in
           mult_n_Sm (exist (λ (p : MyNat_u), MyNat_wf p ∧ True) p ltac:(solver)) O)
          ltac:(solver)).
Qed.

Definition plus_1_1_spec (n : MyNat): Type :=
  {{∃ (plus_res : MyNat_u), plus_rel ⌊ one -⌋ ⌊ n ⌋ plus_res ∧ plus_res == S_u ⌊ n ⌋}}.

#[global] Hint Unfold plus_1_1_spec: lia_unfold.

Theorem plus_1_1 (n : MyNat): plus_1_1_spec n.
Proof.
  destruct n as [n n_p].
  refine (subsumptionCast
          Unit
          (λ (VV : Unit), ∃ (plus_res : MyNat_u), plus_rel ⌊ one -⌋ n plus_res ∧ plus_res == S_u n)
          (# unit)
          ltac:(solver)).
Qed.

Definition plus_1_neq_0_spec (ds_d3hF : MyNat): Type :=
  {{∃ (plus_res : MyNat_u), plus_rel ⌊ ds_d3hF ⌋ ⌊ one -⌋ plus_res ∧ plus_res ≠ O_u}}.

#[global] Hint Unfold plus_1_neq_0_spec: lia_unfold.

Theorem plus_1_neq_0 (ds_d3hF : MyNat): plus_1_neq_0_spec ds_d3hF.
Proof.
  destruct ds_d3hF as [ds_d3hF ds_d3hF_p].
  destruct ds_d3hF as [| ds_d3hG].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (plus_res : MyNat_u), plus_rel O_u ⌊ one -⌋ plus_res ∧ plus_res ≠ O_u)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (plus_res : MyNat_u), plus_rel (S_u ds_d3hG) ⌊ one -⌋ plus_res ∧ plus_res ≠ O_u)
            (# unit)
            ltac:(solver)).
Qed.

Definition plus_O_n_spec (n : MyNat): Type :=
  {{∃ (plus_res : MyNat_u), plus_rel O_u ⌊ n ⌋ plus_res ∧ plus_res == ⌊ n ⌋}}.

#[global] Hint Unfold plus_O_n_spec: lia_unfold.

Theorem plus_O_n (n : MyNat): plus_O_n_spec n.
Proof.
  destruct n as [n n_p].
  refine (subsumptionCast
          Unit
          (λ (VV : Unit), ∃ (plus_res : MyNat_u), plus_rel O_u n plus_res ∧ plus_res == n)
          (# unit)
          ltac:(solver)).
Qed.

Definition plus_id_example_spec (n m : MyNat) (z : {{⌊ n ⌋ == ⌊ m ⌋}}): Type :=
  {{∃ (plus_res : MyNat_u),
    plus_rel ⌊ n ⌋ ⌊ n ⌋ plus_res
    ∧ ∃ (plus_res_2 : MyNat_u), plus_rel ⌊ m ⌋ ⌊ m ⌋ plus_res_2 ∧ plus_res == plus_res_2}}.

#[global] Hint Unfold plus_id_example_spec: lia_unfold.

Theorem plus_id_example (n m : MyNat) (z : {{⌊ n ⌋ == ⌊ m ⌋}}): plus_id_example_spec n m z.
Proof.
  destruct n as [n n_p].
  destruct m as [m m_p].
  destruct z as [z z_p].
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (plus_res : MyNat_u),
           plus_rel n n plus_res ∧ ∃ (plus_res_2 : MyNat_u), plus_rel m m plus_res_2 ∧ plus_res == plus_res_2)
          (# unit)
          ltac:(solver)).
Qed.

Definition plus_id_exercise_spec (n m o : MyNat) (p : {{⌊ n ⌋ == ⌊ m ⌋}}) (q : {{⌊ m ⌋ == ⌊ o ⌋}}):
  Type :=
  {{∃ (plus_res : MyNat_u),
    plus_rel ⌊ n ⌋ ⌊ m ⌋ plus_res
    ∧ ∃ (plus_res_2 : MyNat_u), plus_rel ⌊ m ⌋ ⌊ o ⌋ plus_res_2 ∧ plus_res == plus_res_2}}.

#[global] Hint Unfold plus_id_exercise_spec: lia_unfold.

Theorem plus_id_exercise (n m o : MyNat) (p : {{⌊ n ⌋ == ⌊ m ⌋}}) (q : {{⌊ m ⌋ == ⌊ o ⌋}}):
  plus_id_exercise_spec n m o p q.
Proof.
  destruct n as [n n_p].
  destruct m as [m m_p].
  destruct o as [o o_p].
  destruct p as [p p_p].
  destruct q as [q q_p].
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (plus_res : MyNat_u),
           plus_rel n m plus_res ∧ ∃ (plus_res_2 : MyNat_u), plus_rel m o plus_res_2 ∧ plus_res == plus_res_2)
          (# unit)
          ltac:(solver)).
Qed.

Definition plus_n_Sm_spec (ds_d3gD m : MyNat): Type :=
  {{∃ (plus_res : MyNat_u),
    plus_rel ⌊ ds_d3gD ⌋ ⌊ m ⌋ plus_res
    ∧ ∃ (plus_res_2 : MyNat_u),
      plus_rel ⌊ ds_d3gD ⌋ (S_u ⌊ m ⌋) plus_res_2 ∧ S_u plus_res == plus_res_2}}.

#[global] Hint Unfold plus_n_Sm_spec: lia_unfold.

Theorem plus_n_Sm (ds_d3gD m : MyNat): plus_n_Sm_spec ds_d3gD m.
Proof.
  destruct ds_d3gD as [ds_d3gD ds_d3gD_p].
  destruct m as [m m_p].
  try revert m_p; generalize dependent m; induction ds_d3gD as [| n' IH_n']; intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (plus_res : MyNat_u),
             plus_rel O_u m plus_res
             ∧ ∃ (plus_res_2 : MyNat_u), plus_rel O_u (S_u m) plus_res_2 ∧ S_u plus_res == plus_res_2)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (plus_res : MyNat_u),
             plus_rel (S_u n') m plus_res
             ∧ ∃ (plus_res_2 : MyNat_u), plus_rel (S_u n') (S_u m) plus_res_2 ∧ S_u plus_res == plus_res_2)
            (IH_n' ltac:(try clear IH_n'; solver) m ltac:(try clear IH_n'; solver))
            ltac:(solver)).
Qed.

Definition add_comm_spec (ds_d3gH m : MyNat): Type :=
  {{∃ (plus_res : MyNat_u),
    plus_rel ⌊ ds_d3gH ⌋ ⌊ m ⌋ plus_res
    ∧ ∃ (plus_res_2 : MyNat_u), plus_rel ⌊ m ⌋ ⌊ ds_d3gH ⌋ plus_res_2 ∧ plus_res == plus_res_2}}.

#[global] Hint Unfold add_comm_spec: lia_unfold.

Theorem add_comm (ds_d3gH m : MyNat): add_comm_spec ds_d3gH m.
Proof.
  destruct ds_d3gH as [ds_d3gH ds_d3gH_p].
  destruct m as [m m_p].
  try revert m_p; generalize dependent m; induction ds_d3gH as [| n' IH_n']; intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (plus_res : MyNat_u),
             plus_rel O_u m plus_res
             ∧ ∃ (plus_res_2 : MyNat_u), plus_rel m O_u plus_res_2 ∧ plus_res == plus_res_2)
            (add_0_r (exist (λ (m : MyNat_u), MyNat_wf m ∧ True) m ltac:(solver)))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (plus_res : MyNat_u),
             plus_rel (S_u n') m plus_res
             ∧ ∃ (plus_res_2 : MyNat_u), plus_rel m (S_u n') plus_res_2 ∧ plus_res == plus_res_2)
            (let _: ∃ (plus_res : MyNat_u),
                    plus_rel n' m plus_res
                    ∧ ∃ (plus_res_2 : MyNat_u), plus_rel m n' plus_res_2 ∧ plus_res == plus_res_2 :=
             ⌈ IH_n' ltac:(try clear IH_n'; solver) m ltac:(try clear IH_n'; solver) ⌉ in
             plus_n_Sm
             (exist (λ (m : MyNat_u), MyNat_wf m ∧ True) m ltac:(solver))
             (exist (λ (VV : MyNat_u), MyNat_wf VV ∧ True) n' ltac:(solver)))
            ltac:(solver)).
Qed.

Definition pred_spec (ds_d3im : MyNat): Type :=
  MyNat.

#[global] Hint Unfold pred_spec: lia_unfold.

Definition pred (ds_d3im : MyNat): pred_spec ds_d3im.
Proof.
  destruct ds_d3im as [ds_d3im ds_d3im_p].
  destruct ds_d3im as [| n'].
  - refine O.
  - refine (exist (λ (VV : MyNat_u), MyNat_wf VV ∧ True) n' ltac:(solver)).
Defined.

Inductive pred_rel: MyNat_u → MyNat_u → Prop :=
  | pred_O: pred_rel O_u O_u | pred_S: ∀ n', pred_rel (S_u n') n'.

#[global] Hint Constructors pred_rel: core_hint_db.

#[global] Instance pred_lookup_rel: dictionary rel pred := { lookup' := pred_rel }.

#[global] Instance pred_getF: getFunc pred_rel := { getF' := pred }.

Theorem pred_rel_funct [ds_d3im : MyNat_u]:
  ∀ (VV VV' : MyNat_u), pred_rel ds_d3im VV → (pred_rel ds_d3im VV' → VV = VV').
Proof.
  destruct ds_d3im as [| n']; rel_functionhood_body.
Qed.

#[global] Hint Resolve pred_rel_funct: f_rel_funct_db.

Theorem pred_O_lem pred_O_lem_res: pred_rel O_u pred_O_lem_res ↔ pred_O_lem_res == O_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite pred_O_lem: f_rel_back.

Theorem pred_S_lem n' pred_S_lem_res: pred_rel (S_u n') pred_S_lem_res ↔ pred_S_lem_res == n'.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite pred_S_lem: f_rel_back.

Theorem pred_rel_ex (ds_d3im : MyNat_u) (ds_d3im_p : MyNat_wf ds_d3im ∧ True):
  pred_rel ds_d3im ⌊ pred (exist _ ds_d3im ds_d3im_p) -⌋.
Proof.
  Opaque pred.
  existence_lemma_pre pred;
  destruct ds_d3im as [| n'];
  [fix_notations | fix_notations];
  simpl in *.
  Transparent pred.
  all: (existence_lemma_quicksolve pred; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve pred_rel_ex: rel_ax_db.

#[global] Opaque pred.

Theorem pred__pred_rel_rw (ds_d3im : MyNat_u) (ds_d3im_p : MyNat_wf ds_d3im ∧ True) (VV : MyNat_u):
  ⌊ pred (exist _ ds_d3im ds_d3im_p) -⌋ = VV ↔ pred_rel ds_d3im VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite pred__pred_rel_rw: f_rel_funct_db.

#[global] Hint Resolve pred__pred_rel_rw: rel_ax_db.

#[global] Instance pred_lookup_rw: dictionary rwLem pred := { lookup' := pred__pred_rel_rw }.

Theorem pred__pred_rel (ds_d3im : MyNat) (VV : MyNat_u):
  ⌊ pred ds_d3im -⌋ = VV ↔ pred_rel ⌊ ds_d3im ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite pred__pred_rel: f_rel_funct_db.

Theorem pred__pred_rel' (ds_d3im_u : MyNat_u) (ds_d3im : MyNat) (VV : MyNat_u):
  ds_d3im_u = ⌊ ds_d3im ⌋ → ⌊ pred ds_d3im -⌋ = VV ↔ pred_rel ds_d3im_u VV.
Proof.
  intros ->. refine (pred__pred_rel ds_d3im VV).
Qed.

#[global] Hint Resolve pred__pred_rel': f_rel_funct_db.

Theorem pred_rel_mk (ds_d3im : MyNat_u) (ds_d3im_p : MyNat_wf ds_d3im ∧ True):
  {VV: _ | pred_rel ds_d3im VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, pred_rel ds_d3im VV) (pred (exist _ ds_d3im ds_d3im_p)) _);
  rewrite <- pred__pred_rel';
  quicksolve.
Qed.

#[global] Hint Resolve pred_rel_mk: f_rel_funct_db.

#[global] Instance pred_pack:
  @Pack
  (MyNat ::RT λ (ds_d3im : MyNat), nilRT)
  (MyNat_u ::UT nilUT)
  ltac:(mkProjectsArgListTG ((MyNat ::RT λ (ds_d3im : MyNat), nilRT)) ((MyNat_u ::UT nilUT)))
  MyNat_u
  (λ (x_48722725 : ArgList (MyNat ::RT λ (ds_d3im : MyNat), nilRT)) (v_x_48722725 : MyNat_u),
   ltac:(flattenP (λ (ds_d3im : MyNat) (VV : MyNat_u), MyNat_wf VV ∧ True) x_48722725 v_x_48722725)).
Proof.
  buildPackG pred pred_rel pred__pred_rel pred_rel_funct.
Defined.

#[global] Instance pred_upack: @uPack (MyNat_u ::UT nilUT) MyNat_u.
Proof.
  buildUPackG pred_rel pred_rel_funct.
Defined.

Definition sf_exp_spec (ds_d3ic ds_d3id : MyNat): Type :=
  MyNat.

#[global] Hint Unfold sf_exp_spec: lia_unfold.

Definition sf_exp (ds_d3ic ds_d3id : MyNat): sf_exp_spec ds_d3ic ds_d3id.
Proof.
  destruct ds_d3ic as [ds_d3ic ds_d3ic_p].
  destruct ds_d3id as [ds_d3id ds_d3id_p].
  try revert ds_d3ic_p; generalize dependent ds_d3ic; induction ds_d3id as [| p IH_p]; intros.
  - refine (S O).
  - refine (mult
            (exist (λ (ds_d3ic : MyNat_u), MyNat_wf ds_d3ic ∧ True) ds_d3ic ltac:(solver))
            (IH_p ltac:(try clear IH_p; solver) ds_d3ic ltac:(try clear IH_p; solver))).
Defined.

Inductive sf_exp_rel: MyNat_u → MyNat_u → MyNat_u → Prop :=
  | sf_exp_x_O: ∀ ds_d3ic, sf_exp_rel ds_d3ic O_u (S_u O_u)
  | sf_exp_x_S: ∀ ds_d3ic p (sf_exp_res : MyNat_u),
                sf_exp_rel ds_d3ic p sf_exp_res
                → ∀ (mult_res : MyNat_u),
                  mult_rel ds_d3ic sf_exp_res mult_res → sf_exp_rel ds_d3ic (S_u p) mult_res.

#[global] Hint Constructors sf_exp_rel: core_hint_db.

#[global] Instance sf_exp_lookup_rel: dictionary rel sf_exp := { lookup' := sf_exp_rel }.

#[global] Instance sf_exp_getF: getFunc sf_exp_rel := { getF' := sf_exp }.

Theorem sf_exp_rel_funct [ds_d3ic ds_d3id : MyNat_u]:
  ∀ (VV VV' : MyNat_u), sf_exp_rel ds_d3ic ds_d3id VV → (sf_exp_rel ds_d3ic ds_d3id VV' → VV = VV').
Proof.
  try revert ds_d3ic_p; generalize dependent ds_d3ic; induction ds_d3id as [| p IH_p]; intros;
  rel_functionhood_body.
Qed.

#[global] Hint Resolve sf_exp_rel_funct: f_rel_funct_db.

Theorem sf_exp_x_O_lem ds_d3ic sf_exp_x_O_lem_res:
  sf_exp_rel ds_d3ic O_u sf_exp_x_O_lem_res ↔ sf_exp_x_O_lem_res == S_u O_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite sf_exp_x_O_lem: f_rel_back.

Theorem sf_exp_x_S_lem ds_d3ic p sf_exp_x_S_lem_res:
  sf_exp_rel ds_d3ic (S_u p) sf_exp_x_S_lem_res
  ↔ ∃ (sf_exp_res : MyNat_u),
    sf_exp_rel ds_d3ic p sf_exp_res
    ∧ ∃ (mult_res : MyNat_u), mult_rel ds_d3ic sf_exp_res mult_res ∧ sf_exp_x_S_lem_res == mult_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite sf_exp_x_S_lem: f_rel_back.

Theorem sf_exp_rel_ex
  (ds_d3ic : MyNat_u)
  (ds_d3ic_p : MyNat_wf ds_d3ic ∧ True)
  (ds_d3id : MyNat_u)
  (ds_d3id_p : MyNat_wf ds_d3id ∧ True):
  sf_exp_rel ds_d3ic ds_d3id ⌊ sf_exp (exist _ ds_d3ic ds_d3ic_p) (exist _ ds_d3id ds_d3id_p) -⌋.
Proof.
  Opaque sf_exp.
  existence_lemma_pre sf_exp;
  try revert ds_d3ic_p; generalize dependent ds_d3ic; induction ds_d3id as [| p IH_p]; intros;
  [fix_notations |
   fix_notations;
   pose proof (IH_p
               ltac:(try clear IH_p; solver)
               ds_d3ic
               ltac:(try clear IH_p; solver)) as IH_24832044;
   try clear IH_p];
  simpl in *.
  Transparent sf_exp.
  all: (existence_lemma_quicksolve sf_exp; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve sf_exp_rel_ex: rel_ax_db.

#[global] Opaque sf_exp.

Theorem sf_exp__sf_exp_rel_rw
  (ds_d3ic : MyNat_u)
  (ds_d3ic_p : MyNat_wf ds_d3ic ∧ True)
  (ds_d3id : MyNat_u)
  (ds_d3id_p : MyNat_wf ds_d3id ∧ True)
  (VV : MyNat_u):
  ⌊ sf_exp (exist _ ds_d3ic ds_d3ic_p) (exist _ ds_d3id ds_d3id_p) -⌋ = VV
  ↔ sf_exp_rel ds_d3ic ds_d3id VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite sf_exp__sf_exp_rel_rw: f_rel_funct_db.

#[global] Hint Resolve sf_exp__sf_exp_rel_rw: rel_ax_db.

#[global] Instance sf_exp_lookup_rw: dictionary rwLem sf_exp := {
    lookup' := sf_exp__sf_exp_rel_rw }.

Theorem sf_exp__sf_exp_rel (ds_d3ic ds_d3id : MyNat) (VV : MyNat_u):
  ⌊ sf_exp ds_d3ic ds_d3id -⌋ = VV ↔ sf_exp_rel ⌊ ds_d3ic ⌋ ⌊ ds_d3id ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite sf_exp__sf_exp_rel: f_rel_funct_db.

Theorem sf_exp__sf_exp_rel'
  (ds_d3ic_u ds_d3id_u : MyNat_u) (ds_d3ic ds_d3id : MyNat) (VV : MyNat_u):
  ds_d3ic_u = ⌊ ds_d3ic ⌋
  → (ds_d3id_u = ⌊ ds_d3id ⌋ → ⌊ sf_exp ds_d3ic ds_d3id -⌋ = VV ↔ sf_exp_rel ds_d3ic_u ds_d3id_u VV).
Proof.
  intros -> ->. refine (sf_exp__sf_exp_rel ds_d3ic ds_d3id VV).
Qed.

#[global] Hint Resolve sf_exp__sf_exp_rel': f_rel_funct_db.

Theorem sf_exp_rel_mk
  (ds_d3ic : MyNat_u)
  (ds_d3ic_p : MyNat_wf ds_d3ic ∧ True)
  (ds_d3id : MyNat_u)
  (ds_d3id_p : MyNat_wf ds_d3id ∧ True):
  {VV: _ | sf_exp_rel ds_d3ic ds_d3id VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, sf_exp_rel ds_d3ic ds_d3id VV)
          (sf_exp (exist _ ds_d3ic ds_d3ic_p) (exist _ ds_d3id ds_d3id_p))
          _);
  rewrite <- sf_exp__sf_exp_rel';
  quicksolve.
Qed.

#[global] Hint Resolve sf_exp_rel_mk: f_rel_funct_db.

#[global] Instance sf_exp_pack:
  @Pack
  (MyNat ::RT λ (ds_d3ic : MyNat), MyNat ::RT λ (ds_d3id : MyNat), nilRT)
  (MyNat_u ::UT (MyNat_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((MyNat
  ::RT λ (ds_d3ic : MyNat), MyNat ::RT λ (ds_d3id : MyNat), nilRT)) ((MyNat_u ::UT (MyNat_u ::UT nilUT))))
  MyNat_u
  (λ (x_63489635 : ArgList (MyNat ::RT λ (ds_d3ic : MyNat), MyNat ::RT λ (ds_d3id : MyNat), nilRT))
     (v_x_63489635 : MyNat_u),
   ltac:(flattenP (λ (ds_d3ic ds_d3id : MyNat) (VV : MyNat_u), MyNat_wf VV ∧ True) x_63489635 v_x_63489635)).
Proof.
  buildPackG sf_exp sf_exp_rel sf_exp__sf_exp_rel sf_exp_rel_funct.
Defined.

#[global] Instance sf_exp_upack: @uPack (MyNat_u ::UT (MyNat_u ::UT nilUT)) MyNat_u.
Proof.
  buildUPackG sf_exp_rel sf_exp_rel_funct.
Defined.

Definition sndSF_spec (ds_d3gB : Natprod): Type :=
  MyNat.

#[global] Hint Unfold sndSF_spec: lia_unfold.

Definition sndSF (ds_d3gB : Natprod): sndSF_spec ds_d3gB.
Proof.
  destruct ds_d3gB as [ds_d3gB ds_d3gB_p].
  destruct ds_d3gB as [n1 n2].
  - refine (exist (λ (n2 : MyNat_u), MyNat_wf n2 ∧ True) n2 ltac:(solver)).
Defined.

Inductive sndSF_rel: Natprod_u → MyNat_u → Prop :=
  | sndSF_Pair: ∀ n1 n2, sndSF_rel (Pair_u n1 n2) n2.

#[global] Hint Constructors sndSF_rel: core_hint_db.

#[global] Instance sndSF_lookup_rel: dictionary rel sndSF := { lookup' := sndSF_rel }.

#[global] Instance sndSF_getF: getFunc sndSF_rel := { getF' := sndSF }.

Theorem sndSF_rel_funct [ds_d3gB : Natprod_u]:
  ∀ (VV VV' : MyNat_u), sndSF_rel ds_d3gB VV → (sndSF_rel ds_d3gB VV' → VV = VV').
Proof.
  destruct ds_d3gB as [n1 n2]; rel_functionhood_body.
Qed.

#[global] Hint Resolve sndSF_rel_funct: f_rel_funct_db.

Theorem sndSF_Pair_lem n1 n2 sndSF_Pair_lem_res:
  sndSF_rel (Pair_u n1 n2) sndSF_Pair_lem_res ↔ sndSF_Pair_lem_res == n2.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite sndSF_Pair_lem: f_rel_back.

Theorem sndSF_rel_ex (ds_d3gB : Natprod_u) (ds_d3gB_p : Natprod_wf ds_d3gB ∧ True):
  sndSF_rel ds_d3gB ⌊ sndSF (exist _ ds_d3gB ds_d3gB_p) -⌋.
Proof.
  Opaque sndSF.
  existence_lemma_pre sndSF;
  destruct ds_d3gB as [n1 n2];
  [fix_notations];
  simpl in *.
  Transparent sndSF.
  all: (existence_lemma_quicksolve sndSF; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve sndSF_rel_ex: rel_ax_db.

#[global] Opaque sndSF.

Theorem sndSF__sndSF_rel_rw
  (ds_d3gB : Natprod_u) (ds_d3gB_p : Natprod_wf ds_d3gB ∧ True) (VV : MyNat_u):
  ⌊ sndSF (exist _ ds_d3gB ds_d3gB_p) -⌋ = VV ↔ sndSF_rel ds_d3gB VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite sndSF__sndSF_rel_rw: f_rel_funct_db.

#[global] Hint Resolve sndSF__sndSF_rel_rw: rel_ax_db.

#[global] Instance sndSF_lookup_rw: dictionary rwLem sndSF := { lookup' := sndSF__sndSF_rel_rw }.

Theorem sndSF__sndSF_rel (ds_d3gB : Natprod) (VV : MyNat_u):
  ⌊ sndSF ds_d3gB -⌋ = VV ↔ sndSF_rel ⌊ ds_d3gB ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite sndSF__sndSF_rel: f_rel_funct_db.

Theorem sndSF__sndSF_rel' (ds_d3gB_u : Natprod_u) (ds_d3gB : Natprod) (VV : MyNat_u):
  ds_d3gB_u = ⌊ ds_d3gB ⌋ → ⌊ sndSF ds_d3gB -⌋ = VV ↔ sndSF_rel ds_d3gB_u VV.
Proof.
  intros ->. refine (sndSF__sndSF_rel ds_d3gB VV).
Qed.

#[global] Hint Resolve sndSF__sndSF_rel': f_rel_funct_db.

Theorem sndSF_rel_mk (ds_d3gB : Natprod_u) (ds_d3gB_p : Natprod_wf ds_d3gB ∧ True):
  {VV: _ | sndSF_rel ds_d3gB VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, sndSF_rel ds_d3gB VV) (sndSF (exist _ ds_d3gB ds_d3gB_p)) _);
  rewrite <- sndSF__sndSF_rel';
  quicksolve.
Qed.

#[global] Hint Resolve sndSF_rel_mk: f_rel_funct_db.

#[global] Instance sndSF_pack:
  @Pack
  (Natprod ::RT λ (ds_d3gB : Natprod), nilRT)
  (Natprod_u ::UT nilUT)
  ltac:(mkProjectsArgListTG ((Natprod ::RT λ (ds_d3gB : Natprod), nilRT)) ((Natprod_u ::UT nilUT)))
  MyNat_u
  (λ (x_62410082 : ArgList (Natprod ::RT λ (ds_d3gB : Natprod), nilRT)) (v_x_62410082 : MyNat_u),
   ltac:(flattenP (λ (ds_d3gB : Natprod) (VV : MyNat_u), MyNat_wf VV ∧ True) x_62410082 v_x_62410082)).
Proof.
  buildPackG sndSF sndSF_rel sndSF__sndSF_rel sndSF_rel_funct.
Defined.

#[global] Instance sndSF_upack: @uPack (Natprod_u ::UT nilUT) MyNat_u.
Proof.
  buildUPackG sndSF_rel sndSF_rel_funct.
Defined.

Definition surjective_pairing_spec (ds_d3gx : Natprod): Type :=
  {{∃ (sndSF_res : MyNat_u),
    sndSF_rel ⌊ ds_d3gx ⌋ sndSF_res
    ∧ ∃ (fstSF_res : MyNat_u),
      fstSF_rel ⌊ ds_d3gx ⌋ fstSF_res ∧ ⌊ ds_d3gx ⌋ == Pair_u fstSF_res sndSF_res}}.

#[global] Hint Unfold surjective_pairing_spec: lia_unfold.

Theorem surjective_pairing (ds_d3gx : Natprod): surjective_pairing_spec ds_d3gx.
Proof.
  destruct ds_d3gx as [ds_d3gx ds_d3gx_p].
  destruct ds_d3gx as [n m].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (sndSF_res : MyNat_u),
             sndSF_rel (Pair_u n m) sndSF_res
             ∧ ∃ (fstSF_res : MyNat_u),
               fstSF_rel (Pair_u n m) fstSF_res ∧ Pair_u n m == Pair_u fstSF_res sndSF_res)
            (# unit)
            ltac:(solver)).
Qed.

Definition surjective_pairing'_spec (n m : MyNat): Type :=
  {{∃ (sndSF_res : MyNat_u),
    sndSF_rel (Pair_u ⌊ n ⌋ ⌊ m ⌋) sndSF_res
    ∧ ∃ (fstSF_res : MyNat_u),
      fstSF_rel (Pair_u ⌊ n ⌋ ⌊ m ⌋) fstSF_res ∧ Pair_u ⌊ n ⌋ ⌊ m ⌋ == Pair_u fstSF_res sndSF_res}}.

#[global] Hint Unfold surjective_pairing'_spec: lia_unfold.

Theorem surjective_pairing' (n m : MyNat): surjective_pairing'_spec n m.
Proof.
  destruct n as [n n_p].
  destruct m as [m m_p].
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (sndSF_res : MyNat_u),
           sndSF_rel (Pair_u n m) sndSF_res
           ∧ ∃ (fstSF_res : MyNat_u),
             fstSF_rel (Pair_u n m) fstSF_res ∧ Pair_u n m == Pair_u fstSF_res sndSF_res)
          (# unit)
          ltac:(solver)).
Qed.

Definition two_spec : Type :=
  MyNat.

#[global] Hint Unfold two_spec: lia_unfold.

Definition two : two_spec.
Proof.
  refine (S one).
Defined.

Definition test_leb1_spec : Type :=
  {{∃ (leb_res : SFBool_u), leb_rel ⌊ two -⌋ ⌊ two -⌋ leb_res ∧ leb_res == SFTrue_u}}.

#[global] Hint Unfold test_leb1_spec: lia_unfold.

Theorem test_leb1 : test_leb1_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit), ∃ (leb_res : SFBool_u), leb_rel ⌊ two -⌋ ⌊ two -⌋ leb_res ∧ leb_res == SFTrue_u)
          (# unit)
          ltac:(solver)).
Qed.

Definition test_ltb1_spec : Type :=
  {{∃ (ltb_res : SFBool_u), ltb_rel ⌊ two -⌋ ⌊ two -⌋ ltb_res ∧ ltb_res == SFFalse_u}}.

#[global] Hint Unfold test_ltb1_spec: lia_unfold.

Theorem test_ltb1 : test_ltb1_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit), ∃ (ltb_res : SFBool_u), ltb_rel ⌊ two -⌋ ⌊ two -⌋ ltb_res ∧ ltb_res == SFFalse_u)
          (# unit)
          ltac:(solver)).
Qed.

Definition three_spec : Type :=
  MyNat.

#[global] Hint Unfold three_spec: lia_unfold.

Definition three : three_spec.
Proof.
  refine (S two).
Defined.

Definition four_spec : Type :=
  MyNat.

#[global] Hint Unfold four_spec: lia_unfold.

Definition four : four_spec.
Proof.
  refine (S three).
Defined.

Definition five_spec : Type :=
  MyNat.

#[global] Hint Unfold five_spec: lia_unfold.

Definition five : five_spec.
Proof.
  refine (S four).
Defined.

Definition six_spec : Type :=
  MyNat.

#[global] Hint Unfold six_spec: lia_unfold.

Definition six : six_spec.
Proof.
  refine (S five).
Defined.

Definition seven_spec : Type :=
  MyNat.

#[global] Hint Unfold seven_spec: lia_unfold.

Definition seven : seven_spec.
Proof.
  refine (S six).
Defined.

Definition eight_spec : Type :=
  MyNat.

#[global] Hint Unfold eight_spec: lia_unfold.

Definition eight : eight_spec.
Proof.
  refine (S seven).
Defined.

Definition nine_spec : Type :=
  MyNat.

#[global] Hint Unfold nine_spec: lia_unfold.

Definition nine : nine_spec.
Proof.
  refine (S eight).
Defined.

Definition ten_spec : Type :=
  MyNat.

#[global] Hint Unfold ten_spec: lia_unfold.

Definition ten : ten_spec.
Proof.
  refine (S nine).
Defined.

Definition eleven_spec : Type :=
  MyNat.

#[global] Hint Unfold eleven_spec: lia_unfold.

Definition eleven : eleven_spec.
Proof.
  refine (S ten).
Defined.

Definition twelve_spec : Type :=
  MyNat.

#[global] Hint Unfold twelve_spec: lia_unfold.

Definition twelve : twelve_spec.
Proof.
  refine (S eleven).
Defined.

Definition test_leb2_spec : Type :=
  {{∃ (leb_res : SFBool_u), leb_rel ⌊ two -⌋ ⌊ four -⌋ leb_res ∧ leb_res == SFTrue_u}}.

#[global] Hint Unfold test_leb2_spec: lia_unfold.

Theorem test_leb2 : test_leb2_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit), ∃ (leb_res : SFBool_u), leb_rel ⌊ two -⌋ ⌊ four -⌋ leb_res ∧ leb_res == SFTrue_u)
          (# unit)
          ltac:(solver)).
Qed.

Definition test_leb3_spec : Type :=
  {{∃ (leb_res : SFBool_u), leb_rel ⌊ four -⌋ ⌊ two -⌋ leb_res ∧ leb_res == SFFalse_u}}.

#[global] Hint Unfold test_leb3_spec: lia_unfold.

Theorem test_leb3 : test_leb3_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit), ∃ (leb_res : SFBool_u), leb_rel ⌊ four -⌋ ⌊ two -⌋ leb_res ∧ leb_res == SFFalse_u)
          (# unit)
          ltac:(solver)).
Qed.

Definition test_ltb2_spec : Type :=
  {{∃ (ltb_res : SFBool_u), ltb_rel ⌊ two -⌋ ⌊ four -⌋ ltb_res ∧ ltb_res == SFTrue_u}}.

#[global] Hint Unfold test_ltb2_spec: lia_unfold.

Theorem test_ltb2 : test_ltb2_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit), ∃ (ltb_res : SFBool_u), ltb_rel ⌊ two -⌋ ⌊ four -⌋ ltb_res ∧ ltb_res == SFTrue_u)
          (# unit)
          ltac:(solver)).
Qed.

Definition test_ltb3_spec : Type :=
  {{∃ (ltb_res : SFBool_u), ltb_rel ⌊ four -⌋ ⌊ two -⌋ ltb_res ∧ ltb_res == SFFalse_u}}.

#[global] Hint Unfold test_ltb3_spec: lia_unfold.

Theorem test_ltb3 : test_ltb3_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit), ∃ (ltb_res : SFBool_u), ltb_rel ⌊ four -⌋ ⌊ two -⌋ ltb_res ∧ ltb_res == SFFalse_u)
          (# unit)
          ltac:(solver)).
Qed.

Definition test_factorial1_spec : Type :=
  {{∃ (factorial_res : MyNat_u),
    factorial_rel ⌊ three -⌋ factorial_res ∧ factorial_res == ⌊ six -⌋}}.

#[global] Hint Unfold test_factorial1_spec: lia_unfold.

Theorem test_factorial1 : test_factorial1_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (factorial_res : MyNat_u), factorial_rel ⌊ three -⌋ factorial_res ∧ factorial_res == ⌊ six -⌋)
          (# unit)
          ltac:(solver)).
Qed.

Definition test_mult1_spec : Type :=
  {{∃ (mult_res : MyNat_u), mult_rel ⌊ three -⌋ ⌊ three -⌋ mult_res ∧ mult_res == ⌊ nine -⌋}}.

#[global] Hint Unfold test_mult1_spec: lia_unfold.

Theorem test_mult1 : test_mult1_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (mult_res : MyNat_u), mult_rel ⌊ three -⌋ ⌊ three -⌋ mult_res ∧ mult_res == ⌊ nine -⌋)
          (# unit)
          ltac:(solver)).
Qed.

Definition zero_nbeq_plus_1_spec (ds_d3hy : MyNat): Type :=
  {{∃ (plus_res : MyNat_u),
    plus_rel ⌊ ds_d3hy ⌋ ⌊ one -⌋ plus_res
    ∧ ∃ (eqb_res : SFBool_u), eqb_rel O_u plus_res eqb_res ∧ eqb_res == SFFalse_u}}.

#[global] Hint Unfold zero_nbeq_plus_1_spec: lia_unfold.

Theorem zero_nbeq_plus_1 (ds_d3hy : MyNat): zero_nbeq_plus_1_spec ds_d3hy.
Proof.
  destruct ds_d3hy as [ds_d3hy ds_d3hy_p].
  destruct ds_d3hy as [| n'].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (plus_res : MyNat_u),
             plus_rel O_u ⌊ one -⌋ plus_res
             ∧ ∃ (eqb_res : SFBool_u), eqb_rel O_u plus_res eqb_res ∧ eqb_res == SFFalse_u)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (plus_res : MyNat_u),
             plus_rel (S_u n') ⌊ one -⌋ plus_res
             ∧ ∃ (eqb_res : SFBool_u), eqb_rel O_u plus_res eqb_res ∧ eqb_res == SFFalse_u)
            (# unit)
            ltac:(solver)).
Qed.

Inductive Modifier_u: Type :=
  | Minus_u: Modifier_u | Natural_u: Modifier_u | Plus_u: Modifier_u.

Fixpoint Modifier_eq (x y : Modifier_u): bool :=
  match (x, y) with
  | (Minus_u, Minus_u) => true
  | (Natural_u, Natural_u) => true
  | (Plus_u, Plus_u) => true
  | (_, _) => false
  end.

Theorem Modifier_eq_refl : ∀ (x : Modifier_u), is_true (Modifier_eq x x).
Proof.
  eq_refl_rec.
Qed.

#[global] Hint Resolve Modifier_eq_refl: eq_hint_db.

Theorem Modifier_eqb_eq : ∀ (s t : Modifier_u), is_true (Modifier_eq s t) → s = t.
Proof.
  eqb_eq_lem.
Qed.

#[global] Hint Resolve Modifier_eqb_eq: eq_hint_db.

#[global] Instance leibnitz_eq_Modifier: LeibnitzEqB := {
    equalB' := Modifier_eq;
    refl' := Modifier_eq_refl;
    eqb_eq' := Modifier_eqb_eq }.

Fixpoint Modifier_wf (x : Modifier_u): Prop :=
  match x with | Minus_u => True | Natural_u => True | Plus_u => True end.

Theorem Modifier_wf_ref [p : Modifier_u → Prop] (tm : {v: Modifier_u | Modifier_wf v ∧ p v}):
  Modifier_wf ⌊ tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation Modifier := {x: Modifier_u | Modifier_wf x ∧ True}.

Definition Minus_lem : Modifier_wf Minus_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Minus : Modifier :=
  exist _ Minus_u Minus_lem.

Definition Natural_lem : Modifier_wf Natural_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Natural : Modifier :=
  exist _ Natural_u Natural_lem.

Definition Plus_lem : Modifier_wf Plus_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Plus : Modifier :=
  exist _ Plus_u Plus_lem.

#[global] Hint Resolve Modifier_wf_ref: wf_constr_db.

#[global] Hint Unfold Modifier_wf: wf_constr_db.

#[global] Hint Resolve Modifier_eq: ref_constr_db.

#[global] Hint Unfold Minus: ref_constr_db.

#[global] Hint Unfold Natural: ref_constr_db.

#[global] Hint Unfold Plus: ref_constr_db.

Inductive Letter_u: Type :=
  | A_u: Letter_u | B_u: Letter_u | C_u: Letter_u | D_u: Letter_u | F_u: Letter_u.

Fixpoint Letter_eq (x y : Letter_u): bool :=
  match (x, y) with
  | (A_u, A_u) => true
  | (B_u, B_u) => true
  | (C_u, C_u) => true
  | (D_u, D_u) => true
  | (F_u, F_u) => true
  | (_, _) => false
  end.

Theorem Letter_eq_refl : ∀ (x : Letter_u), is_true (Letter_eq x x).
Proof.
  eq_refl_rec.
Qed.

#[global] Hint Resolve Letter_eq_refl: eq_hint_db.

Theorem Letter_eqb_eq : ∀ (s t : Letter_u), is_true (Letter_eq s t) → s = t.
Proof.
  eqb_eq_lem.
Qed.

#[global] Hint Resolve Letter_eqb_eq: eq_hint_db.

#[global] Instance leibnitz_eq_Letter: LeibnitzEqB := {
    equalB' := Letter_eq;
    refl' := Letter_eq_refl;
    eqb_eq' := Letter_eqb_eq }.

Fixpoint Letter_wf (x : Letter_u): Prop :=
  match x with | A_u => True | B_u => True | C_u => True | D_u => True | F_u => True end.

Theorem Letter_wf_ref [p : Letter_u → Prop] (tm : {v: Letter_u | Letter_wf v ∧ p v}):
  Letter_wf ⌊ tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation Letter := {x: Letter_u | Letter_wf x ∧ True}.

Definition A_lem : Letter_wf A_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition A : Letter :=
  exist _ A_u A_lem.

Definition B_lem : Letter_wf B_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition B : Letter :=
  exist _ B_u B_lem.

Definition C_lem : Letter_wf C_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition C : Letter :=
  exist _ C_u C_lem.

Definition D_lem : Letter_wf D_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition D : Letter :=
  exist _ D_u D_lem.

Definition F_lem : Letter_wf F_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition F : Letter :=
  exist _ F_u F_lem.

#[global] Hint Resolve Letter_wf_ref: wf_constr_db.

#[global] Hint Unfold Letter_wf: wf_constr_db.

#[global] Hint Resolve Letter_eq: ref_constr_db.

#[global] Hint Unfold A: ref_constr_db.

#[global] Hint Unfold B: ref_constr_db.

#[global] Hint Unfold C: ref_constr_db.

#[global] Hint Unfold D: ref_constr_db.

#[global] Hint Unfold F: ref_constr_db.

Definition lower_letter_spec (ds_d3gS : Letter): Type :=
  Letter.

#[global] Hint Unfold lower_letter_spec: lia_unfold.

Definition lower_letter (ds_d3gS : Letter): lower_letter_spec ds_d3gS.
Proof.
  destruct ds_d3gS as [ds_d3gS ds_d3gS_p].
  destruct ds_d3gS as [| | | |].
  - refine B.
  - refine C.
  - refine D.
  - refine F.
  - refine F.
Defined.

Inductive lower_letter_rel: Letter_u → Letter_u → Prop :=
  | lower_letter_A: lower_letter_rel A_u B_u
  | lower_letter_B: lower_letter_rel B_u C_u
  | lower_letter_C: lower_letter_rel C_u D_u
  | lower_letter_D: lower_letter_rel D_u F_u
  | lower_letter_F: lower_letter_rel F_u F_u.

#[global] Hint Constructors lower_letter_rel: core_hint_db.

#[global] Instance lower_letter_lookup_rel: dictionary rel lower_letter := {
    lookup' := lower_letter_rel }.

#[global] Instance lower_letter_getF: getFunc lower_letter_rel := { getF' := lower_letter }.

Theorem lower_letter_rel_funct [ds_d3gS : Letter_u]:
  ∀ (VV VV' : Letter_u), lower_letter_rel ds_d3gS VV → (lower_letter_rel ds_d3gS VV' → VV = VV').
Proof.
  destruct ds_d3gS as [| | | |]; rel_functionhood_body.
Qed.

#[global] Hint Resolve lower_letter_rel_funct: f_rel_funct_db.

Theorem lower_letter_A_lem lower_letter_A_lem_res:
  lower_letter_rel A_u lower_letter_A_lem_res ↔ lower_letter_A_lem_res == B_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite lower_letter_A_lem: f_rel_back.

Theorem lower_letter_B_lem lower_letter_B_lem_res:
  lower_letter_rel B_u lower_letter_B_lem_res ↔ lower_letter_B_lem_res == C_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite lower_letter_B_lem: f_rel_back.

Theorem lower_letter_C_lem lower_letter_C_lem_res:
  lower_letter_rel C_u lower_letter_C_lem_res ↔ lower_letter_C_lem_res == D_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite lower_letter_C_lem: f_rel_back.

Theorem lower_letter_D_lem lower_letter_D_lem_res:
  lower_letter_rel D_u lower_letter_D_lem_res ↔ lower_letter_D_lem_res == F_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite lower_letter_D_lem: f_rel_back.

Theorem lower_letter_F_lem lower_letter_F_lem_res:
  lower_letter_rel F_u lower_letter_F_lem_res ↔ lower_letter_F_lem_res == F_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite lower_letter_F_lem: f_rel_back.

Theorem lower_letter_rel_ex (ds_d3gS : Letter_u) (ds_d3gS_p : Letter_wf ds_d3gS ∧ True):
  lower_letter_rel ds_d3gS ⌊ lower_letter (exist _ ds_d3gS ds_d3gS_p) -⌋.
Proof.
  Opaque lower_letter.
  existence_lemma_pre lower_letter;
  destruct ds_d3gS as [| | | |];
  [fix_notations | fix_notations | fix_notations | fix_notations | fix_notations];
  simpl in *.
  Transparent lower_letter.
  all: (existence_lemma_quicksolve lower_letter; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve lower_letter_rel_ex: rel_ax_db.

#[global] Opaque lower_letter.

Theorem lower_letter__lower_letter_rel_rw
  (ds_d3gS : Letter_u) (ds_d3gS_p : Letter_wf ds_d3gS ∧ True) (VV : Letter_u):
  ⌊ lower_letter (exist _ ds_d3gS ds_d3gS_p) -⌋ = VV ↔ lower_letter_rel ds_d3gS VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite lower_letter__lower_letter_rel_rw: f_rel_funct_db.

#[global] Hint Resolve lower_letter__lower_letter_rel_rw: rel_ax_db.

#[global] Instance lower_letter_lookup_rw: dictionary rwLem lower_letter := {
    lookup' := lower_letter__lower_letter_rel_rw }.

Theorem lower_letter__lower_letter_rel (ds_d3gS : Letter) (VV : Letter_u):
  ⌊ lower_letter ds_d3gS -⌋ = VV ↔ lower_letter_rel ⌊ ds_d3gS ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite lower_letter__lower_letter_rel: f_rel_funct_db.

Theorem lower_letter__lower_letter_rel' (ds_d3gS_u : Letter_u) (ds_d3gS : Letter) (VV : Letter_u):
  ds_d3gS_u = ⌊ ds_d3gS ⌋ → ⌊ lower_letter ds_d3gS -⌋ = VV ↔ lower_letter_rel ds_d3gS_u VV.
Proof.
  intros ->. refine (lower_letter__lower_letter_rel ds_d3gS VV).
Qed.

#[global] Hint Resolve lower_letter__lower_letter_rel': f_rel_funct_db.

Theorem lower_letter_rel_mk (ds_d3gS : Letter_u) (ds_d3gS_p : Letter_wf ds_d3gS ∧ True):
  {VV: _ | lower_letter_rel ds_d3gS VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, lower_letter_rel ds_d3gS VV)
          (lower_letter (exist _ ds_d3gS ds_d3gS_p))
          _);
  rewrite <- lower_letter__lower_letter_rel';
  quicksolve.
Qed.

#[global] Hint Resolve lower_letter_rel_mk: f_rel_funct_db.

#[global] Instance lower_letter_pack:
  @Pack
  (Letter ::RT λ (ds_d3gS : Letter), nilRT)
  (Letter_u ::UT nilUT)
  ltac:(mkProjectsArgListTG ((Letter ::RT λ (ds_d3gS : Letter), nilRT)) ((Letter_u ::UT nilUT)))
  Letter_u
  (λ (x_45948707 : ArgList (Letter ::RT λ (ds_d3gS : Letter), nilRT)) (v_x_45948707 : Letter_u),
   ltac:(flattenP (λ (ds_d3gS : Letter) (VV : Letter_u), Letter_wf VV ∧ True) x_45948707 v_x_45948707)).
Proof.
  buildPackG lower_letter lower_letter_rel lower_letter__lower_letter_rel lower_letter_rel_funct.
Defined.

#[global] Instance lower_letter_upack: @uPack (Letter_u ::UT nilUT) Letter_u.
Proof.
  buildUPackG lower_letter_rel lower_letter_rel_funct.
Defined.

Definition lower_letter_F_is_F_spec : Type :=
  {{∃ (lower_letter_res : Letter_u),
    lower_letter_rel F_u lower_letter_res ∧ lower_letter_res == F_u}}.

#[global] Hint Unfold lower_letter_F_is_F_spec: lia_unfold.

Theorem lower_letter_F_is_F : lower_letter_F_is_F_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (lower_letter_res : Letter_u), lower_letter_rel F_u lower_letter_res ∧ lower_letter_res == F_u)
          (# unit)
          ltac:(solver)).
Qed.

Inductive Grades_u: Type :=
  | Grade_u: Letter_u → Modifier_u → Grades_u.

Fixpoint Grades_eq (x y : Grades_u): bool :=
  match (x, y) with
  | (Grade_u VV VV_, Grade_u VV' VV_') => (true && (VV ==? VV')) && (VV_ ==? VV_')
  end.

Theorem Grades_eq_refl : ∀ (x : Grades_u), is_true (Grades_eq x x).
Proof.
  eq_refl_rec.
Qed.

#[global] Hint Resolve Grades_eq_refl: eq_hint_db.

Theorem Grades_eqb_eq : ∀ (s t : Grades_u), is_true (Grades_eq s t) → s = t.
Proof.
  eqb_eq_lem.
Qed.

#[global] Hint Resolve Grades_eqb_eq: eq_hint_db.

#[global] Instance leibnitz_eq_Grades: LeibnitzEqB := {
    equalB' := Grades_eq;
    refl' := Grades_eq_refl;
    eqb_eq' := Grades_eqb_eq }.

Fixpoint Grades_wf (x : Grades_u): Prop :=
  match x with | Grade_u VV VV_ => (Letter_wf VV ∧ True) ∧ (Modifier_wf VV_ ∧ True) end.

Theorem Grades_wf_ref [p : Grades_u → Prop] (tm : {v: Grades_u | Grades_wf v ∧ p v}):
  Grades_wf ⌊ tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation Grades := {x: Grades_u | Grades_wf x ∧ True}.

Definition Grade_lem (VV : Letter) (VV_ : Modifier): Grades_wf (Grade_u ⌊ VV ⌋ ⌊ VV_ ⌋) ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Grade (VV : Letter) (VV_ : Modifier): Grades :=
  exist _ (Grade_u ⌊ VV ⌋ ⌊ VV_ ⌋) (Grade_lem VV VV_).

Definition wf_Grade_VV [VV : Letter_u] [VV_ : Modifier_u] (p : Grades_wf (Grade_u VV VV_)):
  Letter_wf VV.
Proof.
  quicksolve.
Defined.

#[global] Hint Resolve wf_Grade_VV: ref_constr_db.

Definition wf_Grade_VV_ [VV : Letter_u] [VV_ : Modifier_u] (p : Grades_wf (Grade_u VV VV_)):
  Modifier_wf VV_.
Proof.
  quicksolve.
Defined.

#[global] Hint Resolve wf_Grade_VV_: ref_constr_db.

#[global] Hint Resolve Grades_wf_ref: wf_constr_db.

#[global] Hint Unfold Grades_wf: wf_constr_db.

#[global] Hint Resolve Grades_eq: ref_constr_db.

#[global] Hint Unfold Grade: ref_constr_db.

Definition lower_grade_spec (ds_d3gT : Grades): Type :=
  Grades.

#[global] Hint Unfold lower_grade_spec: lia_unfold.

Definition lower_grade (ds_d3gT : Grades): lower_grade_spec ds_d3gT.
Proof.
  destruct ds_d3gT as [ds_d3gT ds_d3gT_p].
  destruct ds_d3gT as [l m].
  - destruct m as [| |].
    + destruct l as [| | | |].
      ** refine (Grade (lower_letter A) Plus).
      ** refine (Grade (lower_letter B) Plus).
      ** refine (Grade (lower_letter C) Plus).
      ** refine (Grade (lower_letter D) Plus).
      ** refine (Grade F Minus).
    + refine (Grade (exist (λ (VV : Letter_u), Letter_wf VV ∧ True) l ltac:(solver)) Minus).
    + refine (Grade (exist (λ (VV : Letter_u), Letter_wf VV ∧ True) l ltac:(solver)) Natural).
Defined.

Inductive lower_grade_rel: Grades_u → Grades_u → Prop :=
  | lower_grade__Grade_A_Minus: ∀ (lower_letter_res : Letter_u),
                                lower_letter_rel A_u lower_letter_res
                                → lower_grade_rel (Grade_u A_u Minus_u) (Grade_u lower_letter_res Plus_u)
  | lower_grade__Grade_B_Minus: ∀ (lower_letter_res : Letter_u),
                                lower_letter_rel B_u lower_letter_res
                                → lower_grade_rel (Grade_u B_u Minus_u) (Grade_u lower_letter_res Plus_u)
  | lower_grade__Grade_C_Minus: ∀ (lower_letter_res : Letter_u),
                                lower_letter_rel C_u lower_letter_res
                                → lower_grade_rel (Grade_u C_u Minus_u) (Grade_u lower_letter_res Plus_u)
  | lower_grade__Grade_D_Minus: ∀ (lower_letter_res : Letter_u),
                                lower_letter_rel D_u lower_letter_res
                                → lower_grade_rel (Grade_u D_u Minus_u) (Grade_u lower_letter_res Plus_u)
  | lower_grade__Grade_F_Minus: lower_grade_rel (Grade_u F_u Minus_u) (Grade_u F_u Minus_u)
  | lower_grade__Grade_x_Natural: ∀ l, lower_grade_rel (Grade_u l Natural_u) (Grade_u l Minus_u)
  | lower_grade__Grade_x_Plus: ∀ l, lower_grade_rel (Grade_u l Plus_u) (Grade_u l Natural_u).

#[global] Hint Constructors lower_grade_rel: core_hint_db.

#[global] Instance lower_grade_lookup_rel: dictionary rel lower_grade := {
    lookup' := lower_grade_rel }.

#[global] Instance lower_grade_getF: getFunc lower_grade_rel := { getF' := lower_grade }.

Theorem lower_grade_rel_funct [ds_d3gT : Grades_u]:
  ∀ (VV VV' : Grades_u), lower_grade_rel ds_d3gT VV → (lower_grade_rel ds_d3gT VV' → VV = VV').
Proof.
  destruct ds_d3gT as [l m];
  [destruct m as [| |];
   [destruct l as [| | | |] |  |]];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve lower_grade_rel_funct: f_rel_funct_db.

Theorem lower_grade__Grade_A_Minus_lem lower_grade__Grade_A_Minus_lem_res:
  lower_grade_rel (Grade_u A_u Minus_u) lower_grade__Grade_A_Minus_lem_res
  ↔ ∃ (lower_letter_res : Letter_u),
    lower_letter_rel A_u lower_letter_res
    ∧ lower_grade__Grade_A_Minus_lem_res == Grade_u lower_letter_res Plus_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite lower_grade__Grade_A_Minus_lem: f_rel_back.

Theorem lower_grade__Grade_B_Minus_lem lower_grade__Grade_B_Minus_lem_res:
  lower_grade_rel (Grade_u B_u Minus_u) lower_grade__Grade_B_Minus_lem_res
  ↔ ∃ (lower_letter_res : Letter_u),
    lower_letter_rel B_u lower_letter_res
    ∧ lower_grade__Grade_B_Minus_lem_res == Grade_u lower_letter_res Plus_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite lower_grade__Grade_B_Minus_lem: f_rel_back.

Theorem lower_grade__Grade_C_Minus_lem lower_grade__Grade_C_Minus_lem_res:
  lower_grade_rel (Grade_u C_u Minus_u) lower_grade__Grade_C_Minus_lem_res
  ↔ ∃ (lower_letter_res : Letter_u),
    lower_letter_rel C_u lower_letter_res
    ∧ lower_grade__Grade_C_Minus_lem_res == Grade_u lower_letter_res Plus_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite lower_grade__Grade_C_Minus_lem: f_rel_back.

Theorem lower_grade__Grade_D_Minus_lem lower_grade__Grade_D_Minus_lem_res:
  lower_grade_rel (Grade_u D_u Minus_u) lower_grade__Grade_D_Minus_lem_res
  ↔ ∃ (lower_letter_res : Letter_u),
    lower_letter_rel D_u lower_letter_res
    ∧ lower_grade__Grade_D_Minus_lem_res == Grade_u lower_letter_res Plus_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite lower_grade__Grade_D_Minus_lem: f_rel_back.

Theorem lower_grade__Grade_F_Minus_lem lower_grade__Grade_F_Minus_lem_res:
  lower_grade_rel (Grade_u F_u Minus_u) lower_grade__Grade_F_Minus_lem_res
  ↔ lower_grade__Grade_F_Minus_lem_res == Grade_u F_u Minus_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite lower_grade__Grade_F_Minus_lem: f_rel_back.

Theorem lower_grade__Grade_x_Natural_lem l lower_grade__Grade_x_Natural_lem_res:
  lower_grade_rel (Grade_u l Natural_u) lower_grade__Grade_x_Natural_lem_res
  ↔ lower_grade__Grade_x_Natural_lem_res == Grade_u l Minus_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite lower_grade__Grade_x_Natural_lem: f_rel_back.

Theorem lower_grade__Grade_x_Plus_lem l lower_grade__Grade_x_Plus_lem_res:
  lower_grade_rel (Grade_u l Plus_u) lower_grade__Grade_x_Plus_lem_res
  ↔ lower_grade__Grade_x_Plus_lem_res == Grade_u l Natural_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite lower_grade__Grade_x_Plus_lem: f_rel_back.

Theorem lower_grade_rel_ex (ds_d3gT : Grades_u) (ds_d3gT_p : Grades_wf ds_d3gT ∧ True):
  lower_grade_rel ds_d3gT ⌊ lower_grade (exist _ ds_d3gT ds_d3gT_p) -⌋.
Proof.
  Opaque lower_grade.
  existence_lemma_pre lower_grade;
  destruct ds_d3gT as [l m];
  [destruct m as [| |];
   [destruct l as [| | | |];
    [fix_notations | fix_notations | fix_notations | fix_notations | fix_notations] |
    fix_notations |
    fix_notations]];
  simpl in *.
  Transparent lower_grade.
  all: (existence_lemma_quicksolve lower_grade; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve lower_grade_rel_ex: rel_ax_db.

#[global] Opaque lower_grade.

Theorem lower_grade__lower_grade_rel_rw
  (ds_d3gT : Grades_u) (ds_d3gT_p : Grades_wf ds_d3gT ∧ True) (VV : Grades_u):
  ⌊ lower_grade (exist _ ds_d3gT ds_d3gT_p) -⌋ = VV ↔ lower_grade_rel ds_d3gT VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite lower_grade__lower_grade_rel_rw: f_rel_funct_db.

#[global] Hint Resolve lower_grade__lower_grade_rel_rw: rel_ax_db.

#[global] Instance lower_grade_lookup_rw: dictionary rwLem lower_grade := {
    lookup' := lower_grade__lower_grade_rel_rw }.

Theorem lower_grade__lower_grade_rel (ds_d3gT : Grades) (VV : Grades_u):
  ⌊ lower_grade ds_d3gT -⌋ = VV ↔ lower_grade_rel ⌊ ds_d3gT ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite lower_grade__lower_grade_rel: f_rel_funct_db.

Theorem lower_grade__lower_grade_rel' (ds_d3gT_u : Grades_u) (ds_d3gT : Grades) (VV : Grades_u):
  ds_d3gT_u = ⌊ ds_d3gT ⌋ → ⌊ lower_grade ds_d3gT -⌋ = VV ↔ lower_grade_rel ds_d3gT_u VV.
Proof.
  intros ->. refine (lower_grade__lower_grade_rel ds_d3gT VV).
Qed.

#[global] Hint Resolve lower_grade__lower_grade_rel': f_rel_funct_db.

Theorem lower_grade_rel_mk (ds_d3gT : Grades_u) (ds_d3gT_p : Grades_wf ds_d3gT ∧ True):
  {VV: _ | lower_grade_rel ds_d3gT VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, lower_grade_rel ds_d3gT VV)
          (lower_grade (exist _ ds_d3gT ds_d3gT_p))
          _);
  rewrite <- lower_grade__lower_grade_rel';
  quicksolve.
Qed.

#[global] Hint Resolve lower_grade_rel_mk: f_rel_funct_db.

#[global] Instance lower_grade_pack:
  @Pack
  (Grades ::RT λ (ds_d3gT : Grades), nilRT)
  (Grades_u ::UT nilUT)
  ltac:(mkProjectsArgListTG ((Grades ::RT λ (ds_d3gT : Grades), nilRT)) ((Grades_u ::UT nilUT)))
  Grades_u
  (λ (x_54723096 : ArgList (Grades ::RT λ (ds_d3gT : Grades), nilRT)) (v_x_54723096 : Grades_u),
   ltac:(flattenP (λ (ds_d3gT : Grades) (VV : Grades_u), Grades_wf VV ∧ True) x_54723096 v_x_54723096)).
Proof.
  buildPackG lower_grade lower_grade_rel lower_grade__lower_grade_rel lower_grade_rel_funct.
Defined.

#[global] Instance lower_grade_upack: @uPack (Grades_u ::UT nilUT) Grades_u.
Proof.
  buildUPackG lower_grade_rel lower_grade_rel_funct.
Defined.

Definition apply_late_policy_spec (late_days : {late_days: Z | True}) (g : Grades): Type :=
  Grades.

#[global] Hint Unfold apply_late_policy_spec: lia_unfold.

Definition apply_late_policy (late_days : {late_days: Z | True}) (g : Grades):
  apply_late_policy_spec late_days g.
Proof.
  destruct late_days as [late_days late_days_p].
  destruct g as [g g_p].
  let E := fresh "E" in destruct (late_days <? 9) as [|] eqn:E;
  [refine (exist (λ (g : Grades_u), Grades_wf g ∧ True) g ltac:(solver)) |
   let E := fresh "E" in destruct (late_days <? 17) as [|] eqn:E;
   [refine (lower_grade (exist (λ (g : Grades_u), Grades_wf g ∧ True) g ltac:(solver))) |
    let E := fresh "E" in destruct (late_days <? 21) as [|] eqn:E;
    [refine (lower_grade (lower_grade (exist (λ (g : Grades_u), Grades_wf g ∧ True) g ltac:(solver)))) |
     refine (lower_grade
             (lower_grade (lower_grade (exist (λ (g : Grades_u), Grades_wf g ∧ True) g ltac:(solver)))))]]].
Defined.

Inductive apply_late_policy_rel: Z → Grades_u → Grades_u → Prop :=
  | apply_late_policy_x_x_True: ∀ late_days g,
                                (late_days <? 9) == true → apply_late_policy_rel late_days g g
  | apply_late_policy_x_x_False_True: ∀ late_days g,
                                      (late_days <? 9) == false
                                      → ((late_days <? 17) == true
                                         → ∀ (lower_grade_res : Grades_u),
                                           lower_grade_rel g lower_grade_res
                                           → apply_late_policy_rel late_days g lower_grade_res)
  | apply_late_policy_x_x_False_False_True: ∀ late_days g,
                                            (late_days <? 9) == false
                                            → ((late_days <? 17) == false
                                               → ((late_days <? 21) == true
                                                  → ∀ (lower_grade_res : Grades_u),
                                                    lower_grade_rel g lower_grade_res
                                                    → ∀ (lower_grade_res_2 : Grades_u),
                                                      lower_grade_rel lower_grade_res lower_grade_res_2
                                                      → apply_late_policy_rel late_days g lower_grade_res_2))
  | apply_late_policy_x_x_False_False_False: ∀ late_days g,
                                             (late_days <? 9) == false
                                             → ((late_days <? 17) == false
                                                → ((late_days <? 21) == false
                                                   → ∀ (lower_grade_res : Grades_u),
                                                     lower_grade_rel g lower_grade_res
                                                     → ∀ (lower_grade_res_2 : Grades_u),
                                                       lower_grade_rel lower_grade_res lower_grade_res_2
                                                       → ∀ (lower_grade_res_3 : Grades_u),
                                                         lower_grade_rel lower_grade_res_2 lower_grade_res_3
                                                         → apply_late_policy_rel late_days g lower_grade_res_3)).

#[global] Hint Constructors apply_late_policy_rel: core_hint_db.

#[global] Instance apply_late_policy_lookup_rel: dictionary rel apply_late_policy := {
    lookup' := apply_late_policy_rel }.

#[global] Instance apply_late_policy_getF: getFunc apply_late_policy_rel := {
    getF' := apply_late_policy }.

Theorem apply_late_policy_rel_funct [late_days : Z] [g : Grades_u]:
  ∀ (VV VV' : Grades_u),
  apply_late_policy_rel late_days g VV → (apply_late_policy_rel late_days g VV' → VV = VV').
Proof.
  let E := fresh "E" in destruct (late_days <? 9) as [|] eqn:E;
  [ |
   let E := fresh "E" in destruct (late_days <? 17) as [|] eqn:E;
   [ | let E := fresh "E" in destruct (late_days <? 21) as [|] eqn:E]];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve apply_late_policy_rel_funct: f_rel_funct_db.

Theorem apply_late_policy_inv_lem g late_days apply_late_policy_inv_lem_res:
  apply_late_policy_rel late_days g apply_late_policy_inv_lem_res
  ↔ (((late_days <? 9) == true ∧ apply_late_policy_inv_lem_res == g
      ∨ (late_days <? 9) == false
        ∧ ((late_days <? 17) == true
           ∧ ∃ (lower_grade_res : Grades_u),
             lower_grade_rel g lower_grade_res ∧ apply_late_policy_inv_lem_res == lower_grade_res))
     ∨ (late_days <? 9) == false
       ∧ ((late_days <? 17) == false
          ∧ ((late_days <? 21) == true
             ∧ ∃ (lower_grade_res : Grades_u),
               lower_grade_rel g lower_grade_res
               ∧ ∃ (lower_grade_res_2 : Grades_u),
                 lower_grade_rel lower_grade_res lower_grade_res_2
                 ∧ apply_late_policy_inv_lem_res == lower_grade_res_2)))
    ∨ (late_days <? 9) == false
      ∧ ((late_days <? 17) == false
         ∧ ((late_days <? 21) == false
            ∧ ∃ (lower_grade_res : Grades_u),
              lower_grade_rel g lower_grade_res
              ∧ ∃ (lower_grade_res_2 : Grades_u),
                lower_grade_rel lower_grade_res lower_grade_res_2
                ∧ ∃ (lower_grade_res_3 : Grades_u),
                  lower_grade_rel lower_grade_res_2 lower_grade_res_3
                  ∧ apply_late_policy_inv_lem_res == lower_grade_res_3)).
Proof.
  rel_back' ((late_days <? 9) _::_
           (late_days <? 17) _::_
           (late_days <? 21) _::_ _nil).
Qed.

#[global] Hint Rewrite apply_late_policy_inv_lem: f_rel_back.

Theorem apply_late_policy_rel_ex
  (late_days : Z) (late_days_p : True) (g : Grades_u) (g_p : Grades_wf g ∧ True):
  apply_late_policy_rel
  late_days
  g
  ⌊ apply_late_policy (exist _ late_days late_days_p) (exist _ g g_p) -⌋.
Proof.
  Opaque apply_late_policy.
  existence_lemma_pre apply_late_policy;
  let E := fresh "E" in destruct (late_days <? 9) as [|] eqn:E;
  [fix_notations |
   let E := fresh "E" in destruct (late_days <? 17) as [|] eqn:E;
   [fix_notations |
    let E := fresh "E" in destruct (late_days <? 21) as [|] eqn:E;
    [fix_notations | fix_notations]]];
  simpl in *.
  Transparent apply_late_policy.
  all: (existence_lemma_quicksolve apply_late_policy; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve apply_late_policy_rel_ex: rel_ax_db.

#[global] Opaque apply_late_policy.

Theorem apply_late_policy__apply_late_policy_rel_rw
  (late_days : Z) (late_days_p : True) (g : Grades_u) (g_p : Grades_wf g ∧ True) (VV : Grades_u):
  ⌊ apply_late_policy (exist _ late_days late_days_p) (exist _ g g_p) -⌋ = VV
  ↔ apply_late_policy_rel late_days g VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite apply_late_policy__apply_late_policy_rel_rw: f_rel_funct_db.

#[global] Hint Resolve apply_late_policy__apply_late_policy_rel_rw: rel_ax_db.

#[global] Instance apply_late_policy_lookup_rw: dictionary rwLem apply_late_policy := {
    lookup' := apply_late_policy__apply_late_policy_rel_rw }.

Theorem apply_late_policy__apply_late_policy_rel
  (late_days : {late_days: Z | True}) (g : Grades) (VV : Grades_u):
  ⌊ apply_late_policy late_days g -⌋ = VV ↔ apply_late_policy_rel ⌊ late_days ⌋ ⌊ g ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite apply_late_policy__apply_late_policy_rel: f_rel_funct_db.

Theorem apply_late_policy__apply_late_policy_rel'
  (late_days_u : Z) (g_u : Grades_u) (late_days : {late_days: Z | True}) (g : Grades) (VV : Grades_u):
  late_days_u = ⌊ late_days ⌋
  → (g_u = ⌊ g ⌋
     → ⌊ apply_late_policy late_days g -⌋ = VV ↔ apply_late_policy_rel late_days_u g_u VV).
Proof.
  intros -> ->. refine (apply_late_policy__apply_late_policy_rel late_days g VV).
Qed.

#[global] Hint Resolve apply_late_policy__apply_late_policy_rel': f_rel_funct_db.

Theorem apply_late_policy_rel_mk
  (late_days : Z) (late_days_p : True) (g : Grades_u) (g_p : Grades_wf g ∧ True):
  {VV: _ | apply_late_policy_rel late_days g VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, apply_late_policy_rel late_days g VV)
          (apply_late_policy (exist _ late_days late_days_p) (exist _ g g_p))
          _);
  rewrite <- apply_late_policy__apply_late_policy_rel';
  quicksolve.
Qed.

#[global] Hint Resolve apply_late_policy_rel_mk: f_rel_funct_db.

#[global] Instance apply_late_policy_pack:
  @Pack
  ({late_days: Z | True}
   ::RT λ (late_days : {late_days: Z | True}), Grades ::RT λ (g : Grades), nilRT)
  (Z ::UT (Grades_u ::UT nilUT))
  ltac:(mkProjectsArgListTG (({late_days: Z | True}
  ::RT λ (late_days : {late_days: Z | True}),
       Grades ::RT λ (g : Grades), nilRT)) ((Z ::UT (Grades_u ::UT nilUT))))
  Grades_u
  (λ (x_47115878 : ArgList ({late_days: Z | True}
                            ::RT λ (late_days : {late_days: Z | True}), Grades ::RT λ (g : Grades), nilRT))
     (v_x_47115878 : Grades_u),
   ltac:(flattenP (λ (late_days : {late_days: Z | True})
   (g : Grades)
   (VV : Grades_u),
 Grades_wf VV ∧ True) x_47115878 v_x_47115878)).
Proof.
  buildPackG apply_late_policy apply_late_policy_rel apply_late_policy__apply_late_policy_rel apply_late_policy_rel_funct.
Defined.

#[global] Instance apply_late_policy_upack: @uPack (Z ::UT (Grades_u ::UT nilUT)) Grades_u.
Proof.
  buildUPackG apply_late_policy_rel apply_late_policy_rel_funct.
Defined.

Definition lower_grade_F_Minus_spec : Type :=
  {{∃ (lower_grade_res : Grades_u),
    lower_grade_rel (Grade_u F_u Minus_u) lower_grade_res ∧ lower_grade_res == Grade_u F_u Minus_u}}.

#[global] Hint Unfold lower_grade_F_Minus_spec: lia_unfold.

Theorem lower_grade_F_Minus : lower_grade_F_Minus_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (lower_grade_res : Grades_u),
           lower_grade_rel (Grade_u F_u Minus_u) lower_grade_res ∧ lower_grade_res == Grade_u F_u Minus_u)
          (# unit)
          ltac:(solver)).
Qed.

Definition lower_grade_thrice_spec : Type :=
  {{∃ (lower_grade_res : Grades_u),
    lower_grade_rel (Grade_u B_u Minus_u) lower_grade_res
    ∧ ∃ (lower_grade_res_2 : Grades_u),
      lower_grade_rel lower_grade_res lower_grade_res_2
      ∧ ∃ (lower_grade_res_3 : Grades_u),
        lower_grade_rel lower_grade_res_2 lower_grade_res_3 ∧ lower_grade_res_3 == Grade_u C_u Minus_u}}.

#[global] Hint Unfold lower_grade_thrice_spec: lia_unfold.

Theorem lower_grade_thrice : lower_grade_thrice_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (lower_grade_res : Grades_u),
           lower_grade_rel (Grade_u B_u Minus_u) lower_grade_res
           ∧ ∃ (lower_grade_res_2 : Grades_u),
             lower_grade_rel lower_grade_res lower_grade_res_2
             ∧ ∃ (lower_grade_res_3 : Grades_u),
               lower_grade_rel lower_grade_res_2 lower_grade_res_3 ∧ lower_grade_res_3 == Grade_u C_u Minus_u)
          (# unit)
          ltac:(solver)).
Qed.

Definition lower_grade_twice_spec : Type :=
  {{∃ (lower_grade_res : Grades_u),
    lower_grade_rel (Grade_u B_u Minus_u) lower_grade_res
    ∧ ∃ (lower_grade_res_2 : Grades_u),
      lower_grade_rel lower_grade_res lower_grade_res_2 ∧ lower_grade_res_2 == Grade_u C_u Natural_u}}.

#[global] Hint Unfold lower_grade_twice_spec: lia_unfold.

Theorem lower_grade_twice : lower_grade_twice_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (lower_grade_res : Grades_u),
           lower_grade_rel (Grade_u B_u Minus_u) lower_grade_res
           ∧ ∃ (lower_grade_res_2 : Grades_u),
             lower_grade_rel lower_grade_res lower_grade_res_2 ∧ lower_grade_res_2 == Grade_u C_u Natural_u)
          (# unit)
          ltac:(solver)).
Qed.

Definition no_penalty_for_mostly_on_time_spec
  (late_days : {late_days: Z | True}) (g : Grades) (h : {{ltbZ_rel ⌊ late_days ⌋ 9 true}}):
  Type :=
  {{∃ (apply_late_policy_res : Grades_u),
    apply_late_policy_rel ⌊ late_days ⌋ ⌊ g ⌋ apply_late_policy_res ∧ apply_late_policy_res == ⌊ g ⌋}}.

#[global] Hint Unfold no_penalty_for_mostly_on_time_spec: lia_unfold.

Theorem no_penalty_for_mostly_on_time
  (late_days : {late_days: Z | True}) (g : Grades) (h : {{ltbZ_rel ⌊ late_days ⌋ 9 true}}):
  no_penalty_for_mostly_on_time_spec late_days g h.
Proof.
  destruct late_days as [late_days late_days_p].
  destruct g as [g g_p].
  destruct h as [h h_p].
  let E := fresh "E" in destruct (late_days <? 9) as [|] eqn:E;
  [refine (subsumptionCast
           Unit
           (λ (VV : Unit),
            ∃ (apply_late_policy_res : Grades_u),
            apply_late_policy_rel late_days g apply_late_policy_res ∧ apply_late_policy_res == g)
           (# unit)
           ltac:(solver)) |
   refine (subsumptionCast
           Unit
           (λ (VV : Unit),
            ∃ (apply_late_policy_res : Grades_u),
            apply_late_policy_rel late_days g apply_late_policy_res ∧ apply_late_policy_res == g)
           (exist (λ (h : Unit), ltbZ_rel late_days 9 true) h ltac:(solver))
           ltac:(solver))].
Qed.

Inductive Day_u: Type :=
  | Friday_u: Day_u
  | Monday_u: Day_u
  | Saturday_u: Day_u
  | Sunday_u: Day_u
  | Thursday_u: Day_u
  | Tuesday_u: Day_u
  | Wednesday_u: Day_u.

Fixpoint Day_eq (x y : Day_u): bool :=
  match (x, y) with
  | (Friday_u, Friday_u) => true
  | (Monday_u, Monday_u) => true
  | (Saturday_u, Saturday_u) => true
  | (Sunday_u, Sunday_u) => true
  | (Thursday_u, Thursday_u) => true
  | (Tuesday_u, Tuesday_u) => true
  | (Wednesday_u, Wednesday_u) => true
  | (_, _) => false
  end.

Theorem Day_eq_refl : ∀ (x : Day_u), is_true (Day_eq x x).
Proof.
  eq_refl_rec.
Qed.

#[global] Hint Resolve Day_eq_refl: eq_hint_db.

Theorem Day_eqb_eq : ∀ (s t : Day_u), is_true (Day_eq s t) → s = t.
Proof.
  eqb_eq_lem.
Qed.

#[global] Hint Resolve Day_eqb_eq: eq_hint_db.

#[global] Instance leibnitz_eq_Day: LeibnitzEqB := {
    equalB' := Day_eq;
    refl' := Day_eq_refl;
    eqb_eq' := Day_eqb_eq }.

Fixpoint Day_wf (x : Day_u): Prop :=
  match x with
  | Friday_u => True
  | Monday_u => True
  | Saturday_u => True
  | Sunday_u => True
  | Thursday_u => True
  | Tuesday_u => True
  | Wednesday_u => True
  end.

Theorem Day_wf_ref [p : Day_u → Prop] (tm : {v: Day_u | Day_wf v ∧ p v}): Day_wf ⌊ tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation Day := {x: Day_u | Day_wf x ∧ True}.

Definition Friday_lem : Day_wf Friday_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Friday : Day :=
  exist _ Friday_u Friday_lem.

Definition Monday_lem : Day_wf Monday_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Monday : Day :=
  exist _ Monday_u Monday_lem.

Definition Saturday_lem : Day_wf Saturday_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Saturday : Day :=
  exist _ Saturday_u Saturday_lem.

Definition Sunday_lem : Day_wf Sunday_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Sunday : Day :=
  exist _ Sunday_u Sunday_lem.

Definition Thursday_lem : Day_wf Thursday_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Thursday : Day :=
  exist _ Thursday_u Thursday_lem.

Definition Tuesday_lem : Day_wf Tuesday_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Tuesday : Day :=
  exist _ Tuesday_u Tuesday_lem.

Definition Wednesday_lem : Day_wf Wednesday_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Wednesday : Day :=
  exist _ Wednesday_u Wednesday_lem.

#[global] Hint Resolve Day_wf_ref: wf_constr_db.

#[global] Hint Unfold Day_wf: wf_constr_db.

#[global] Hint Resolve Day_eq: ref_constr_db.

#[global] Hint Unfold Friday: ref_constr_db.

#[global] Hint Unfold Monday: ref_constr_db.

#[global] Hint Unfold Saturday: ref_constr_db.

#[global] Hint Unfold Sunday: ref_constr_db.

#[global] Hint Unfold Thursday: ref_constr_db.

#[global] Hint Unfold Tuesday: ref_constr_db.

#[global] Hint Unfold Wednesday: ref_constr_db.

Definition next_weekday_spec (ds_d3iT : Day): Type :=
  Day.

#[global] Hint Unfold next_weekday_spec: lia_unfold.

Definition next_weekday (ds_d3iT : Day): next_weekday_spec ds_d3iT.
Proof.
  destruct ds_d3iT as [ds_d3iT ds_d3iT_p].
  destruct ds_d3iT as [| | | | | |].
  - refine Monday.
  - refine Tuesday.
  - refine Monday.
  - refine Monday.
  - refine Friday.
  - refine Wednesday.
  - refine Thursday.
Defined.

Inductive next_weekday_rel: Day_u → Day_u → Prop :=
  | next_weekday_Friday: next_weekday_rel Friday_u Monday_u
  | next_weekday_Monday: next_weekday_rel Monday_u Tuesday_u
  | next_weekday_Saturday: next_weekday_rel Saturday_u Monday_u
  | next_weekday_Sunday: next_weekday_rel Sunday_u Monday_u
  | next_weekday_Thursday: next_weekday_rel Thursday_u Friday_u
  | next_weekday_Tuesday: next_weekday_rel Tuesday_u Wednesday_u
  | next_weekday_Wednesday: next_weekday_rel Wednesday_u Thursday_u.

#[global] Hint Constructors next_weekday_rel: core_hint_db.

#[global] Instance next_weekday_lookup_rel: dictionary rel next_weekday := {
    lookup' := next_weekday_rel }.

#[global] Instance next_weekday_getF: getFunc next_weekday_rel := { getF' := next_weekday }.

Theorem next_weekday_rel_funct [ds_d3iT : Day_u]:
  ∀ (VV VV' : Day_u), next_weekday_rel ds_d3iT VV → (next_weekday_rel ds_d3iT VV' → VV = VV').
Proof.
  destruct ds_d3iT as [| | | | | |]; rel_functionhood_body.
Qed.

#[global] Hint Resolve next_weekday_rel_funct: f_rel_funct_db.

Theorem next_weekday_Friday_lem next_weekday_Friday_lem_res:
  next_weekday_rel Friday_u next_weekday_Friday_lem_res ↔ next_weekday_Friday_lem_res == Monday_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite next_weekday_Friday_lem: f_rel_back.

Theorem next_weekday_Monday_lem next_weekday_Monday_lem_res:
  next_weekday_rel Monday_u next_weekday_Monday_lem_res ↔ next_weekday_Monday_lem_res == Tuesday_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite next_weekday_Monday_lem: f_rel_back.

Theorem next_weekday_Saturday_lem next_weekday_Saturday_lem_res:
  next_weekday_rel Saturday_u next_weekday_Saturday_lem_res
  ↔ next_weekday_Saturday_lem_res == Monday_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite next_weekday_Saturday_lem: f_rel_back.

Theorem next_weekday_Sunday_lem next_weekday_Sunday_lem_res:
  next_weekday_rel Sunday_u next_weekday_Sunday_lem_res ↔ next_weekday_Sunday_lem_res == Monday_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite next_weekday_Sunday_lem: f_rel_back.

Theorem next_weekday_Thursday_lem next_weekday_Thursday_lem_res:
  next_weekday_rel Thursday_u next_weekday_Thursday_lem_res
  ↔ next_weekday_Thursday_lem_res == Friday_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite next_weekday_Thursday_lem: f_rel_back.

Theorem next_weekday_Tuesday_lem next_weekday_Tuesday_lem_res:
  next_weekday_rel Tuesday_u next_weekday_Tuesday_lem_res
  ↔ next_weekday_Tuesday_lem_res == Wednesday_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite next_weekday_Tuesday_lem: f_rel_back.

Theorem next_weekday_Wednesday_lem next_weekday_Wednesday_lem_res:
  next_weekday_rel Wednesday_u next_weekday_Wednesday_lem_res
  ↔ next_weekday_Wednesday_lem_res == Thursday_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite next_weekday_Wednesday_lem: f_rel_back.

Theorem next_weekday_rel_ex (ds_d3iT : Day_u) (ds_d3iT_p : Day_wf ds_d3iT ∧ True):
  next_weekday_rel ds_d3iT ⌊ next_weekday (exist _ ds_d3iT ds_d3iT_p) -⌋.
Proof.
  Opaque next_weekday.
  existence_lemma_pre next_weekday;
  destruct ds_d3iT as [| | | | | |];
  [fix_notations |
   fix_notations |
   fix_notations |
   fix_notations |
   fix_notations |
   fix_notations |
   fix_notations];
  simpl in *.
  Transparent next_weekday.
  all: (existence_lemma_quicksolve next_weekday; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve next_weekday_rel_ex: rel_ax_db.

#[global] Opaque next_weekday.

Theorem next_weekday__next_weekday_rel_rw
  (ds_d3iT : Day_u) (ds_d3iT_p : Day_wf ds_d3iT ∧ True) (VV : Day_u):
  ⌊ next_weekday (exist _ ds_d3iT ds_d3iT_p) -⌋ = VV ↔ next_weekday_rel ds_d3iT VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite next_weekday__next_weekday_rel_rw: f_rel_funct_db.

#[global] Hint Resolve next_weekday__next_weekday_rel_rw: rel_ax_db.

#[global] Instance next_weekday_lookup_rw: dictionary rwLem next_weekday := {
    lookup' := next_weekday__next_weekday_rel_rw }.

Theorem next_weekday__next_weekday_rel (ds_d3iT : Day) (VV : Day_u):
  ⌊ next_weekday ds_d3iT -⌋ = VV ↔ next_weekday_rel ⌊ ds_d3iT ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite next_weekday__next_weekday_rel: f_rel_funct_db.

Theorem next_weekday__next_weekday_rel' (ds_d3iT_u : Day_u) (ds_d3iT : Day) (VV : Day_u):
  ds_d3iT_u = ⌊ ds_d3iT ⌋ → ⌊ next_weekday ds_d3iT -⌋ = VV ↔ next_weekday_rel ds_d3iT_u VV.
Proof.
  intros ->. refine (next_weekday__next_weekday_rel ds_d3iT VV).
Qed.

#[global] Hint Resolve next_weekday__next_weekday_rel': f_rel_funct_db.

Theorem next_weekday_rel_mk (ds_d3iT : Day_u) (ds_d3iT_p : Day_wf ds_d3iT ∧ True):
  {VV: _ | next_weekday_rel ds_d3iT VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, next_weekday_rel ds_d3iT VV)
          (next_weekday (exist _ ds_d3iT ds_d3iT_p))
          _);
  rewrite <- next_weekday__next_weekday_rel';
  quicksolve.
Qed.

#[global] Hint Resolve next_weekday_rel_mk: f_rel_funct_db.

#[global] Instance next_weekday_pack:
  @Pack
  (Day ::RT λ (ds_d3iT : Day), nilRT)
  (Day_u ::UT nilUT)
  ltac:(mkProjectsArgListTG ((Day ::RT λ (ds_d3iT : Day), nilRT)) ((Day_u ::UT nilUT)))
  Day_u
  (λ (x_20104880 : ArgList (Day ::RT λ (ds_d3iT : Day), nilRT)) (v_x_20104880 : Day_u),
   ltac:(flattenP (λ (ds_d3iT : Day) (VV : Day_u), Day_wf VV ∧ True) x_20104880 v_x_20104880)).
Proof.
  buildPackG next_weekday next_weekday_rel next_weekday__next_weekday_rel next_weekday_rel_funct.
Defined.

#[global] Instance next_weekday_upack: @uPack (Day_u ::UT nilUT) Day_u.
Proof.
  buildUPackG next_weekday_rel next_weekday_rel_funct.
Defined.

Definition test_next_weekday_spec : Type :=
  {{∃ (next_weekday_res : Day_u),
    next_weekday_rel Saturday_u next_weekday_res
    ∧ ∃ (next_weekday_res_2 : Day_u),
      next_weekday_rel next_weekday_res next_weekday_res_2 ∧ next_weekday_res_2 == Tuesday_u}}.

#[global] Hint Unfold test_next_weekday_spec: lia_unfold.

Theorem test_next_weekday : test_next_weekday_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (next_weekday_res : Day_u),
           next_weekday_rel Saturday_u next_weekday_res
           ∧ ∃ (next_weekday_res_2 : Day_u),
             next_weekday_rel next_weekday_res next_weekday_res_2 ∧ next_weekday_res_2 == Tuesday_u)
          (# unit)
          ltac:(solver)).
Qed.

Inductive Comparison_u: Type :=
  | Eq_u: Comparison_u | Gt_u: Comparison_u | Lt_u: Comparison_u.

Fixpoint Comparison_eq (x y : Comparison_u): bool :=
  match (x, y) with
  | (Eq_u, Eq_u) => true
  | (Gt_u, Gt_u) => true
  | (Lt_u, Lt_u) => true
  | (_, _) => false
  end.

Theorem Comparison_eq_refl : ∀ (x : Comparison_u), is_true (Comparison_eq x x).
Proof.
  eq_refl_rec.
Qed.

#[global] Hint Resolve Comparison_eq_refl: eq_hint_db.

Theorem Comparison_eqb_eq : ∀ (s t : Comparison_u), is_true (Comparison_eq s t) → s = t.
Proof.
  eqb_eq_lem.
Qed.

#[global] Hint Resolve Comparison_eqb_eq: eq_hint_db.

#[global] Instance leibnitz_eq_Comparison: LeibnitzEqB := {
    equalB' := Comparison_eq;
    refl' := Comparison_eq_refl;
    eqb_eq' := Comparison_eqb_eq }.

Fixpoint Comparison_wf (x : Comparison_u): Prop :=
  match x with | Eq_u => True | Gt_u => True | Lt_u => True end.

Theorem Comparison_wf_ref
  [p : Comparison_u → Prop] (tm : {v: Comparison_u | Comparison_wf v ∧ p v}):
  Comparison_wf ⌊ tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation Comparison := {x: Comparison_u | Comparison_wf x ∧ True}.

Definition Eq_lem : Comparison_wf Eq_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Eq : Comparison :=
  exist _ Eq_u Eq_lem.

Definition Gt_lem : Comparison_wf Gt_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Gt : Comparison :=
  exist _ Gt_u Gt_lem.

Definition Lt_lem : Comparison_wf Lt_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Lt : Comparison :=
  exist _ Lt_u Lt_lem.

#[global] Hint Resolve Comparison_wf_ref: wf_constr_db.

#[global] Hint Unfold Comparison_wf: wf_constr_db.

#[global] Hint Resolve Comparison_eq: ref_constr_db.

#[global] Hint Unfold Eq: ref_constr_db.

#[global] Hint Unfold Gt: ref_constr_db.

#[global] Hint Unfold Lt: ref_constr_db.

Definition letter_comparison_spec (ds_d3hh ds_d3hi : Letter): Type :=
  Comparison.

#[global] Hint Unfold letter_comparison_spec: lia_unfold.

Definition letter_comparison (ds_d3hh ds_d3hi : Letter): letter_comparison_spec ds_d3hh ds_d3hi.
Proof.
  destruct ds_d3hh as [ds_d3hh ds_d3hh_p].
  destruct ds_d3hi as [ds_d3hi ds_d3hi_p].
  destruct ds_d3hh as [| | | |].
  - destruct ds_d3hi as [| | | |].
    + refine Eq.
    + refine Gt.
    + refine Gt.
    + refine Gt.
    + refine Gt.
  - destruct ds_d3hi as [| | | |].
    + refine Lt.
    + refine Eq.
    + refine Gt.
    + refine Gt.
    + refine Gt.
  - destruct ds_d3hi as [| | | |].
    + refine Lt.
    + refine Lt.
    + refine Eq.
    + refine Gt.
    + refine Gt.
  - destruct ds_d3hi as [| | | |].
    + refine Lt.
    + refine Lt.
    + refine Lt.
    + refine Eq.
    + refine Gt.
  - destruct ds_d3hi as [| | | |].
    + refine Lt.
    + refine Lt.
    + refine Lt.
    + refine Lt.
    + refine Eq.
Defined.

Inductive letter_comparison_rel: Letter_u → Letter_u → Comparison_u → Prop :=
  | letter_comparison_A_A: letter_comparison_rel A_u A_u Eq_u
  | letter_comparison_A_B: letter_comparison_rel A_u B_u Gt_u
  | letter_comparison_A_C: letter_comparison_rel A_u C_u Gt_u
  | letter_comparison_A_D: letter_comparison_rel A_u D_u Gt_u
  | letter_comparison_A_F: letter_comparison_rel A_u F_u Gt_u
  | letter_comparison_B_A: letter_comparison_rel B_u A_u Lt_u
  | letter_comparison_B_B: letter_comparison_rel B_u B_u Eq_u
  | letter_comparison_B_C: letter_comparison_rel B_u C_u Gt_u
  | letter_comparison_B_D: letter_comparison_rel B_u D_u Gt_u
  | letter_comparison_B_F: letter_comparison_rel B_u F_u Gt_u
  | letter_comparison_C_A: letter_comparison_rel C_u A_u Lt_u
  | letter_comparison_C_B: letter_comparison_rel C_u B_u Lt_u
  | letter_comparison_C_C: letter_comparison_rel C_u C_u Eq_u
  | letter_comparison_C_D: letter_comparison_rel C_u D_u Gt_u
  | letter_comparison_C_F: letter_comparison_rel C_u F_u Gt_u
  | letter_comparison_D_A: letter_comparison_rel D_u A_u Lt_u
  | letter_comparison_D_B: letter_comparison_rel D_u B_u Lt_u
  | letter_comparison_D_C: letter_comparison_rel D_u C_u Lt_u
  | letter_comparison_D_D: letter_comparison_rel D_u D_u Eq_u
  | letter_comparison_D_F: letter_comparison_rel D_u F_u Gt_u
  | letter_comparison_F_A: letter_comparison_rel F_u A_u Lt_u
  | letter_comparison_F_B: letter_comparison_rel F_u B_u Lt_u
  | letter_comparison_F_C: letter_comparison_rel F_u C_u Lt_u
  | letter_comparison_F_D: letter_comparison_rel F_u D_u Lt_u
  | letter_comparison_F_F: letter_comparison_rel F_u F_u Eq_u.

#[global] Hint Constructors letter_comparison_rel: core_hint_db.

#[global] Instance letter_comparison_lookup_rel: dictionary rel letter_comparison := {
    lookup' := letter_comparison_rel }.

#[global] Instance letter_comparison_getF: getFunc letter_comparison_rel := {
    getF' := letter_comparison }.

Theorem letter_comparison_rel_funct [ds_d3hh ds_d3hi : Letter_u]:
  ∀ (VV VV' : Comparison_u),
  letter_comparison_rel ds_d3hh ds_d3hi VV → (letter_comparison_rel ds_d3hh ds_d3hi VV' → VV = VV').
Proof.
  destruct ds_d3hh as [| | | |];
  [destruct ds_d3hi as [| | | |] |
   destruct ds_d3hi as [| | | |] |
   destruct ds_d3hi as [| | | |] |
   destruct ds_d3hi as [| | | |] |
   destruct ds_d3hi as [| | | |]];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve letter_comparison_rel_funct: f_rel_funct_db.

Theorem letter_comparison_A_A_lem letter_comparison_A_A_lem_res:
  letter_comparison_rel A_u A_u letter_comparison_A_A_lem_res ↔ letter_comparison_A_A_lem_res == Eq_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letter_comparison_A_A_lem: f_rel_back.

Theorem letter_comparison_A_B_lem letter_comparison_A_B_lem_res:
  letter_comparison_rel A_u B_u letter_comparison_A_B_lem_res ↔ letter_comparison_A_B_lem_res == Gt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letter_comparison_A_B_lem: f_rel_back.

Theorem letter_comparison_A_C_lem letter_comparison_A_C_lem_res:
  letter_comparison_rel A_u C_u letter_comparison_A_C_lem_res ↔ letter_comparison_A_C_lem_res == Gt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letter_comparison_A_C_lem: f_rel_back.

Theorem letter_comparison_A_D_lem letter_comparison_A_D_lem_res:
  letter_comparison_rel A_u D_u letter_comparison_A_D_lem_res ↔ letter_comparison_A_D_lem_res == Gt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letter_comparison_A_D_lem: f_rel_back.

Theorem letter_comparison_A_F_lem letter_comparison_A_F_lem_res:
  letter_comparison_rel A_u F_u letter_comparison_A_F_lem_res ↔ letter_comparison_A_F_lem_res == Gt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letter_comparison_A_F_lem: f_rel_back.

Theorem letter_comparison_B_A_lem letter_comparison_B_A_lem_res:
  letter_comparison_rel B_u A_u letter_comparison_B_A_lem_res ↔ letter_comparison_B_A_lem_res == Lt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letter_comparison_B_A_lem: f_rel_back.

Theorem letter_comparison_B_B_lem letter_comparison_B_B_lem_res:
  letter_comparison_rel B_u B_u letter_comparison_B_B_lem_res ↔ letter_comparison_B_B_lem_res == Eq_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letter_comparison_B_B_lem: f_rel_back.

Theorem letter_comparison_B_C_lem letter_comparison_B_C_lem_res:
  letter_comparison_rel B_u C_u letter_comparison_B_C_lem_res ↔ letter_comparison_B_C_lem_res == Gt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letter_comparison_B_C_lem: f_rel_back.

Theorem letter_comparison_B_D_lem letter_comparison_B_D_lem_res:
  letter_comparison_rel B_u D_u letter_comparison_B_D_lem_res ↔ letter_comparison_B_D_lem_res == Gt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letter_comparison_B_D_lem: f_rel_back.

Theorem letter_comparison_B_F_lem letter_comparison_B_F_lem_res:
  letter_comparison_rel B_u F_u letter_comparison_B_F_lem_res ↔ letter_comparison_B_F_lem_res == Gt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letter_comparison_B_F_lem: f_rel_back.

Theorem letter_comparison_C_A_lem letter_comparison_C_A_lem_res:
  letter_comparison_rel C_u A_u letter_comparison_C_A_lem_res ↔ letter_comparison_C_A_lem_res == Lt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letter_comparison_C_A_lem: f_rel_back.

Theorem letter_comparison_C_B_lem letter_comparison_C_B_lem_res:
  letter_comparison_rel C_u B_u letter_comparison_C_B_lem_res ↔ letter_comparison_C_B_lem_res == Lt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letter_comparison_C_B_lem: f_rel_back.

Theorem letter_comparison_C_C_lem letter_comparison_C_C_lem_res:
  letter_comparison_rel C_u C_u letter_comparison_C_C_lem_res ↔ letter_comparison_C_C_lem_res == Eq_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letter_comparison_C_C_lem: f_rel_back.

Theorem letter_comparison_C_D_lem letter_comparison_C_D_lem_res:
  letter_comparison_rel C_u D_u letter_comparison_C_D_lem_res ↔ letter_comparison_C_D_lem_res == Gt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letter_comparison_C_D_lem: f_rel_back.

Theorem letter_comparison_C_F_lem letter_comparison_C_F_lem_res:
  letter_comparison_rel C_u F_u letter_comparison_C_F_lem_res ↔ letter_comparison_C_F_lem_res == Gt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letter_comparison_C_F_lem: f_rel_back.

Theorem letter_comparison_D_A_lem letter_comparison_D_A_lem_res:
  letter_comparison_rel D_u A_u letter_comparison_D_A_lem_res ↔ letter_comparison_D_A_lem_res == Lt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letter_comparison_D_A_lem: f_rel_back.

Theorem letter_comparison_D_B_lem letter_comparison_D_B_lem_res:
  letter_comparison_rel D_u B_u letter_comparison_D_B_lem_res ↔ letter_comparison_D_B_lem_res == Lt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letter_comparison_D_B_lem: f_rel_back.

Theorem letter_comparison_D_C_lem letter_comparison_D_C_lem_res:
  letter_comparison_rel D_u C_u letter_comparison_D_C_lem_res ↔ letter_comparison_D_C_lem_res == Lt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letter_comparison_D_C_lem: f_rel_back.

Theorem letter_comparison_D_D_lem letter_comparison_D_D_lem_res:
  letter_comparison_rel D_u D_u letter_comparison_D_D_lem_res ↔ letter_comparison_D_D_lem_res == Eq_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letter_comparison_D_D_lem: f_rel_back.

Theorem letter_comparison_D_F_lem letter_comparison_D_F_lem_res:
  letter_comparison_rel D_u F_u letter_comparison_D_F_lem_res ↔ letter_comparison_D_F_lem_res == Gt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letter_comparison_D_F_lem: f_rel_back.

Theorem letter_comparison_F_A_lem letter_comparison_F_A_lem_res:
  letter_comparison_rel F_u A_u letter_comparison_F_A_lem_res ↔ letter_comparison_F_A_lem_res == Lt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letter_comparison_F_A_lem: f_rel_back.

Theorem letter_comparison_F_B_lem letter_comparison_F_B_lem_res:
  letter_comparison_rel F_u B_u letter_comparison_F_B_lem_res ↔ letter_comparison_F_B_lem_res == Lt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letter_comparison_F_B_lem: f_rel_back.

Theorem letter_comparison_F_C_lem letter_comparison_F_C_lem_res:
  letter_comparison_rel F_u C_u letter_comparison_F_C_lem_res ↔ letter_comparison_F_C_lem_res == Lt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letter_comparison_F_C_lem: f_rel_back.

Theorem letter_comparison_F_D_lem letter_comparison_F_D_lem_res:
  letter_comparison_rel F_u D_u letter_comparison_F_D_lem_res ↔ letter_comparison_F_D_lem_res == Lt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letter_comparison_F_D_lem: f_rel_back.

Theorem letter_comparison_F_F_lem letter_comparison_F_F_lem_res:
  letter_comparison_rel F_u F_u letter_comparison_F_F_lem_res ↔ letter_comparison_F_F_lem_res == Eq_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letter_comparison_F_F_lem: f_rel_back.

Theorem letter_comparison_rel_ex
  (ds_d3hh : Letter_u)
  (ds_d3hh_p : Letter_wf ds_d3hh ∧ True)
  (ds_d3hi : Letter_u)
  (ds_d3hi_p : Letter_wf ds_d3hi ∧ True):
  letter_comparison_rel
  ds_d3hh
  ds_d3hi
  ⌊ letter_comparison (exist _ ds_d3hh ds_d3hh_p) (exist _ ds_d3hi ds_d3hi_p) -⌋.
Proof.
  Opaque letter_comparison.
  existence_lemma_pre letter_comparison;
  destruct ds_d3hh as [| | | |];
  [destruct ds_d3hi as [| | | |];
   [fix_notations | fix_notations | fix_notations | fix_notations | fix_notations] |
   destruct ds_d3hi as [| | | |];
   [fix_notations | fix_notations | fix_notations | fix_notations | fix_notations] |
   destruct ds_d3hi as [| | | |];
   [fix_notations | fix_notations | fix_notations | fix_notations | fix_notations] |
   destruct ds_d3hi as [| | | |];
   [fix_notations | fix_notations | fix_notations | fix_notations | fix_notations] |
   destruct ds_d3hi as [| | | |];
   [fix_notations | fix_notations | fix_notations | fix_notations | fix_notations]];
  simpl in *.
  Transparent letter_comparison.
  all: (existence_lemma_quicksolve letter_comparison; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve letter_comparison_rel_ex: rel_ax_db.

#[global] Opaque letter_comparison.

Theorem letter_comparison__letter_comparison_rel_rw
  (ds_d3hh : Letter_u)
  (ds_d3hh_p : Letter_wf ds_d3hh ∧ True)
  (ds_d3hi : Letter_u)
  (ds_d3hi_p : Letter_wf ds_d3hi ∧ True)
  (VV : Comparison_u):
  ⌊ letter_comparison (exist _ ds_d3hh ds_d3hh_p) (exist _ ds_d3hi ds_d3hi_p) -⌋ = VV
  ↔ letter_comparison_rel ds_d3hh ds_d3hi VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite letter_comparison__letter_comparison_rel_rw: f_rel_funct_db.

#[global] Hint Resolve letter_comparison__letter_comparison_rel_rw: rel_ax_db.

#[global] Instance letter_comparison_lookup_rw: dictionary rwLem letter_comparison := {
    lookup' := letter_comparison__letter_comparison_rel_rw }.

Theorem letter_comparison__letter_comparison_rel (ds_d3hh ds_d3hi : Letter) (VV : Comparison_u):
  ⌊ letter_comparison ds_d3hh ds_d3hi -⌋ = VV ↔ letter_comparison_rel ⌊ ds_d3hh ⌋ ⌊ ds_d3hi ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite letter_comparison__letter_comparison_rel: f_rel_funct_db.

Theorem letter_comparison__letter_comparison_rel'
  (ds_d3hh_u ds_d3hi_u : Letter_u) (ds_d3hh ds_d3hi : Letter) (VV : Comparison_u):
  ds_d3hh_u = ⌊ ds_d3hh ⌋
  → (ds_d3hi_u = ⌊ ds_d3hi ⌋
     → ⌊ letter_comparison ds_d3hh ds_d3hi -⌋ = VV ↔ letter_comparison_rel ds_d3hh_u ds_d3hi_u VV).
Proof.
  intros -> ->. refine (letter_comparison__letter_comparison_rel ds_d3hh ds_d3hi VV).
Qed.

#[global] Hint Resolve letter_comparison__letter_comparison_rel': f_rel_funct_db.

Theorem letter_comparison_rel_mk
  (ds_d3hh : Letter_u)
  (ds_d3hh_p : Letter_wf ds_d3hh ∧ True)
  (ds_d3hi : Letter_u)
  (ds_d3hi_p : Letter_wf ds_d3hi ∧ True):
  {VV: _ | letter_comparison_rel ds_d3hh ds_d3hi VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, letter_comparison_rel ds_d3hh ds_d3hi VV)
          (letter_comparison (exist _ ds_d3hh ds_d3hh_p) (exist _ ds_d3hi ds_d3hi_p))
          _);
  rewrite <- letter_comparison__letter_comparison_rel';
  quicksolve.
Qed.

#[global] Hint Resolve letter_comparison_rel_mk: f_rel_funct_db.

#[global] Instance letter_comparison_pack:
  @Pack
  (Letter ::RT λ (ds_d3hh : Letter), Letter ::RT λ (ds_d3hi : Letter), nilRT)
  (Letter_u ::UT (Letter_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((Letter
  ::RT λ (ds_d3hh : Letter),
       Letter ::RT λ (ds_d3hi : Letter), nilRT)) ((Letter_u ::UT (Letter_u ::UT nilUT))))
  Comparison_u
  (λ (x_61379309 : ArgList (Letter
                            ::RT λ (ds_d3hh : Letter), Letter ::RT λ (ds_d3hi : Letter), nilRT))
     (v_x_61379309 : Comparison_u),
   ltac:(flattenP (λ (ds_d3hh ds_d3hi : Letter) (VV : Comparison_u),
 Comparison_wf VV ∧ True) x_61379309 v_x_61379309)).
Proof.
  buildPackG letter_comparison letter_comparison_rel letter_comparison__letter_comparison_rel letter_comparison_rel_funct.
Defined.

#[global] Instance letter_comparison_upack:
  @uPack (Letter_u ::UT (Letter_u ::UT nilUT)) Comparison_u.
Proof.
  buildUPackG letter_comparison_rel letter_comparison_rel_funct.
Defined.

Definition letter_comparison_eq_spec (ds_d3hg : Letter): Type :=
  {{∃ (letter_comparison_res : Comparison_u),
    letter_comparison_rel ⌊ ds_d3hg ⌋ ⌊ ds_d3hg ⌋ letter_comparison_res
    ∧ letter_comparison_res == Eq_u}}.

#[global] Hint Unfold letter_comparison_eq_spec: lia_unfold.

Theorem letter_comparison_eq (ds_d3hg : Letter): letter_comparison_eq_spec ds_d3hg.
Proof.
  destruct ds_d3hg as [ds_d3hg ds_d3hg_p].
  destruct ds_d3hg as [| | | |].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (letter_comparison_res : Comparison_u),
             letter_comparison_rel A_u A_u letter_comparison_res ∧ letter_comparison_res == Eq_u)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (letter_comparison_res : Comparison_u),
             letter_comparison_rel B_u B_u letter_comparison_res ∧ letter_comparison_res == Eq_u)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (letter_comparison_res : Comparison_u),
             letter_comparison_rel C_u C_u letter_comparison_res ∧ letter_comparison_res == Eq_u)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (letter_comparison_res : Comparison_u),
             letter_comparison_rel D_u D_u letter_comparison_res ∧ letter_comparison_res == Eq_u)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (letter_comparison_res : Comparison_u),
             letter_comparison_rel F_u F_u letter_comparison_res ∧ letter_comparison_res == Eq_u)
            (# unit)
            ltac:(solver)).
Qed.

Definition lower_letter_lowers_spec
  (l : Letter)
  (p : {{∃ (letter_comparison_res : Comparison_u),
         letter_comparison_rel F_u ⌊ l ⌋ letter_comparison_res ∧ letter_comparison_res == Lt_u}}):
  Type :=
  {{∃ (lower_letter_res : Letter_u),
    lower_letter_rel ⌊ l ⌋ lower_letter_res
    ∧ ∃ (letter_comparison_res : Comparison_u),
      letter_comparison_rel lower_letter_res ⌊ l ⌋ letter_comparison_res
      ∧ letter_comparison_res == Lt_u}}.

#[global] Hint Unfold lower_letter_lowers_spec: lia_unfold.

Theorem lower_letter_lowers
  (l : Letter)
  (p : {{∃ (letter_comparison_res : Comparison_u),
         letter_comparison_rel F_u ⌊ l ⌋ letter_comparison_res ∧ letter_comparison_res == Lt_u}}):
  lower_letter_lowers_spec l p.
Proof.
  destruct l as [l l_p].
  destruct p as [p p_p].
  destruct l as [| | | |].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (lower_letter_res : Letter_u),
             lower_letter_rel A_u lower_letter_res
             ∧ ∃ (letter_comparison_res : Comparison_u),
               letter_comparison_rel lower_letter_res A_u letter_comparison_res ∧ letter_comparison_res == Lt_u)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (lower_letter_res : Letter_u),
             lower_letter_rel B_u lower_letter_res
             ∧ ∃ (letter_comparison_res : Comparison_u),
               letter_comparison_rel lower_letter_res B_u letter_comparison_res ∧ letter_comparison_res == Lt_u)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (lower_letter_res : Letter_u),
             lower_letter_rel C_u lower_letter_res
             ∧ ∃ (letter_comparison_res : Comparison_u),
               letter_comparison_rel lower_letter_res C_u letter_comparison_res ∧ letter_comparison_res == Lt_u)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (lower_letter_res : Letter_u),
             lower_letter_rel D_u lower_letter_res
             ∧ ∃ (letter_comparison_res : Comparison_u),
               letter_comparison_rel lower_letter_res D_u letter_comparison_res ∧ letter_comparison_res == Lt_u)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (lower_letter_res : Letter_u),
             lower_letter_rel F_u lower_letter_res
             ∧ ∃ (letter_comparison_res : Comparison_u),
               letter_comparison_rel lower_letter_res F_u letter_comparison_res ∧ letter_comparison_res == Lt_u)
            (exist (λ (p : Unit),
                    ∃ (letter_comparison_res : Comparison_u),
                    letter_comparison_rel F_u F_u letter_comparison_res
                    ∧ letter_comparison_res == Lt_u) p ltac:(solver))
            ltac:(solver)).
Qed.

Definition modifier_comparison_spec (ds_d3h8 ds_d3h9 : Modifier): Type :=
  Comparison.

#[global] Hint Unfold modifier_comparison_spec: lia_unfold.

Definition modifier_comparison (ds_d3h8 ds_d3h9 : Modifier):
  modifier_comparison_spec ds_d3h8 ds_d3h9.
Proof.
  destruct ds_d3h8 as [ds_d3h8 ds_d3h8_p].
  destruct ds_d3h9 as [ds_d3h9 ds_d3h9_p].
  destruct ds_d3h8 as [| |].
  - destruct ds_d3h9 as [| |].
    + refine Eq.
    + refine Lt.
    + refine Lt.
  - destruct ds_d3h9 as [| |].
    + refine Gt.
    + refine Eq.
    + refine Lt.
  - destruct ds_d3h9 as [| |].
    + refine Gt.
    + refine Gt.
    + refine Eq.
Defined.

Inductive modifier_comparison_rel: Modifier_u → Modifier_u → Comparison_u → Prop :=
  | modifier_comparison_Minus_Minus: modifier_comparison_rel Minus_u Minus_u Eq_u
  | modifier_comparison_Minus_Natural: modifier_comparison_rel Minus_u Natural_u Lt_u
  | modifier_comparison_Minus_Plus: modifier_comparison_rel Minus_u Plus_u Lt_u
  | modifier_comparison_Natural_Minus: modifier_comparison_rel Natural_u Minus_u Gt_u
  | modifier_comparison_Natural_Natural: modifier_comparison_rel Natural_u Natural_u Eq_u
  | modifier_comparison_Natural_Plus: modifier_comparison_rel Natural_u Plus_u Lt_u
  | modifier_comparison_Plus_Minus: modifier_comparison_rel Plus_u Minus_u Gt_u
  | modifier_comparison_Plus_Natural: modifier_comparison_rel Plus_u Natural_u Gt_u
  | modifier_comparison_Plus_Plus: modifier_comparison_rel Plus_u Plus_u Eq_u.

#[global] Hint Constructors modifier_comparison_rel: core_hint_db.

#[global] Instance modifier_comparison_lookup_rel: dictionary rel modifier_comparison := {
    lookup' := modifier_comparison_rel }.

#[global] Instance modifier_comparison_getF: getFunc modifier_comparison_rel := {
    getF' := modifier_comparison }.

Theorem modifier_comparison_rel_funct [ds_d3h8 ds_d3h9 : Modifier_u]:
  ∀ (VV VV' : Comparison_u),
  modifier_comparison_rel ds_d3h8 ds_d3h9 VV
  → (modifier_comparison_rel ds_d3h8 ds_d3h9 VV' → VV = VV').
Proof.
  destruct ds_d3h8 as [| |];
  [destruct ds_d3h9 as [| |] | destruct ds_d3h9 as [| |] | destruct ds_d3h9 as [| |]];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve modifier_comparison_rel_funct: f_rel_funct_db.

Theorem modifier_comparison_Minus_Minus_lem modifier_comparison_Minus_Minus_lem_res:
  modifier_comparison_rel Minus_u Minus_u modifier_comparison_Minus_Minus_lem_res
  ↔ modifier_comparison_Minus_Minus_lem_res == Eq_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite modifier_comparison_Minus_Minus_lem: f_rel_back.

Theorem modifier_comparison_Minus_Natural_lem modifier_comparison_Minus_Natural_lem_res:
  modifier_comparison_rel Minus_u Natural_u modifier_comparison_Minus_Natural_lem_res
  ↔ modifier_comparison_Minus_Natural_lem_res == Lt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite modifier_comparison_Minus_Natural_lem: f_rel_back.

Theorem modifier_comparison_Minus_Plus_lem modifier_comparison_Minus_Plus_lem_res:
  modifier_comparison_rel Minus_u Plus_u modifier_comparison_Minus_Plus_lem_res
  ↔ modifier_comparison_Minus_Plus_lem_res == Lt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite modifier_comparison_Minus_Plus_lem: f_rel_back.

Theorem modifier_comparison_Natural_Minus_lem modifier_comparison_Natural_Minus_lem_res:
  modifier_comparison_rel Natural_u Minus_u modifier_comparison_Natural_Minus_lem_res
  ↔ modifier_comparison_Natural_Minus_lem_res == Gt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite modifier_comparison_Natural_Minus_lem: f_rel_back.

Theorem modifier_comparison_Natural_Natural_lem modifier_comparison_Natural_Natural_lem_res:
  modifier_comparison_rel Natural_u Natural_u modifier_comparison_Natural_Natural_lem_res
  ↔ modifier_comparison_Natural_Natural_lem_res == Eq_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite modifier_comparison_Natural_Natural_lem: f_rel_back.

Theorem modifier_comparison_Natural_Plus_lem modifier_comparison_Natural_Plus_lem_res:
  modifier_comparison_rel Natural_u Plus_u modifier_comparison_Natural_Plus_lem_res
  ↔ modifier_comparison_Natural_Plus_lem_res == Lt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite modifier_comparison_Natural_Plus_lem: f_rel_back.

Theorem modifier_comparison_Plus_Minus_lem modifier_comparison_Plus_Minus_lem_res:
  modifier_comparison_rel Plus_u Minus_u modifier_comparison_Plus_Minus_lem_res
  ↔ modifier_comparison_Plus_Minus_lem_res == Gt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite modifier_comparison_Plus_Minus_lem: f_rel_back.

Theorem modifier_comparison_Plus_Natural_lem modifier_comparison_Plus_Natural_lem_res:
  modifier_comparison_rel Plus_u Natural_u modifier_comparison_Plus_Natural_lem_res
  ↔ modifier_comparison_Plus_Natural_lem_res == Gt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite modifier_comparison_Plus_Natural_lem: f_rel_back.

Theorem modifier_comparison_Plus_Plus_lem modifier_comparison_Plus_Plus_lem_res:
  modifier_comparison_rel Plus_u Plus_u modifier_comparison_Plus_Plus_lem_res
  ↔ modifier_comparison_Plus_Plus_lem_res == Eq_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite modifier_comparison_Plus_Plus_lem: f_rel_back.

Theorem modifier_comparison_rel_ex
  (ds_d3h8 : Modifier_u)
  (ds_d3h8_p : Modifier_wf ds_d3h8 ∧ True)
  (ds_d3h9 : Modifier_u)
  (ds_d3h9_p : Modifier_wf ds_d3h9 ∧ True):
  modifier_comparison_rel
  ds_d3h8
  ds_d3h9
  ⌊ modifier_comparison (exist _ ds_d3h8 ds_d3h8_p) (exist _ ds_d3h9 ds_d3h9_p) -⌋.
Proof.
  Opaque modifier_comparison.
  existence_lemma_pre modifier_comparison;
  destruct ds_d3h8 as [| |];
  [destruct ds_d3h9 as [| |];
   [fix_notations | fix_notations | fix_notations] |
   destruct ds_d3h9 as [| |];
   [fix_notations | fix_notations | fix_notations] |
   destruct ds_d3h9 as [| |];
   [fix_notations | fix_notations | fix_notations]];
  simpl in *.
  Transparent modifier_comparison.
  all: (existence_lemma_quicksolve modifier_comparison; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve modifier_comparison_rel_ex: rel_ax_db.

#[global] Opaque modifier_comparison.

Theorem modifier_comparison__modifier_comparison_rel_rw
  (ds_d3h8 : Modifier_u)
  (ds_d3h8_p : Modifier_wf ds_d3h8 ∧ True)
  (ds_d3h9 : Modifier_u)
  (ds_d3h9_p : Modifier_wf ds_d3h9 ∧ True)
  (VV : Comparison_u):
  ⌊ modifier_comparison (exist _ ds_d3h8 ds_d3h8_p) (exist _ ds_d3h9 ds_d3h9_p) -⌋ = VV
  ↔ modifier_comparison_rel ds_d3h8 ds_d3h9 VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite modifier_comparison__modifier_comparison_rel_rw: f_rel_funct_db.

#[global] Hint Resolve modifier_comparison__modifier_comparison_rel_rw: rel_ax_db.

#[global] Instance modifier_comparison_lookup_rw: dictionary rwLem modifier_comparison := {
    lookup' := modifier_comparison__modifier_comparison_rel_rw }.

Theorem modifier_comparison__modifier_comparison_rel
  (ds_d3h8 ds_d3h9 : Modifier) (VV : Comparison_u):
  ⌊ modifier_comparison ds_d3h8 ds_d3h9 -⌋ = VV ↔ modifier_comparison_rel ⌊ ds_d3h8 ⌋ ⌊ ds_d3h9 ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite modifier_comparison__modifier_comparison_rel: f_rel_funct_db.

Theorem modifier_comparison__modifier_comparison_rel'
  (ds_d3h8_u ds_d3h9_u : Modifier_u) (ds_d3h8 ds_d3h9 : Modifier) (VV : Comparison_u):
  ds_d3h8_u = ⌊ ds_d3h8 ⌋
  → (ds_d3h9_u = ⌊ ds_d3h9 ⌋
     → ⌊ modifier_comparison ds_d3h8 ds_d3h9 -⌋ = VV ↔ modifier_comparison_rel ds_d3h8_u ds_d3h9_u VV).
Proof.
  intros -> ->. refine (modifier_comparison__modifier_comparison_rel ds_d3h8 ds_d3h9 VV).
Qed.

#[global] Hint Resolve modifier_comparison__modifier_comparison_rel': f_rel_funct_db.

Theorem modifier_comparison_rel_mk
  (ds_d3h8 : Modifier_u)
  (ds_d3h8_p : Modifier_wf ds_d3h8 ∧ True)
  (ds_d3h9 : Modifier_u)
  (ds_d3h9_p : Modifier_wf ds_d3h9 ∧ True):
  {VV: _ | modifier_comparison_rel ds_d3h8 ds_d3h9 VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, modifier_comparison_rel ds_d3h8 ds_d3h9 VV)
          (modifier_comparison (exist _ ds_d3h8 ds_d3h8_p) (exist _ ds_d3h9 ds_d3h9_p))
          _);
  rewrite <- modifier_comparison__modifier_comparison_rel';
  quicksolve.
Qed.

#[global] Hint Resolve modifier_comparison_rel_mk: f_rel_funct_db.

#[global] Instance modifier_comparison_pack:
  @Pack
  (Modifier ::RT λ (ds_d3h8 : Modifier), Modifier ::RT λ (ds_d3h9 : Modifier), nilRT)
  (Modifier_u ::UT (Modifier_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((Modifier
  ::RT λ (ds_d3h8 : Modifier),
       Modifier ::RT λ (ds_d3h9 : Modifier), nilRT)) ((Modifier_u ::UT (Modifier_u ::UT nilUT))))
  Comparison_u
  (λ (x_26503466 : ArgList (Modifier
                            ::RT λ (ds_d3h8 : Modifier), Modifier ::RT λ (ds_d3h9 : Modifier), nilRT))
     (v_x_26503466 : Comparison_u),
   ltac:(flattenP (λ (ds_d3h8 ds_d3h9 : Modifier) (VV : Comparison_u),
 Comparison_wf VV ∧ True) x_26503466 v_x_26503466)).
Proof.
  buildPackG modifier_comparison modifier_comparison_rel modifier_comparison__modifier_comparison_rel modifier_comparison_rel_funct.
Defined.

#[global] Instance modifier_comparison_upack:
  @uPack (Modifier_u ::UT (Modifier_u ::UT nilUT)) Comparison_u.
Proof.
  buildUPackG modifier_comparison_rel modifier_comparison_rel_funct.
Defined.

Inductive Color_u: Type :=
  | Black_u: Color_u | Primary_u: RGB_u → Color_u | White_u: Color_u.

Fixpoint Color_eq (x y : Color_u): bool :=
  match (x, y) with
  | (Black_u, Black_u) => true
  | (Primary_u VV, Primary_u VV') => true && (VV ==? VV')
  | (White_u, White_u) => true
  | (_, _) => false
  end.

Theorem Color_eq_refl : ∀ (x : Color_u), is_true (Color_eq x x).
Proof.
  eq_refl_rec.
Qed.

#[global] Hint Resolve Color_eq_refl: eq_hint_db.

Theorem Color_eqb_eq : ∀ (s t : Color_u), is_true (Color_eq s t) → s = t.
Proof.
  eqb_eq_lem.
Qed.

#[global] Hint Resolve Color_eqb_eq: eq_hint_db.

#[global] Instance leibnitz_eq_Color: LeibnitzEqB := {
    equalB' := Color_eq;
    refl' := Color_eq_refl;
    eqb_eq' := Color_eqb_eq }.

Fixpoint Color_wf (x : Color_u): Prop :=
  match x with | Black_u => True | Primary_u VV => RGB_wf VV ∧ True | White_u => True end.

Theorem Color_wf_ref [p : Color_u → Prop] (tm : {v: Color_u | Color_wf v ∧ p v}): Color_wf ⌊ tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation Color := {x: Color_u | Color_wf x ∧ True}.

Definition Black_lem : Color_wf Black_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Black : Color :=
  exist _ Black_u Black_lem.

Definition Primary_lem (VV : RGB): Color_wf (Primary_u ⌊ VV ⌋) ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Primary (VV : RGB): Color :=
  exist _ (Primary_u ⌊ VV ⌋) (Primary_lem VV).

Definition White_lem : Color_wf White_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition White : Color :=
  exist _ White_u White_lem.

Definition wf_Primary_VV [VV : RGB_u] (p : Color_wf (Primary_u VV)): RGB_wf VV.
Proof.
  quicksolve.
Defined.

#[global] Hint Resolve wf_Primary_VV: ref_constr_db.

#[global] Hint Resolve Color_wf_ref: wf_constr_db.

#[global] Hint Unfold Color_wf: wf_constr_db.

#[global] Hint Resolve Color_eq: ref_constr_db.

#[global] Hint Unfold Black: ref_constr_db.

#[global] Hint Unfold Primary: ref_constr_db.

#[global] Hint Unfold White: ref_constr_db.

Definition isred_spec (ds_d3iw : Color): Type :=
  SFBool.

#[global] Hint Unfold isred_spec: lia_unfold.

Definition isred (ds_d3iw : Color): isred_spec ds_d3iw.
Proof.
  destruct ds_d3iw as [ds_d3iw ds_d3iw_p].
  destruct ds_d3iw as [| ds_d3ix|].
  - refine SFFalse.
  - destruct ds_d3ix as [| |].
    + refine SFFalse.
    + refine SFFalse.
    + refine SFTrue.
  - refine SFFalse.
Defined.

Definition monochrome_spec (ds_d3iC : Color): Type :=
  SFBool.

#[global] Hint Unfold monochrome_spec: lia_unfold.

Definition monochrome (ds_d3iC : Color): monochrome_spec ds_d3iC.
Proof.
  destruct ds_d3iC as [ds_d3iC ds_d3iC_p].
  destruct ds_d3iC as [| p|].
  - refine SFTrue.
  - refine SFFalse.
  - refine SFTrue.
Defined.

Inductive monochrome_rel: Color_u → SFBool_u → Prop :=
  | monochrome_Black: monochrome_rel Black_u SFTrue_u
  | monochrome_Primary: ∀ p, monochrome_rel (Primary_u p) SFFalse_u
  | monochrome_White: monochrome_rel White_u SFTrue_u.

#[global] Hint Constructors monochrome_rel: core_hint_db.

#[global] Instance monochrome_lookup_rel: dictionary rel monochrome := {
    lookup' := monochrome_rel }.

#[global] Instance monochrome_getF: getFunc monochrome_rel := { getF' := monochrome }.

Theorem monochrome_rel_funct [ds_d3iC : Color_u]:
  ∀ (VV VV' : SFBool_u), monochrome_rel ds_d3iC VV → (monochrome_rel ds_d3iC VV' → VV = VV').
Proof.
  destruct ds_d3iC as [| p|]; rel_functionhood_body.
Qed.

#[global] Hint Resolve monochrome_rel_funct: f_rel_funct_db.

Theorem monochrome_Black_lem monochrome_Black_lem_res:
  monochrome_rel Black_u monochrome_Black_lem_res ↔ monochrome_Black_lem_res == SFTrue_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite monochrome_Black_lem: f_rel_back.

Theorem monochrome_Primary_lem p monochrome_Primary_lem_res:
  monochrome_rel (Primary_u p) monochrome_Primary_lem_res ↔ monochrome_Primary_lem_res == SFFalse_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite monochrome_Primary_lem: f_rel_back.

Theorem monochrome_White_lem monochrome_White_lem_res:
  monochrome_rel White_u monochrome_White_lem_res ↔ monochrome_White_lem_res == SFTrue_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite monochrome_White_lem: f_rel_back.

Theorem monochrome_rel_ex (ds_d3iC : Color_u) (ds_d3iC_p : Color_wf ds_d3iC ∧ True):
  monochrome_rel ds_d3iC ⌊ monochrome (exist _ ds_d3iC ds_d3iC_p) -⌋.
Proof.
  Opaque monochrome.
  existence_lemma_pre monochrome;
  destruct ds_d3iC as [| p|];
  [fix_notations | fix_notations | fix_notations];
  simpl in *.
  Transparent monochrome.
  all: (existence_lemma_quicksolve monochrome; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve monochrome_rel_ex: rel_ax_db.

#[global] Opaque monochrome.

Theorem monochrome__monochrome_rel_rw
  (ds_d3iC : Color_u) (ds_d3iC_p : Color_wf ds_d3iC ∧ True) (VV : SFBool_u):
  ⌊ monochrome (exist _ ds_d3iC ds_d3iC_p) -⌋ = VV ↔ monochrome_rel ds_d3iC VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite monochrome__monochrome_rel_rw: f_rel_funct_db.

#[global] Hint Resolve monochrome__monochrome_rel_rw: rel_ax_db.

#[global] Instance monochrome_lookup_rw: dictionary rwLem monochrome := {
    lookup' := monochrome__monochrome_rel_rw }.

Theorem monochrome__monochrome_rel (ds_d3iC : Color) (VV : SFBool_u):
  ⌊ monochrome ds_d3iC -⌋ = VV ↔ monochrome_rel ⌊ ds_d3iC ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite monochrome__monochrome_rel: f_rel_funct_db.

Theorem monochrome__monochrome_rel' (ds_d3iC_u : Color_u) (ds_d3iC : Color) (VV : SFBool_u):
  ds_d3iC_u = ⌊ ds_d3iC ⌋ → ⌊ monochrome ds_d3iC -⌋ = VV ↔ monochrome_rel ds_d3iC_u VV.
Proof.
  intros ->. refine (monochrome__monochrome_rel ds_d3iC VV).
Qed.

#[global] Hint Resolve monochrome__monochrome_rel': f_rel_funct_db.

Theorem monochrome_rel_mk (ds_d3iC : Color_u) (ds_d3iC_p : Color_wf ds_d3iC ∧ True):
  {VV: _ | monochrome_rel ds_d3iC VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, monochrome_rel ds_d3iC VV)
          (monochrome (exist _ ds_d3iC ds_d3iC_p))
          _);
  rewrite <- monochrome__monochrome_rel';
  quicksolve.
Qed.

#[global] Hint Resolve monochrome_rel_mk: f_rel_funct_db.

#[global] Instance monochrome_pack:
  @Pack
  (Color ::RT λ (ds_d3iC : Color), nilRT)
  (Color_u ::UT nilUT)
  ltac:(mkProjectsArgListTG ((Color ::RT λ (ds_d3iC : Color), nilRT)) ((Color_u ::UT nilUT)))
  SFBool_u
  (λ (x_18669380 : ArgList (Color ::RT λ (ds_d3iC : Color), nilRT)) (v_x_18669380 : SFBool_u),
   ltac:(flattenP (λ (ds_d3iC : Color) (VV : SFBool_u), SFBool_wf VV ∧ True) x_18669380 v_x_18669380)).
Proof.
  buildPackG monochrome monochrome_rel monochrome__monochrome_rel monochrome_rel_funct.
Defined.

#[global] Instance monochrome_upack: @uPack (Color_u ::UT nilUT) SFBool_u.
Proof.
  buildUPackG monochrome_rel monochrome_rel_funct.
Defined.
