From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Set Universe Polymorphism. 
From Coq Require Import Unicode.Utf8.

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

Definition lowerLetter_spec (ds_d153 : Letter): Type :=
  Letter.

#[global] Hint Unfold lowerLetter_spec: lia_unfold.

Definition lowerLetter (ds_d153 : Letter): lowerLetter_spec ds_d153.
Proof.
  destruct ds_d153 as [ds_d153 ds_d153_p].
  destruct ds_d153 as [| | | |].
  - refine B.
  - refine C.
  - refine D.
  - refine F.
  - refine F.
Defined.

Inductive lowerLetter_rel: Letter_u → Letter_u → Prop :=
  | lowerLetter_A: lowerLetter_rel A_u B_u
  | lowerLetter_B: lowerLetter_rel B_u C_u
  | lowerLetter_C: lowerLetter_rel C_u D_u
  | lowerLetter_D: lowerLetter_rel D_u F_u
  | lowerLetter_F: lowerLetter_rel F_u F_u.

#[global] Hint Constructors lowerLetter_rel: core_hint_db.

#[global] Instance lowerLetter_lookup_rel: dictionary rel lowerLetter := {
    lookup' := lowerLetter_rel }.

#[global] Instance lowerLetter_getF: getFunc lowerLetter_rel := { getF' := lowerLetter }.

Theorem lowerLetter_rel_funct [ds_d153 : Letter_u]:
  ∀ (VV VV' : Letter_u), lowerLetter_rel ds_d153 VV → (lowerLetter_rel ds_d153 VV' → VV = VV').
Proof.
  destruct ds_d153 as [| | | |]; rel_functionhood_body.
Qed.

#[global] Hint Resolve lowerLetter_rel_funct: f_rel_funct_db.

Theorem lowerLetter_A_lem lowerLetter_A_lem_res:
  lowerLetter_rel A_u lowerLetter_A_lem_res ↔ lowerLetter_A_lem_res == B_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite lowerLetter_A_lem: f_rel_back.

Theorem lowerLetter_B_lem lowerLetter_B_lem_res:
  lowerLetter_rel B_u lowerLetter_B_lem_res ↔ lowerLetter_B_lem_res == C_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite lowerLetter_B_lem: f_rel_back.

Theorem lowerLetter_C_lem lowerLetter_C_lem_res:
  lowerLetter_rel C_u lowerLetter_C_lem_res ↔ lowerLetter_C_lem_res == D_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite lowerLetter_C_lem: f_rel_back.

Theorem lowerLetter_D_lem lowerLetter_D_lem_res:
  lowerLetter_rel D_u lowerLetter_D_lem_res ↔ lowerLetter_D_lem_res == F_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite lowerLetter_D_lem: f_rel_back.

Theorem lowerLetter_F_lem lowerLetter_F_lem_res:
  lowerLetter_rel F_u lowerLetter_F_lem_res ↔ lowerLetter_F_lem_res == F_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite lowerLetter_F_lem: f_rel_back.

Theorem lowerLetter_rel_ex (ds_d153 : Letter_u) (ds_d153_p : Letter_wf ds_d153 ∧ True):
  lowerLetter_rel ds_d153 ⌊ lowerLetter (exist _ ds_d153 ds_d153_p) -⌋.
Proof.
  Opaque lowerLetter.
  existence_lemma_pre lowerLetter;
  destruct ds_d153 as [| | | |];
  [fix_notations | fix_notations | fix_notations | fix_notations | fix_notations];
  simpl in *.
  Transparent lowerLetter.
  all: (existence_lemma_quicksolve lowerLetter; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve lowerLetter_rel_ex: rel_ax_db.

#[global] Opaque lowerLetter.

Theorem lowerLetter__lowerLetter_rel_rw
  (ds_d153 : Letter_u) (ds_d153_p : Letter_wf ds_d153 ∧ True) (VV : Letter_u):
  ⌊ lowerLetter (exist _ ds_d153 ds_d153_p) -⌋ = VV ↔ lowerLetter_rel ds_d153 VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite lowerLetter__lowerLetter_rel_rw: f_rel_funct_db.

#[global] Hint Resolve lowerLetter__lowerLetter_rel_rw: rel_ax_db.

#[global] Instance lowerLetter_lookup_rw: dictionary rwLem lowerLetter := {
    lookup' := lowerLetter__lowerLetter_rel_rw }.

Theorem lowerLetter__lowerLetter_rel (ds_d153 : Letter) (VV : Letter_u):
  ⌊ lowerLetter ds_d153 -⌋ = VV ↔ lowerLetter_rel ⌊ ds_d153 ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite lowerLetter__lowerLetter_rel: f_rel_funct_db.

Theorem lowerLetter__lowerLetter_rel' (ds_d153_u : Letter_u) (ds_d153 : Letter) (VV : Letter_u):
  ds_d153_u = ⌊ ds_d153 ⌋ → ⌊ lowerLetter ds_d153 -⌋ = VV ↔ lowerLetter_rel ds_d153_u VV.
Proof.
  intros ->. refine (lowerLetter__lowerLetter_rel ds_d153 VV).
Qed.

#[global] Hint Resolve lowerLetter__lowerLetter_rel': f_rel_funct_db.

Theorem lowerLetter_rel_mk (ds_d153 : Letter_u) (ds_d153_p : Letter_wf ds_d153 ∧ True):
  {VV: _ | lowerLetter_rel ds_d153 VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, lowerLetter_rel ds_d153 VV)
          (lowerLetter (exist _ ds_d153 ds_d153_p))
          _);
  rewrite <- lowerLetter__lowerLetter_rel';
  quicksolve.
Qed.

#[global] Hint Resolve lowerLetter_rel_mk: f_rel_funct_db.

#[global] Instance lowerLetter_pack:
  @Pack
  (Letter ::RT λ (ds_d153 : Letter), nilRT)
  (Letter_u ::UT nilUT)
  ltac:(mkProjectsArgListTG ((Letter ::RT λ (ds_d153 : Letter), nilRT)) ((Letter_u ::UT nilUT)))
  Letter_u
  (λ (x_90789449 : ArgList (Letter ::RT λ (ds_d153 : Letter), nilRT)) (v_x_90789449 : Letter_u),
   ltac:(flattenP (λ (ds_d153 : Letter) (VV : Letter_u), Letter_wf VV ∧ True) x_90789449 v_x_90789449)).
Proof.
  buildPackG lowerLetter lowerLetter_rel lowerLetter__lowerLetter_rel lowerLetter_rel_funct.
Defined.

#[global] Instance lowerLetter_upack: @uPack (Letter_u ::UT nilUT) Letter_u.
Proof.
  buildUPackG lowerLetter_rel lowerLetter_rel_funct.
Defined.

Definition lowerLetterFIsF_spec : Type :=
  {{∃ (lowerLetter_res : Letter_u), lowerLetter_rel F_u lowerLetter_res ∧ lowerLetter_res == F_u}}.

#[global] Hint Unfold lowerLetterFIsF_spec: lia_unfold.

Theorem lowerLetterFIsF : lowerLetterFIsF_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (lowerLetter_res : Letter_u), lowerLetter_rel F_u lowerLetter_res ∧ lowerLetter_res == F_u)
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

Definition lowerGrade_spec (ds_d154 : Grades): Type :=
  Grades.

#[global] Hint Unfold lowerGrade_spec: lia_unfold.

Definition lowerGrade (ds_d154 : Grades): lowerGrade_spec ds_d154.
Proof.
  destruct ds_d154 as [ds_d154 ds_d154_p].
  destruct ds_d154 as [l m].
  - destruct m as [| |].
    + destruct l as [| | | |].
      ** refine (Grade (lowerLetter A) Plus).
      ** refine (Grade (lowerLetter B) Plus).
      ** refine (Grade (lowerLetter C) Plus).
      ** refine (Grade (lowerLetter D) Plus).
      ** refine (Grade F Minus).
    + refine (Grade (exist (λ (VV : Letter_u), Letter_wf VV ∧ True) l ltac:(solver)) Minus).
    + refine (Grade (exist (λ (VV : Letter_u), Letter_wf VV ∧ True) l ltac:(solver)) Natural).
Defined.

Inductive lowerGrade_rel: Grades_u → Grades_u → Prop :=
  | lowerGrade__Grade_A_Minus: ∀ (lowerLetter_res : Letter_u),
                               lowerLetter_rel A_u lowerLetter_res
                               → lowerGrade_rel (Grade_u A_u Minus_u) (Grade_u lowerLetter_res Plus_u)
  | lowerGrade__Grade_B_Minus: ∀ (lowerLetter_res : Letter_u),
                               lowerLetter_rel B_u lowerLetter_res
                               → lowerGrade_rel (Grade_u B_u Minus_u) (Grade_u lowerLetter_res Plus_u)
  | lowerGrade__Grade_C_Minus: ∀ (lowerLetter_res : Letter_u),
                               lowerLetter_rel C_u lowerLetter_res
                               → lowerGrade_rel (Grade_u C_u Minus_u) (Grade_u lowerLetter_res Plus_u)
  | lowerGrade__Grade_D_Minus: ∀ (lowerLetter_res : Letter_u),
                               lowerLetter_rel D_u lowerLetter_res
                               → lowerGrade_rel (Grade_u D_u Minus_u) (Grade_u lowerLetter_res Plus_u)
  | lowerGrade__Grade_F_Minus: lowerGrade_rel (Grade_u F_u Minus_u) (Grade_u F_u Minus_u)
  | lowerGrade__Grade_x_Natural: ∀ l, lowerGrade_rel (Grade_u l Natural_u) (Grade_u l Minus_u)
  | lowerGrade__Grade_x_Plus: ∀ l, lowerGrade_rel (Grade_u l Plus_u) (Grade_u l Natural_u).

#[global] Hint Constructors lowerGrade_rel: core_hint_db.

#[global] Instance lowerGrade_lookup_rel: dictionary rel lowerGrade := {
    lookup' := lowerGrade_rel }.

#[global] Instance lowerGrade_getF: getFunc lowerGrade_rel := { getF' := lowerGrade }.

Theorem lowerGrade_rel_funct [ds_d154 : Grades_u]:
  ∀ (VV VV' : Grades_u), lowerGrade_rel ds_d154 VV → (lowerGrade_rel ds_d154 VV' → VV = VV').
Proof.
  destruct ds_d154 as [l m];
  [destruct m as [| |];
   [destruct l as [| | | |] |  |]];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve lowerGrade_rel_funct: f_rel_funct_db.

Theorem lowerGrade__Grade_A_Minus_lem lowerGrade__Grade_A_Minus_lem_res:
  lowerGrade_rel (Grade_u A_u Minus_u) lowerGrade__Grade_A_Minus_lem_res
  ↔ ∃ (lowerLetter_res : Letter_u),
    lowerLetter_rel A_u lowerLetter_res
    ∧ lowerGrade__Grade_A_Minus_lem_res == Grade_u lowerLetter_res Plus_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite lowerGrade__Grade_A_Minus_lem: f_rel_back.

Theorem lowerGrade__Grade_B_Minus_lem lowerGrade__Grade_B_Minus_lem_res:
  lowerGrade_rel (Grade_u B_u Minus_u) lowerGrade__Grade_B_Minus_lem_res
  ↔ ∃ (lowerLetter_res : Letter_u),
    lowerLetter_rel B_u lowerLetter_res
    ∧ lowerGrade__Grade_B_Minus_lem_res == Grade_u lowerLetter_res Plus_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite lowerGrade__Grade_B_Minus_lem: f_rel_back.

Theorem lowerGrade__Grade_C_Minus_lem lowerGrade__Grade_C_Minus_lem_res:
  lowerGrade_rel (Grade_u C_u Minus_u) lowerGrade__Grade_C_Minus_lem_res
  ↔ ∃ (lowerLetter_res : Letter_u),
    lowerLetter_rel C_u lowerLetter_res
    ∧ lowerGrade__Grade_C_Minus_lem_res == Grade_u lowerLetter_res Plus_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite lowerGrade__Grade_C_Minus_lem: f_rel_back.

Theorem lowerGrade__Grade_D_Minus_lem lowerGrade__Grade_D_Minus_lem_res:
  lowerGrade_rel (Grade_u D_u Minus_u) lowerGrade__Grade_D_Minus_lem_res
  ↔ ∃ (lowerLetter_res : Letter_u),
    lowerLetter_rel D_u lowerLetter_res
    ∧ lowerGrade__Grade_D_Minus_lem_res == Grade_u lowerLetter_res Plus_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite lowerGrade__Grade_D_Minus_lem: f_rel_back.

Theorem lowerGrade__Grade_F_Minus_lem lowerGrade__Grade_F_Minus_lem_res:
  lowerGrade_rel (Grade_u F_u Minus_u) lowerGrade__Grade_F_Minus_lem_res
  ↔ lowerGrade__Grade_F_Minus_lem_res == Grade_u F_u Minus_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite lowerGrade__Grade_F_Minus_lem: f_rel_back.

Theorem lowerGrade__Grade_x_Natural_lem l lowerGrade__Grade_x_Natural_lem_res:
  lowerGrade_rel (Grade_u l Natural_u) lowerGrade__Grade_x_Natural_lem_res
  ↔ lowerGrade__Grade_x_Natural_lem_res == Grade_u l Minus_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite lowerGrade__Grade_x_Natural_lem: f_rel_back.

Theorem lowerGrade__Grade_x_Plus_lem l lowerGrade__Grade_x_Plus_lem_res:
  lowerGrade_rel (Grade_u l Plus_u) lowerGrade__Grade_x_Plus_lem_res
  ↔ lowerGrade__Grade_x_Plus_lem_res == Grade_u l Natural_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite lowerGrade__Grade_x_Plus_lem: f_rel_back.

Theorem lowerGrade_rel_ex (ds_d154 : Grades_u) (ds_d154_p : Grades_wf ds_d154 ∧ True):
  lowerGrade_rel ds_d154 ⌊ lowerGrade (exist _ ds_d154 ds_d154_p) -⌋.
Proof.
  Opaque lowerGrade.
  existence_lemma_pre lowerGrade;
  destruct ds_d154 as [l m];
  [destruct m as [| |];
   [destruct l as [| | | |];
    [fix_notations | fix_notations | fix_notations | fix_notations | fix_notations] |
    fix_notations |
    fix_notations]];
  simpl in *.
  Transparent lowerGrade.
  all: (existence_lemma_quicksolve lowerGrade; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve lowerGrade_rel_ex: rel_ax_db.

#[global] Opaque lowerGrade.

Theorem lowerGrade__lowerGrade_rel_rw
  (ds_d154 : Grades_u) (ds_d154_p : Grades_wf ds_d154 ∧ True) (VV : Grades_u):
  ⌊ lowerGrade (exist _ ds_d154 ds_d154_p) -⌋ = VV ↔ lowerGrade_rel ds_d154 VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite lowerGrade__lowerGrade_rel_rw: f_rel_funct_db.

#[global] Hint Resolve lowerGrade__lowerGrade_rel_rw: rel_ax_db.

#[global] Instance lowerGrade_lookup_rw: dictionary rwLem lowerGrade := {
    lookup' := lowerGrade__lowerGrade_rel_rw }.

Theorem lowerGrade__lowerGrade_rel (ds_d154 : Grades) (VV : Grades_u):
  ⌊ lowerGrade ds_d154 -⌋ = VV ↔ lowerGrade_rel ⌊ ds_d154 ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite lowerGrade__lowerGrade_rel: f_rel_funct_db.

Theorem lowerGrade__lowerGrade_rel' (ds_d154_u : Grades_u) (ds_d154 : Grades) (VV : Grades_u):
  ds_d154_u = ⌊ ds_d154 ⌋ → ⌊ lowerGrade ds_d154 -⌋ = VV ↔ lowerGrade_rel ds_d154_u VV.
Proof.
  intros ->. refine (lowerGrade__lowerGrade_rel ds_d154 VV).
Qed.

#[global] Hint Resolve lowerGrade__lowerGrade_rel': f_rel_funct_db.

Theorem lowerGrade_rel_mk (ds_d154 : Grades_u) (ds_d154_p : Grades_wf ds_d154 ∧ True):
  {VV: _ | lowerGrade_rel ds_d154 VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, lowerGrade_rel ds_d154 VV)
          (lowerGrade (exist _ ds_d154 ds_d154_p))
          _);
  rewrite <- lowerGrade__lowerGrade_rel';
  quicksolve.
Qed.

#[global] Hint Resolve lowerGrade_rel_mk: f_rel_funct_db.

#[global] Instance lowerGrade_pack:
  @Pack
  (Grades ::RT λ (ds_d154 : Grades), nilRT)
  (Grades_u ::UT nilUT)
  ltac:(mkProjectsArgListTG ((Grades ::RT λ (ds_d154 : Grades), nilRT)) ((Grades_u ::UT nilUT)))
  Grades_u
  (λ (x_65119381 : ArgList (Grades ::RT λ (ds_d154 : Grades), nilRT)) (v_x_65119381 : Grades_u),
   ltac:(flattenP (λ (ds_d154 : Grades) (VV : Grades_u), Grades_wf VV ∧ True) x_65119381 v_x_65119381)).
Proof.
  buildPackG lowerGrade lowerGrade_rel lowerGrade__lowerGrade_rel lowerGrade_rel_funct.
Defined.

#[global] Instance lowerGrade_upack: @uPack (Grades_u ::UT nilUT) Grades_u.
Proof.
  buildUPackG lowerGrade_rel lowerGrade_rel_funct.
Defined.

Definition applyLatePolicy_spec (lateDays : {lateDays: Z | True}) (g : Grades): Type :=
  Grades.

#[global] Hint Unfold applyLatePolicy_spec: lia_unfold.

Definition applyLatePolicy (lateDays : {lateDays: Z | True}) (g : Grades):
  applyLatePolicy_spec lateDays g.
Proof.
  destruct lateDays as [lateDays lateDays_p].
  destruct g as [g g_p].
  let E := fresh "E" in destruct (lateDays <? 9) as [|] eqn:E;
  [refine (exist (λ (g : Grades_u), Grades_wf g ∧ True) g ltac:(solver)) |
   let E := fresh "E" in destruct (lateDays <? 17) as [|] eqn:E;
   [refine (lowerGrade (exist (λ (g : Grades_u), Grades_wf g ∧ True) g ltac:(solver))) |
    let E := fresh "E" in destruct (lateDays <? 21) as [|] eqn:E;
    [refine (lowerGrade (lowerGrade (exist (λ (g : Grades_u), Grades_wf g ∧ True) g ltac:(solver)))) |
     refine (lowerGrade
             (lowerGrade (lowerGrade (exist (λ (g : Grades_u), Grades_wf g ∧ True) g ltac:(solver)))))]]].
Defined.

Inductive applyLatePolicy_rel: Z → Grades_u → Grades_u → Prop :=
  | applyLatePolicy_x_x_True: ∀ lateDays g, (lateDays <? 9) == true → applyLatePolicy_rel lateDays g g
  | applyLatePolicy_x_x_False_True: ∀ lateDays g,
                                    (lateDays <? 9) == false
                                    → ((lateDays <? 17) == true
                                       → ∀ (lowerGrade_res : Grades_u),
                                         lowerGrade_rel g lowerGrade_res
                                         → applyLatePolicy_rel lateDays g lowerGrade_res)
  | applyLatePolicy_x_x_False_False_True: ∀ lateDays g,
                                          (lateDays <? 9) == false
                                          → ((lateDays <? 17) == false
                                             → ((lateDays <? 21) == true
                                                → ∀ (lowerGrade_res : Grades_u),
                                                  lowerGrade_rel g lowerGrade_res
                                                  → ∀ (lowerGrade_res_2 : Grades_u),
                                                    lowerGrade_rel lowerGrade_res lowerGrade_res_2
                                                    → applyLatePolicy_rel lateDays g lowerGrade_res_2))
  | applyLatePolicy_x_x_False_False_False: ∀ lateDays g,
                                           (lateDays <? 9) == false
                                           → ((lateDays <? 17) == false
                                              → ((lateDays <? 21) == false
                                                 → ∀ (lowerGrade_res : Grades_u),
                                                   lowerGrade_rel g lowerGrade_res
                                                   → ∀ (lowerGrade_res_2 : Grades_u),
                                                     lowerGrade_rel lowerGrade_res lowerGrade_res_2
                                                     → ∀ (lowerGrade_res_3 : Grades_u),
                                                       lowerGrade_rel lowerGrade_res_2 lowerGrade_res_3
                                                       → applyLatePolicy_rel lateDays g lowerGrade_res_3)).

#[global] Hint Constructors applyLatePolicy_rel: core_hint_db.

#[global] Instance applyLatePolicy_lookup_rel: dictionary rel applyLatePolicy := {
    lookup' := applyLatePolicy_rel }.

#[global] Instance applyLatePolicy_getF: getFunc applyLatePolicy_rel := {
    getF' := applyLatePolicy }.

Theorem applyLatePolicy_rel_funct [lateDays : Z] [g : Grades_u]:
  ∀ (VV VV' : Grades_u),
  applyLatePolicy_rel lateDays g VV → (applyLatePolicy_rel lateDays g VV' → VV = VV').
Proof.
  let E := fresh "E" in destruct (lateDays <? 9) as [|] eqn:E;
  [ |
   let E := fresh "E" in destruct (lateDays <? 17) as [|] eqn:E;
   [ | let E := fresh "E" in destruct (lateDays <? 21) as [|] eqn:E]];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve applyLatePolicy_rel_funct: f_rel_funct_db.

Theorem applyLatePolicy_inv_lem g lateDays applyLatePolicy_inv_lem_res:
  applyLatePolicy_rel lateDays g applyLatePolicy_inv_lem_res
  ↔ (((lateDays <? 9) == true ∧ applyLatePolicy_inv_lem_res == g
      ∨ (lateDays <? 9) == false
        ∧ ((lateDays <? 17) == true
           ∧ ∃ (lowerGrade_res : Grades_u),
             lowerGrade_rel g lowerGrade_res ∧ applyLatePolicy_inv_lem_res == lowerGrade_res))
     ∨ (lateDays <? 9) == false
       ∧ ((lateDays <? 17) == false
          ∧ ((lateDays <? 21) == true
             ∧ ∃ (lowerGrade_res : Grades_u),
               lowerGrade_rel g lowerGrade_res
               ∧ ∃ (lowerGrade_res_2 : Grades_u),
                 lowerGrade_rel lowerGrade_res lowerGrade_res_2 ∧ applyLatePolicy_inv_lem_res == lowerGrade_res_2)))
    ∨ (lateDays <? 9) == false
      ∧ ((lateDays <? 17) == false
         ∧ ((lateDays <? 21) == false
            ∧ ∃ (lowerGrade_res : Grades_u),
              lowerGrade_rel g lowerGrade_res
              ∧ ∃ (lowerGrade_res_2 : Grades_u),
                lowerGrade_rel lowerGrade_res lowerGrade_res_2
                ∧ ∃ (lowerGrade_res_3 : Grades_u),
                  lowerGrade_rel lowerGrade_res_2 lowerGrade_res_3
                  ∧ applyLatePolicy_inv_lem_res == lowerGrade_res_3)).
Proof.
  rel_back' ((lateDays <? 9) _::_
           (lateDays <? 17) _::_
           (lateDays <? 21) _::_ _nil).
Qed.

#[global] Hint Rewrite applyLatePolicy_inv_lem: f_rel_back.

Theorem applyLatePolicy_rel_ex
  (lateDays : Z) (lateDays_p : True) (g : Grades_u) (g_p : Grades_wf g ∧ True):
  applyLatePolicy_rel lateDays g ⌊ applyLatePolicy (exist _ lateDays lateDays_p) (exist _ g g_p) -⌋.
Proof.
  Opaque applyLatePolicy.
  existence_lemma_pre applyLatePolicy;
  let E := fresh "E" in destruct (lateDays <? 9) as [|] eqn:E;
  [fix_notations |
   let E := fresh "E" in destruct (lateDays <? 17) as [|] eqn:E;
   [fix_notations |
    let E := fresh "E" in destruct (lateDays <? 21) as [|] eqn:E;
    [fix_notations | fix_notations]]];
  simpl in *.
  Transparent applyLatePolicy.
  all: (existence_lemma_quicksolve applyLatePolicy; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve applyLatePolicy_rel_ex: rel_ax_db.

#[global] Opaque applyLatePolicy.

Theorem applyLatePolicy__applyLatePolicy_rel_rw
  (lateDays : Z) (lateDays_p : True) (g : Grades_u) (g_p : Grades_wf g ∧ True) (VV : Grades_u):
  ⌊ applyLatePolicy (exist _ lateDays lateDays_p) (exist _ g g_p) -⌋ = VV
  ↔ applyLatePolicy_rel lateDays g VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite applyLatePolicy__applyLatePolicy_rel_rw: f_rel_funct_db.

#[global] Hint Resolve applyLatePolicy__applyLatePolicy_rel_rw: rel_ax_db.

#[global] Instance applyLatePolicy_lookup_rw: dictionary rwLem applyLatePolicy := {
    lookup' := applyLatePolicy__applyLatePolicy_rel_rw }.

Theorem applyLatePolicy__applyLatePolicy_rel
  (lateDays : {lateDays: Z | True}) (g : Grades) (VV : Grades_u):
  ⌊ applyLatePolicy lateDays g -⌋ = VV ↔ applyLatePolicy_rel ⌊ lateDays ⌋ ⌊ g ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite applyLatePolicy__applyLatePolicy_rel: f_rel_funct_db.

Theorem applyLatePolicy__applyLatePolicy_rel'
  (lateDays_u : Z) (g_u : Grades_u) (lateDays : {lateDays: Z | True}) (g : Grades) (VV : Grades_u):
  lateDays_u = ⌊ lateDays ⌋
  → (g_u = ⌊ g ⌋ → ⌊ applyLatePolicy lateDays g -⌋ = VV ↔ applyLatePolicy_rel lateDays_u g_u VV).
Proof.
  intros -> ->. refine (applyLatePolicy__applyLatePolicy_rel lateDays g VV).
Qed.

#[global] Hint Resolve applyLatePolicy__applyLatePolicy_rel': f_rel_funct_db.

Theorem applyLatePolicy_rel_mk
  (lateDays : Z) (lateDays_p : True) (g : Grades_u) (g_p : Grades_wf g ∧ True):
  {VV: _ | applyLatePolicy_rel lateDays g VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, applyLatePolicy_rel lateDays g VV)
          (applyLatePolicy (exist _ lateDays lateDays_p) (exist _ g g_p))
          _);
  rewrite <- applyLatePolicy__applyLatePolicy_rel';
  quicksolve.
Qed.

#[global] Hint Resolve applyLatePolicy_rel_mk: f_rel_funct_db.

#[global] Instance applyLatePolicy_pack:
  @Pack
  ({lateDays: Z | True} ::RT λ (lateDays : {lateDays: Z | True}), Grades ::RT λ (g : Grades), nilRT)
  (Z ::UT (Grades_u ::UT nilUT))
  ltac:(mkProjectsArgListTG (({lateDays: Z | True}
  ::RT λ (lateDays : {lateDays: Z | True}),
       Grades ::RT λ (g : Grades), nilRT)) ((Z ::UT (Grades_u ::UT nilUT))))
  Grades_u
  (λ (x_58156632 : ArgList ({lateDays: Z | True}
                            ::RT λ (lateDays : {lateDays: Z | True}), Grades ::RT λ (g : Grades), nilRT))
     (v_x_58156632 : Grades_u),
   ltac:(flattenP (λ (lateDays : {lateDays: Z | True}) (g : Grades) (VV : Grades_u),
 Grades_wf VV ∧ True) x_58156632 v_x_58156632)).
Proof.
  buildPackG applyLatePolicy applyLatePolicy_rel applyLatePolicy__applyLatePolicy_rel applyLatePolicy_rel_funct.
Defined.

#[global] Instance applyLatePolicy_upack: @uPack (Z ::UT (Grades_u ::UT nilUT)) Grades_u.
Proof.
  buildUPackG applyLatePolicy_rel applyLatePolicy_rel_funct.
Defined.

Definition lowerGradeFMinus_spec : Type :=
  {{∃ (lowerGrade_res : Grades_u),
    lowerGrade_rel (Grade_u F_u Minus_u) lowerGrade_res ∧ lowerGrade_res == Grade_u F_u Minus_u}}.

#[global] Hint Unfold lowerGradeFMinus_spec: lia_unfold.

Theorem lowerGradeFMinus : lowerGradeFMinus_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (lowerGrade_res : Grades_u),
           lowerGrade_rel (Grade_u F_u Minus_u) lowerGrade_res ∧ lowerGrade_res == Grade_u F_u Minus_u)
          (# unit)
          ltac:(solver)).
Qed.

Definition lowerGradeThrice_spec : Type :=
  {{∃ (lowerGrade_res : Grades_u),
    lowerGrade_rel (Grade_u B_u Minus_u) lowerGrade_res
    ∧ ∃ (lowerGrade_res_2 : Grades_u),
      lowerGrade_rel lowerGrade_res lowerGrade_res_2
      ∧ ∃ (lowerGrade_res_3 : Grades_u),
        lowerGrade_rel lowerGrade_res_2 lowerGrade_res_3 ∧ lowerGrade_res_3 == Grade_u C_u Minus_u}}.

#[global] Hint Unfold lowerGradeThrice_spec: lia_unfold.

Theorem lowerGradeThrice : lowerGradeThrice_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (lowerGrade_res : Grades_u),
           lowerGrade_rel (Grade_u B_u Minus_u) lowerGrade_res
           ∧ ∃ (lowerGrade_res_2 : Grades_u),
             lowerGrade_rel lowerGrade_res lowerGrade_res_2
             ∧ ∃ (lowerGrade_res_3 : Grades_u),
               lowerGrade_rel lowerGrade_res_2 lowerGrade_res_3 ∧ lowerGrade_res_3 == Grade_u C_u Minus_u)
          (# unit)
          ltac:(solver)).
Qed.

Definition lowerGradeTwice_spec : Type :=
  {{∃ (lowerGrade_res : Grades_u),
    lowerGrade_rel (Grade_u B_u Minus_u) lowerGrade_res
    ∧ ∃ (lowerGrade_res_2 : Grades_u),
      lowerGrade_rel lowerGrade_res lowerGrade_res_2 ∧ lowerGrade_res_2 == Grade_u C_u Natural_u}}.

#[global] Hint Unfold lowerGradeTwice_spec: lia_unfold.

Theorem lowerGradeTwice : lowerGradeTwice_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (lowerGrade_res : Grades_u),
           lowerGrade_rel (Grade_u B_u Minus_u) lowerGrade_res
           ∧ ∃ (lowerGrade_res_2 : Grades_u),
             lowerGrade_rel lowerGrade_res lowerGrade_res_2 ∧ lowerGrade_res_2 == Grade_u C_u Natural_u)
          (# unit)
          ltac:(solver)).
Qed.

Definition noPenaltyForMostlyOnTime_spec
  (lateDays : {lateDays: Z | True}) (g : Grades) (h : {{ltbZ_rel ⌊ lateDays ⌋ 9 true}}):
  Type :=
  {{∃ (applyLatePolicy_res : Grades_u),
    applyLatePolicy_rel ⌊ lateDays ⌋ ⌊ g ⌋ applyLatePolicy_res ∧ applyLatePolicy_res == ⌊ g ⌋}}.

#[global] Hint Unfold noPenaltyForMostlyOnTime_spec: lia_unfold.

Theorem noPenaltyForMostlyOnTime
  (lateDays : {lateDays: Z | True}) (g : Grades) (h : {{ltbZ_rel ⌊ lateDays ⌋ 9 true}}):
  noPenaltyForMostlyOnTime_spec lateDays g h.
Proof.
  destruct lateDays as [lateDays lateDays_p].
  destruct g as [g g_p].
  destruct h as [h h_p].
  let E := fresh "E" in destruct (lateDays <? 9) as [|] eqn:E;
  [refine (subsumptionCast
           Unit
           (λ (VV : Unit),
            ∃ (applyLatePolicy_res : Grades_u),
            applyLatePolicy_rel lateDays g applyLatePolicy_res ∧ applyLatePolicy_res == g)
           (# unit)
           ltac:(solver)) |
   refine (subsumptionCast
           Unit
           (λ (VV : Unit),
            ∃ (applyLatePolicy_res : Grades_u),
            applyLatePolicy_rel lateDays g applyLatePolicy_res ∧ applyLatePolicy_res == g)
           (exist (λ (h : Unit), ltbZ_rel lateDays 9 true) h ltac:(solver))
           ltac:(solver))].
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

Definition letterComparison_spec (ds_d15A ds_d15B : Letter): Type :=
  Comparison.

#[global] Hint Unfold letterComparison_spec: lia_unfold.

Definition letterComparison (ds_d15A ds_d15B : Letter): letterComparison_spec ds_d15A ds_d15B.
Proof.
  destruct ds_d15A as [ds_d15A ds_d15A_p].
  destruct ds_d15B as [ds_d15B ds_d15B_p].
  destruct ds_d15A as [| | | |].
  - destruct ds_d15B as [| | | |].
    + refine Eq.
    + refine Gt.
    + refine Gt.
    + refine Gt.
    + refine Gt.
  - destruct ds_d15B as [| | | |].
    + refine Lt.
    + refine Eq.
    + refine Gt.
    + refine Gt.
    + refine Gt.
  - destruct ds_d15B as [| | | |].
    + refine Lt.
    + refine Lt.
    + refine Eq.
    + refine Gt.
    + refine Gt.
  - destruct ds_d15B as [| | | |].
    + refine Lt.
    + refine Lt.
    + refine Lt.
    + refine Eq.
    + refine Gt.
  - destruct ds_d15B as [| | | |].
    + refine Lt.
    + refine Lt.
    + refine Lt.
    + refine Lt.
    + refine Eq.
Defined.

Inductive letterComparison_rel: Letter_u → Letter_u → Comparison_u → Prop :=
  | letterComparison_A_A: letterComparison_rel A_u A_u Eq_u
  | letterComparison_A_B: letterComparison_rel A_u B_u Gt_u
  | letterComparison_A_C: letterComparison_rel A_u C_u Gt_u
  | letterComparison_A_D: letterComparison_rel A_u D_u Gt_u
  | letterComparison_A_F: letterComparison_rel A_u F_u Gt_u
  | letterComparison_B_A: letterComparison_rel B_u A_u Lt_u
  | letterComparison_B_B: letterComparison_rel B_u B_u Eq_u
  | letterComparison_B_C: letterComparison_rel B_u C_u Gt_u
  | letterComparison_B_D: letterComparison_rel B_u D_u Gt_u
  | letterComparison_B_F: letterComparison_rel B_u F_u Gt_u
  | letterComparison_C_A: letterComparison_rel C_u A_u Lt_u
  | letterComparison_C_B: letterComparison_rel C_u B_u Lt_u
  | letterComparison_C_C: letterComparison_rel C_u C_u Eq_u
  | letterComparison_C_D: letterComparison_rel C_u D_u Gt_u
  | letterComparison_C_F: letterComparison_rel C_u F_u Gt_u
  | letterComparison_D_A: letterComparison_rel D_u A_u Lt_u
  | letterComparison_D_B: letterComparison_rel D_u B_u Lt_u
  | letterComparison_D_C: letterComparison_rel D_u C_u Lt_u
  | letterComparison_D_D: letterComparison_rel D_u D_u Eq_u
  | letterComparison_D_F: letterComparison_rel D_u F_u Gt_u
  | letterComparison_F_A: letterComparison_rel F_u A_u Lt_u
  | letterComparison_F_B: letterComparison_rel F_u B_u Lt_u
  | letterComparison_F_C: letterComparison_rel F_u C_u Lt_u
  | letterComparison_F_D: letterComparison_rel F_u D_u Lt_u
  | letterComparison_F_F: letterComparison_rel F_u F_u Eq_u.

#[global] Hint Constructors letterComparison_rel: core_hint_db.

#[global] Instance letterComparison_lookup_rel: dictionary rel letterComparison := {
    lookup' := letterComparison_rel }.

#[global] Instance letterComparison_getF: getFunc letterComparison_rel := {
    getF' := letterComparison }.

Theorem letterComparison_rel_funct [ds_d15A ds_d15B : Letter_u]:
  ∀ (VV VV' : Comparison_u),
  letterComparison_rel ds_d15A ds_d15B VV → (letterComparison_rel ds_d15A ds_d15B VV' → VV = VV').
Proof.
  destruct ds_d15A as [| | | |];
  [destruct ds_d15B as [| | | |] |
   destruct ds_d15B as [| | | |] |
   destruct ds_d15B as [| | | |] |
   destruct ds_d15B as [| | | |] |
   destruct ds_d15B as [| | | |]];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve letterComparison_rel_funct: f_rel_funct_db.

Theorem letterComparison_A_A_lem letterComparison_A_A_lem_res:
  letterComparison_rel A_u A_u letterComparison_A_A_lem_res ↔ letterComparison_A_A_lem_res == Eq_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letterComparison_A_A_lem: f_rel_back.

Theorem letterComparison_A_B_lem letterComparison_A_B_lem_res:
  letterComparison_rel A_u B_u letterComparison_A_B_lem_res ↔ letterComparison_A_B_lem_res == Gt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letterComparison_A_B_lem: f_rel_back.

Theorem letterComparison_A_C_lem letterComparison_A_C_lem_res:
  letterComparison_rel A_u C_u letterComparison_A_C_lem_res ↔ letterComparison_A_C_lem_res == Gt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letterComparison_A_C_lem: f_rel_back.

Theorem letterComparison_A_D_lem letterComparison_A_D_lem_res:
  letterComparison_rel A_u D_u letterComparison_A_D_lem_res ↔ letterComparison_A_D_lem_res == Gt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letterComparison_A_D_lem: f_rel_back.

Theorem letterComparison_A_F_lem letterComparison_A_F_lem_res:
  letterComparison_rel A_u F_u letterComparison_A_F_lem_res ↔ letterComparison_A_F_lem_res == Gt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letterComparison_A_F_lem: f_rel_back.

Theorem letterComparison_B_A_lem letterComparison_B_A_lem_res:
  letterComparison_rel B_u A_u letterComparison_B_A_lem_res ↔ letterComparison_B_A_lem_res == Lt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letterComparison_B_A_lem: f_rel_back.

Theorem letterComparison_B_B_lem letterComparison_B_B_lem_res:
  letterComparison_rel B_u B_u letterComparison_B_B_lem_res ↔ letterComparison_B_B_lem_res == Eq_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letterComparison_B_B_lem: f_rel_back.

Theorem letterComparison_B_C_lem letterComparison_B_C_lem_res:
  letterComparison_rel B_u C_u letterComparison_B_C_lem_res ↔ letterComparison_B_C_lem_res == Gt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letterComparison_B_C_lem: f_rel_back.

Theorem letterComparison_B_D_lem letterComparison_B_D_lem_res:
  letterComparison_rel B_u D_u letterComparison_B_D_lem_res ↔ letterComparison_B_D_lem_res == Gt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letterComparison_B_D_lem: f_rel_back.

Theorem letterComparison_B_F_lem letterComparison_B_F_lem_res:
  letterComparison_rel B_u F_u letterComparison_B_F_lem_res ↔ letterComparison_B_F_lem_res == Gt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letterComparison_B_F_lem: f_rel_back.

Theorem letterComparison_C_A_lem letterComparison_C_A_lem_res:
  letterComparison_rel C_u A_u letterComparison_C_A_lem_res ↔ letterComparison_C_A_lem_res == Lt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letterComparison_C_A_lem: f_rel_back.

Theorem letterComparison_C_B_lem letterComparison_C_B_lem_res:
  letterComparison_rel C_u B_u letterComparison_C_B_lem_res ↔ letterComparison_C_B_lem_res == Lt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letterComparison_C_B_lem: f_rel_back.

Theorem letterComparison_C_C_lem letterComparison_C_C_lem_res:
  letterComparison_rel C_u C_u letterComparison_C_C_lem_res ↔ letterComparison_C_C_lem_res == Eq_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letterComparison_C_C_lem: f_rel_back.

Theorem letterComparison_C_D_lem letterComparison_C_D_lem_res:
  letterComparison_rel C_u D_u letterComparison_C_D_lem_res ↔ letterComparison_C_D_lem_res == Gt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letterComparison_C_D_lem: f_rel_back.

Theorem letterComparison_C_F_lem letterComparison_C_F_lem_res:
  letterComparison_rel C_u F_u letterComparison_C_F_lem_res ↔ letterComparison_C_F_lem_res == Gt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letterComparison_C_F_lem: f_rel_back.

Theorem letterComparison_D_A_lem letterComparison_D_A_lem_res:
  letterComparison_rel D_u A_u letterComparison_D_A_lem_res ↔ letterComparison_D_A_lem_res == Lt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letterComparison_D_A_lem: f_rel_back.

Theorem letterComparison_D_B_lem letterComparison_D_B_lem_res:
  letterComparison_rel D_u B_u letterComparison_D_B_lem_res ↔ letterComparison_D_B_lem_res == Lt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letterComparison_D_B_lem: f_rel_back.

Theorem letterComparison_D_C_lem letterComparison_D_C_lem_res:
  letterComparison_rel D_u C_u letterComparison_D_C_lem_res ↔ letterComparison_D_C_lem_res == Lt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letterComparison_D_C_lem: f_rel_back.

Theorem letterComparison_D_D_lem letterComparison_D_D_lem_res:
  letterComparison_rel D_u D_u letterComparison_D_D_lem_res ↔ letterComparison_D_D_lem_res == Eq_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letterComparison_D_D_lem: f_rel_back.

Theorem letterComparison_D_F_lem letterComparison_D_F_lem_res:
  letterComparison_rel D_u F_u letterComparison_D_F_lem_res ↔ letterComparison_D_F_lem_res == Gt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letterComparison_D_F_lem: f_rel_back.

Theorem letterComparison_F_A_lem letterComparison_F_A_lem_res:
  letterComparison_rel F_u A_u letterComparison_F_A_lem_res ↔ letterComparison_F_A_lem_res == Lt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letterComparison_F_A_lem: f_rel_back.

Theorem letterComparison_F_B_lem letterComparison_F_B_lem_res:
  letterComparison_rel F_u B_u letterComparison_F_B_lem_res ↔ letterComparison_F_B_lem_res == Lt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letterComparison_F_B_lem: f_rel_back.

Theorem letterComparison_F_C_lem letterComparison_F_C_lem_res:
  letterComparison_rel F_u C_u letterComparison_F_C_lem_res ↔ letterComparison_F_C_lem_res == Lt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letterComparison_F_C_lem: f_rel_back.

Theorem letterComparison_F_D_lem letterComparison_F_D_lem_res:
  letterComparison_rel F_u D_u letterComparison_F_D_lem_res ↔ letterComparison_F_D_lem_res == Lt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letterComparison_F_D_lem: f_rel_back.

Theorem letterComparison_F_F_lem letterComparison_F_F_lem_res:
  letterComparison_rel F_u F_u letterComparison_F_F_lem_res ↔ letterComparison_F_F_lem_res == Eq_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite letterComparison_F_F_lem: f_rel_back.

Theorem letterComparison_rel_ex
  (ds_d15A : Letter_u)
  (ds_d15A_p : Letter_wf ds_d15A ∧ True)
  (ds_d15B : Letter_u)
  (ds_d15B_p : Letter_wf ds_d15B ∧ True):
  letterComparison_rel
  ds_d15A
  ds_d15B
  ⌊ letterComparison (exist _ ds_d15A ds_d15A_p) (exist _ ds_d15B ds_d15B_p) -⌋.
Proof.
  Opaque letterComparison.
  existence_lemma_pre letterComparison;
  destruct ds_d15A as [| | | |];
  [destruct ds_d15B as [| | | |];
   [fix_notations | fix_notations | fix_notations | fix_notations | fix_notations] |
   destruct ds_d15B as [| | | |];
   [fix_notations | fix_notations | fix_notations | fix_notations | fix_notations] |
   destruct ds_d15B as [| | | |];
   [fix_notations | fix_notations | fix_notations | fix_notations | fix_notations] |
   destruct ds_d15B as [| | | |];
   [fix_notations | fix_notations | fix_notations | fix_notations | fix_notations] |
   destruct ds_d15B as [| | | |];
   [fix_notations | fix_notations | fix_notations | fix_notations | fix_notations]];
  simpl in *.
  Transparent letterComparison.
  all: (existence_lemma_quicksolve letterComparison; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve letterComparison_rel_ex: rel_ax_db.

#[global] Opaque letterComparison.

Theorem letterComparison__letterComparison_rel_rw
  (ds_d15A : Letter_u)
  (ds_d15A_p : Letter_wf ds_d15A ∧ True)
  (ds_d15B : Letter_u)
  (ds_d15B_p : Letter_wf ds_d15B ∧ True)
  (VV : Comparison_u):
  ⌊ letterComparison (exist _ ds_d15A ds_d15A_p) (exist _ ds_d15B ds_d15B_p) -⌋ = VV
  ↔ letterComparison_rel ds_d15A ds_d15B VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite letterComparison__letterComparison_rel_rw: f_rel_funct_db.

#[global] Hint Resolve letterComparison__letterComparison_rel_rw: rel_ax_db.

#[global] Instance letterComparison_lookup_rw: dictionary rwLem letterComparison := {
    lookup' := letterComparison__letterComparison_rel_rw }.

Theorem letterComparison__letterComparison_rel (ds_d15A ds_d15B : Letter) (VV : Comparison_u):
  ⌊ letterComparison ds_d15A ds_d15B -⌋ = VV ↔ letterComparison_rel ⌊ ds_d15A ⌋ ⌊ ds_d15B ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite letterComparison__letterComparison_rel: f_rel_funct_db.

Theorem letterComparison__letterComparison_rel'
  (ds_d15A_u ds_d15B_u : Letter_u) (ds_d15A ds_d15B : Letter) (VV : Comparison_u):
  ds_d15A_u = ⌊ ds_d15A ⌋
  → (ds_d15B_u = ⌊ ds_d15B ⌋
     → ⌊ letterComparison ds_d15A ds_d15B -⌋ = VV ↔ letterComparison_rel ds_d15A_u ds_d15B_u VV).
Proof.
  intros -> ->. refine (letterComparison__letterComparison_rel ds_d15A ds_d15B VV).
Qed.

#[global] Hint Resolve letterComparison__letterComparison_rel': f_rel_funct_db.

Theorem letterComparison_rel_mk
  (ds_d15A : Letter_u)
  (ds_d15A_p : Letter_wf ds_d15A ∧ True)
  (ds_d15B : Letter_u)
  (ds_d15B_p : Letter_wf ds_d15B ∧ True):
  {VV: _ | letterComparison_rel ds_d15A ds_d15B VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, letterComparison_rel ds_d15A ds_d15B VV)
          (letterComparison (exist _ ds_d15A ds_d15A_p) (exist _ ds_d15B ds_d15B_p))
          _);
  rewrite <- letterComparison__letterComparison_rel';
  quicksolve.
Qed.

#[global] Hint Resolve letterComparison_rel_mk: f_rel_funct_db.

#[global] Instance letterComparison_pack:
  @Pack
  (Letter ::RT λ (ds_d15A : Letter), Letter ::RT λ (ds_d15B : Letter), nilRT)
  (Letter_u ::UT (Letter_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((Letter
  ::RT λ (ds_d15A : Letter),
       Letter ::RT λ (ds_d15B : Letter), nilRT)) ((Letter_u ::UT (Letter_u ::UT nilUT))))
  Comparison_u
  (λ (x_46193732 : ArgList (Letter
                            ::RT λ (ds_d15A : Letter), Letter ::RT λ (ds_d15B : Letter), nilRT))
     (v_x_46193732 : Comparison_u),
   ltac:(flattenP (λ (ds_d15A ds_d15B : Letter) (VV : Comparison_u),
 Comparison_wf VV ∧ True) x_46193732 v_x_46193732)).
Proof.
  buildPackG letterComparison letterComparison_rel letterComparison__letterComparison_rel letterComparison_rel_funct.
Defined.

#[global] Instance letterComparison_upack:
  @uPack (Letter_u ::UT (Letter_u ::UT nilUT)) Comparison_u.
Proof.
  buildUPackG letterComparison_rel letterComparison_rel_funct.
Defined.

Definition letterComparisonEq_spec (ds_d15z : Letter): Type :=
  {{∃ (letterComparison_res : Comparison_u),
    letterComparison_rel ⌊ ds_d15z ⌋ ⌊ ds_d15z ⌋ letterComparison_res ∧ letterComparison_res == Eq_u}}.

#[global] Hint Unfold letterComparisonEq_spec: lia_unfold.

Theorem letterComparisonEq (ds_d15z : Letter): letterComparisonEq_spec ds_d15z.
Proof.
  destruct ds_d15z as [ds_d15z ds_d15z_p].
  destruct ds_d15z as [| | | |].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (letterComparison_res : Comparison_u),
             letterComparison_rel A_u A_u letterComparison_res ∧ letterComparison_res == Eq_u)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (letterComparison_res : Comparison_u),
             letterComparison_rel B_u B_u letterComparison_res ∧ letterComparison_res == Eq_u)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (letterComparison_res : Comparison_u),
             letterComparison_rel C_u C_u letterComparison_res ∧ letterComparison_res == Eq_u)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (letterComparison_res : Comparison_u),
             letterComparison_rel D_u D_u letterComparison_res ∧ letterComparison_res == Eq_u)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (letterComparison_res : Comparison_u),
             letterComparison_rel F_u F_u letterComparison_res ∧ letterComparison_res == Eq_u)
            (# unit)
            ltac:(solver)).
Qed.

Definition lowerLetterLowers_spec
  (l : Letter)
  (p : {{∃ (letterComparison_res : Comparison_u),
         letterComparison_rel F_u ⌊ l ⌋ letterComparison_res ∧ letterComparison_res == Lt_u}}):
  Type :=
  {{∃ (lowerLetter_res : Letter_u),
    lowerLetter_rel ⌊ l ⌋ lowerLetter_res
    ∧ ∃ (letterComparison_res : Comparison_u),
      letterComparison_rel lowerLetter_res ⌊ l ⌋ letterComparison_res ∧ letterComparison_res == Lt_u}}.

#[global] Hint Unfold lowerLetterLowers_spec: lia_unfold.

Theorem lowerLetterLowers
  (l : Letter)
  (p : {{∃ (letterComparison_res : Comparison_u),
         letterComparison_rel F_u ⌊ l ⌋ letterComparison_res ∧ letterComparison_res == Lt_u}}):
  lowerLetterLowers_spec l p.
Proof.
  destruct l as [l l_p].
  destruct p as [p p_p].
  destruct l as [| | | |].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (lowerLetter_res : Letter_u),
             lowerLetter_rel A_u lowerLetter_res
             ∧ ∃ (letterComparison_res : Comparison_u),
               letterComparison_rel lowerLetter_res A_u letterComparison_res ∧ letterComparison_res == Lt_u)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (lowerLetter_res : Letter_u),
             lowerLetter_rel B_u lowerLetter_res
             ∧ ∃ (letterComparison_res : Comparison_u),
               letterComparison_rel lowerLetter_res B_u letterComparison_res ∧ letterComparison_res == Lt_u)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (lowerLetter_res : Letter_u),
             lowerLetter_rel C_u lowerLetter_res
             ∧ ∃ (letterComparison_res : Comparison_u),
               letterComparison_rel lowerLetter_res C_u letterComparison_res ∧ letterComparison_res == Lt_u)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (lowerLetter_res : Letter_u),
             lowerLetter_rel D_u lowerLetter_res
             ∧ ∃ (letterComparison_res : Comparison_u),
               letterComparison_rel lowerLetter_res D_u letterComparison_res ∧ letterComparison_res == Lt_u)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (lowerLetter_res : Letter_u),
             lowerLetter_rel F_u lowerLetter_res
             ∧ ∃ (letterComparison_res : Comparison_u),
               letterComparison_rel lowerLetter_res F_u letterComparison_res ∧ letterComparison_res == Lt_u)
            (exist (λ (p : Unit),
                    ∃ (letterComparison_res : Comparison_u),
                    letterComparison_rel F_u F_u letterComparison_res ∧ letterComparison_res == Lt_u) p ltac:(solver))
            ltac:(solver)).
Qed.

Definition modifierComparison_spec (ds_d15r ds_d15s : Modifier): Type :=
  Comparison.

#[global] Hint Unfold modifierComparison_spec: lia_unfold.

Definition modifierComparison (ds_d15r ds_d15s : Modifier): modifierComparison_spec ds_d15r ds_d15s.
Proof.
  destruct ds_d15r as [ds_d15r ds_d15r_p].
  destruct ds_d15s as [ds_d15s ds_d15s_p].
  destruct ds_d15r as [| |].
  - destruct ds_d15s as [| |].
    + refine Eq.
    + refine Lt.
    + refine Lt.
  - destruct ds_d15s as [| |].
    + refine Gt.
    + refine Eq.
    + refine Lt.
  - destruct ds_d15s as [| |].
    + refine Gt.
    + refine Gt.
    + refine Eq.
Defined.

Inductive modifierComparison_rel: Modifier_u → Modifier_u → Comparison_u → Prop :=
  | modifierComparison_Minus_Minus: modifierComparison_rel Minus_u Minus_u Eq_u
  | modifierComparison_Minus_Natural: modifierComparison_rel Minus_u Natural_u Lt_u
  | modifierComparison_Minus_Plus: modifierComparison_rel Minus_u Plus_u Lt_u
  | modifierComparison_Natural_Minus: modifierComparison_rel Natural_u Minus_u Gt_u
  | modifierComparison_Natural_Natural: modifierComparison_rel Natural_u Natural_u Eq_u
  | modifierComparison_Natural_Plus: modifierComparison_rel Natural_u Plus_u Lt_u
  | modifierComparison_Plus_Minus: modifierComparison_rel Plus_u Minus_u Gt_u
  | modifierComparison_Plus_Natural: modifierComparison_rel Plus_u Natural_u Gt_u
  | modifierComparison_Plus_Plus: modifierComparison_rel Plus_u Plus_u Eq_u.

#[global] Hint Constructors modifierComparison_rel: core_hint_db.

#[global] Instance modifierComparison_lookup_rel: dictionary rel modifierComparison := {
    lookup' := modifierComparison_rel }.

#[global] Instance modifierComparison_getF: getFunc modifierComparison_rel := {
    getF' := modifierComparison }.

Theorem modifierComparison_rel_funct [ds_d15r ds_d15s : Modifier_u]:
  ∀ (VV VV' : Comparison_u),
  modifierComparison_rel ds_d15r ds_d15s VV → (modifierComparison_rel ds_d15r ds_d15s VV' → VV = VV').
Proof.
  destruct ds_d15r as [| |];
  [destruct ds_d15s as [| |] | destruct ds_d15s as [| |] | destruct ds_d15s as [| |]];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve modifierComparison_rel_funct: f_rel_funct_db.

Theorem modifierComparison_Minus_Minus_lem modifierComparison_Minus_Minus_lem_res:
  modifierComparison_rel Minus_u Minus_u modifierComparison_Minus_Minus_lem_res
  ↔ modifierComparison_Minus_Minus_lem_res == Eq_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite modifierComparison_Minus_Minus_lem: f_rel_back.

Theorem modifierComparison_Minus_Natural_lem modifierComparison_Minus_Natural_lem_res:
  modifierComparison_rel Minus_u Natural_u modifierComparison_Minus_Natural_lem_res
  ↔ modifierComparison_Minus_Natural_lem_res == Lt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite modifierComparison_Minus_Natural_lem: f_rel_back.

Theorem modifierComparison_Minus_Plus_lem modifierComparison_Minus_Plus_lem_res:
  modifierComparison_rel Minus_u Plus_u modifierComparison_Minus_Plus_lem_res
  ↔ modifierComparison_Minus_Plus_lem_res == Lt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite modifierComparison_Minus_Plus_lem: f_rel_back.

Theorem modifierComparison_Natural_Minus_lem modifierComparison_Natural_Minus_lem_res:
  modifierComparison_rel Natural_u Minus_u modifierComparison_Natural_Minus_lem_res
  ↔ modifierComparison_Natural_Minus_lem_res == Gt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite modifierComparison_Natural_Minus_lem: f_rel_back.

Theorem modifierComparison_Natural_Natural_lem modifierComparison_Natural_Natural_lem_res:
  modifierComparison_rel Natural_u Natural_u modifierComparison_Natural_Natural_lem_res
  ↔ modifierComparison_Natural_Natural_lem_res == Eq_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite modifierComparison_Natural_Natural_lem: f_rel_back.

Theorem modifierComparison_Natural_Plus_lem modifierComparison_Natural_Plus_lem_res:
  modifierComparison_rel Natural_u Plus_u modifierComparison_Natural_Plus_lem_res
  ↔ modifierComparison_Natural_Plus_lem_res == Lt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite modifierComparison_Natural_Plus_lem: f_rel_back.

Theorem modifierComparison_Plus_Minus_lem modifierComparison_Plus_Minus_lem_res:
  modifierComparison_rel Plus_u Minus_u modifierComparison_Plus_Minus_lem_res
  ↔ modifierComparison_Plus_Minus_lem_res == Gt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite modifierComparison_Plus_Minus_lem: f_rel_back.

Theorem modifierComparison_Plus_Natural_lem modifierComparison_Plus_Natural_lem_res:
  modifierComparison_rel Plus_u Natural_u modifierComparison_Plus_Natural_lem_res
  ↔ modifierComparison_Plus_Natural_lem_res == Gt_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite modifierComparison_Plus_Natural_lem: f_rel_back.

Theorem modifierComparison_Plus_Plus_lem modifierComparison_Plus_Plus_lem_res:
  modifierComparison_rel Plus_u Plus_u modifierComparison_Plus_Plus_lem_res
  ↔ modifierComparison_Plus_Plus_lem_res == Eq_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite modifierComparison_Plus_Plus_lem: f_rel_back.

Theorem modifierComparison_rel_ex
  (ds_d15r : Modifier_u)
  (ds_d15r_p : Modifier_wf ds_d15r ∧ True)
  (ds_d15s : Modifier_u)
  (ds_d15s_p : Modifier_wf ds_d15s ∧ True):
  modifierComparison_rel
  ds_d15r
  ds_d15s
  ⌊ modifierComparison (exist _ ds_d15r ds_d15r_p) (exist _ ds_d15s ds_d15s_p) -⌋.
Proof.
  Opaque modifierComparison.
  existence_lemma_pre modifierComparison;
  destruct ds_d15r as [| |];
  [destruct ds_d15s as [| |];
   [fix_notations | fix_notations | fix_notations] |
   destruct ds_d15s as [| |];
   [fix_notations | fix_notations | fix_notations] |
   destruct ds_d15s as [| |];
   [fix_notations | fix_notations | fix_notations]];
  simpl in *.
  Transparent modifierComparison.
  all: (existence_lemma_quicksolve modifierComparison; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve modifierComparison_rel_ex: rel_ax_db.

#[global] Opaque modifierComparison.

Theorem modifierComparison__modifierComparison_rel_rw
  (ds_d15r : Modifier_u)
  (ds_d15r_p : Modifier_wf ds_d15r ∧ True)
  (ds_d15s : Modifier_u)
  (ds_d15s_p : Modifier_wf ds_d15s ∧ True)
  (VV : Comparison_u):
  ⌊ modifierComparison (exist _ ds_d15r ds_d15r_p) (exist _ ds_d15s ds_d15s_p) -⌋ = VV
  ↔ modifierComparison_rel ds_d15r ds_d15s VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite modifierComparison__modifierComparison_rel_rw: f_rel_funct_db.

#[global] Hint Resolve modifierComparison__modifierComparison_rel_rw: rel_ax_db.

#[global] Instance modifierComparison_lookup_rw: dictionary rwLem modifierComparison := {
    lookup' := modifierComparison__modifierComparison_rel_rw }.

Theorem modifierComparison__modifierComparison_rel (ds_d15r ds_d15s : Modifier) (VV : Comparison_u):
  ⌊ modifierComparison ds_d15r ds_d15s -⌋ = VV ↔ modifierComparison_rel ⌊ ds_d15r ⌋ ⌊ ds_d15s ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite modifierComparison__modifierComparison_rel: f_rel_funct_db.

Theorem modifierComparison__modifierComparison_rel'
  (ds_d15r_u ds_d15s_u : Modifier_u) (ds_d15r ds_d15s : Modifier) (VV : Comparison_u):
  ds_d15r_u = ⌊ ds_d15r ⌋
  → (ds_d15s_u = ⌊ ds_d15s ⌋
     → ⌊ modifierComparison ds_d15r ds_d15s -⌋ = VV ↔ modifierComparison_rel ds_d15r_u ds_d15s_u VV).
Proof.
  intros -> ->. refine (modifierComparison__modifierComparison_rel ds_d15r ds_d15s VV).
Qed.

#[global] Hint Resolve modifierComparison__modifierComparison_rel': f_rel_funct_db.

Theorem modifierComparison_rel_mk
  (ds_d15r : Modifier_u)
  (ds_d15r_p : Modifier_wf ds_d15r ∧ True)
  (ds_d15s : Modifier_u)
  (ds_d15s_p : Modifier_wf ds_d15s ∧ True):
  {VV: _ | modifierComparison_rel ds_d15r ds_d15s VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, modifierComparison_rel ds_d15r ds_d15s VV)
          (modifierComparison (exist _ ds_d15r ds_d15r_p) (exist _ ds_d15s ds_d15s_p))
          _);
  rewrite <- modifierComparison__modifierComparison_rel';
  quicksolve.
Qed.

#[global] Hint Resolve modifierComparison_rel_mk: f_rel_funct_db.

#[global] Instance modifierComparison_pack:
  @Pack
  (Modifier ::RT λ (ds_d15r : Modifier), Modifier ::RT λ (ds_d15s : Modifier), nilRT)
  (Modifier_u ::UT (Modifier_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((Modifier
  ::RT λ (ds_d15r : Modifier),
       Modifier ::RT λ (ds_d15s : Modifier), nilRT)) ((Modifier_u ::UT (Modifier_u ::UT nilUT))))
  Comparison_u
  (λ (x_90108088 : ArgList (Modifier
                            ::RT λ (ds_d15r : Modifier), Modifier ::RT λ (ds_d15s : Modifier), nilRT))
     (v_x_90108088 : Comparison_u),
   ltac:(flattenP (λ (ds_d15r ds_d15s : Modifier) (VV : Comparison_u),
 Comparison_wf VV ∧ True) x_90108088 v_x_90108088)).
Proof.
  buildPackG modifierComparison modifierComparison_rel modifierComparison__modifierComparison_rel modifierComparison_rel_funct.
Defined.

#[global] Instance modifierComparison_upack:
  @uPack (Modifier_u ::UT (Modifier_u ::UT nilUT)) Comparison_u.
Proof.
  buildUPackG modifierComparison_rel modifierComparison_rel_funct.
Defined.
