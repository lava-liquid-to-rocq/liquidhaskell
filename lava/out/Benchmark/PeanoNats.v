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

Definition Suc_lem (n : Nats): Nats_wf (Suc_u ⌊ n ⌋) ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Suc (n : Nats): Nats :=
  exist _ (Suc_u ⌊ n ⌋) (Suc_lem n).

Definition Zero_lem : Nats_wf Zero_u ∧ True.
Proof.
  repeat first [split; solver].
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

Definition add_spec (ds_d4mH n : Nats): Type :=
  Nats.

#[global] Hint Unfold add_spec: lia_unfold.

Definition add (ds_d4mH n : Nats): add_spec ds_d4mH n.
Proof.
  destruct ds_d4mH as [ds_d4mH ds_d4mH_p].
  destruct n as [n n_p].
  try revert n_p; generalize dependent n; induction ds_d4mH as [m IH_m|]; intros.
  - refine (Suc (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver))).
  - refine (exist (λ (n : Nats_u), Nats_wf n ∧ True) n ltac:(solver)).
Defined.

Inductive add_rel: Nats_u → Nats_u → Nats_u → Prop :=
  | add_Zero_x: ∀ n, add_rel Zero_u n n
  | add_Suc_x: ∀ m n (add_res : Nats_u), add_rel m n add_res → add_rel (Suc_u m) n (Suc_u add_res).

#[global] Hint Constructors add_rel: core_hint_db.

#[global] Instance add_lookup_rel: dictionary rel add := { lookup' := add_rel }.

#[global] Instance add_getF: getFunc add_rel := { getF' := add }.

Theorem add_rel_funct [ds_d4mH n : Nats_u]:
  ∀ (VV VV' : Nats_u), add_rel ds_d4mH n VV → (add_rel ds_d4mH n VV' → VV = VV').
Proof.
  try revert n_p; generalize dependent n; induction ds_d4mH as [m IH_m|]; intros;
  rel_functionhood_body.
Qed.

#[global] Hint Resolve add_rel_funct: f_rel_funct_db.

Theorem add_Zero_x_lem n add_Zero_x_lem_res:
  add_rel Zero_u n add_Zero_x_lem_res ↔ add_Zero_x_lem_res == n.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite add_Zero_x_lem: f_rel_back.

Theorem add_Suc_x_lem m n add_Suc_x_lem_res:
  add_rel (Suc_u m) n add_Suc_x_lem_res
  ↔ ∃ (add_res : Nats_u), add_rel m n add_res ∧ add_Suc_x_lem_res == Suc_u add_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite add_Suc_x_lem: f_rel_back.

Theorem add_rel_ex
  (ds_d4mH : Nats_u) (ds_d4mH_p : Nats_wf ds_d4mH ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True):
  add_rel ds_d4mH n ⌊ add (exist _ ds_d4mH ds_d4mH_p) (exist _ n n_p) -⌋.
Proof.
  Opaque add.
  existence_lemma_pre add;
  try revert n_p; generalize dependent n; induction ds_d4mH as [m IH_m|]; intros;
  [fix_notations;
   pose proof (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver)) as IH_14792487;
   try clear IH_m |
   fix_notations];
  simpl in *.
  Transparent add.
  all: (existence_lemma_quicksolve add; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve add_rel_ex: rel_ax_db.

#[global] Opaque add.

Theorem add__add_rel_rw
  (ds_d4mH : Nats_u)
  (ds_d4mH_p : Nats_wf ds_d4mH ∧ True)
  (n : Nats_u)
  (n_p : Nats_wf n ∧ True)
  (VV : Nats_u):
  ⌊ add (exist _ ds_d4mH ds_d4mH_p) (exist _ n n_p) -⌋ = VV ↔ add_rel ds_d4mH n VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite add__add_rel_rw: f_rel_funct_db.

#[global] Hint Resolve add__add_rel_rw: rel_ax_db.

#[global] Instance add_lookup_rw: dictionary rwLem add := { lookup' := add__add_rel_rw }.

Theorem add__add_rel (ds_d4mH n : Nats) (VV : Nats_u):
  ⌊ add ds_d4mH n -⌋ = VV ↔ add_rel ⌊ ds_d4mH ⌋ ⌊ n ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite add__add_rel: f_rel_funct_db.

Theorem add__add_rel' (ds_d4mH_u n_u : Nats_u) (ds_d4mH n : Nats) (VV : Nats_u):
  ds_d4mH_u = ⌊ ds_d4mH ⌋ → (n_u = ⌊ n ⌋ → ⌊ add ds_d4mH n -⌋ = VV ↔ add_rel ds_d4mH_u n_u VV).
Proof.
  intros -> ->. refine (add__add_rel ds_d4mH n VV).
Qed.

#[global] Hint Resolve add__add_rel': f_rel_funct_db.

Theorem add_rel_mk
  (ds_d4mH : Nats_u) (ds_d4mH_p : Nats_wf ds_d4mH ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True):
  {VV: _ | add_rel ds_d4mH n VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, add_rel ds_d4mH n VV)
          (add (exist _ ds_d4mH ds_d4mH_p) (exist _ n n_p))
          _);
  rewrite <- add__add_rel';
  quicksolve.
Qed.

#[global] Hint Resolve add_rel_mk: f_rel_funct_db.

#[global] Instance add_pack:
  @Pack
  (Nats ::RT λ (ds_d4mH : Nats), Nats ::RT λ (n : Nats), nilRT)
  (Nats_u ::UT (Nats_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((Nats ::RT λ (ds_d4mH : Nats), Nats ::RT λ (n : Nats), nilRT)) ((Nats_u ::UT (Nats_u ::UT nilUT))))
  Nats_u
  (λ (x_34303546 : ArgList (Nats ::RT λ (ds_d4mH : Nats), Nats ::RT λ (n : Nats), nilRT))
     (v_x_34303546 : Nats_u),
   ltac:(flattenP (λ (ds_d4mH n : Nats) (VV : Nats_u), Nats_wf VV ∧ True) x_34303546 v_x_34303546)).
Proof.
  buildPackG add add_rel add__add_rel add_rel_funct.
Defined.

#[global] Instance add_upack: @uPack (Nats_u ::UT (Nats_u ::UT nilUT)) Nats_u.
Proof.
  buildUPackG add_rel add_rel_funct.
Defined.

Definition add'_spec (m n : Nats): Type :=
  {v: Nats_u | Nats_wf v
               ∧ ∃ (add_res : Nats_u),
                 add_rel ⌊ m ⌋ ⌊ n ⌋ add_res
                 ∧ ∃ (add_res_2 : Nats_u), add_rel add_res Zero_u add_res_2 ∧ add_res_2 == v}.

#[global] Hint Unfold add'_spec: lia_unfold.

Definition add' (m n : Nats): add'_spec m n.
Proof.
  destruct m as [m m_p].
  destruct n as [n n_p].
  refine (subsumptionCast
          Nats_u
          (λ (v : Nats_u),
           Nats_wf v
           ∧ ∃ (add_res : Nats_u),
             add_rel m n add_res ∧ ∃ (add_res_2 : Nats_u), add_rel add_res Zero_u add_res_2 ∧ add_res_2 == v)
          (add
           (add
            (exist (λ (m : Nats_u), Nats_wf m ∧ True) m ltac:(solver))
            (exist (λ (n : Nats_u), Nats_wf n ∧ True) n ltac:(solver)))
           Zero)
          ltac:(solver)).
Defined.

Definition add''_spec (m n : Nats): Type :=
  {v: Nats_u | Nats_wf v ∧ ∃ (add_res : Nats_u), add_rel ⌊ m ⌋ ⌊ n ⌋ add_res ∧ add_res == v}.

#[global] Hint Unfold add''_spec: lia_unfold.

Definition add'' (m n : Nats): add''_spec m n.
Proof.
  destruct m as [m m_p].
  destruct n as [n n_p].
  refine (subsumptionCast
          Nats_u
          (λ (v : Nats_u), Nats_wf v ∧ ∃ (add_res : Nats_u), add_rel m n add_res ∧ add_res == v)
          (add
           (exist (λ (m : Nats_u), Nats_wf m ∧ True) m ltac:(solver))
           (exist (λ (n : Nats_u), Nats_wf n ∧ True) n ltac:(solver)))
          ltac:(solver)).
Defined.

Definition add_assoc_spec (ds_d4mB ds_d4mC ds_d4mD : Nats): Type :=
  {{∃ (add_res : Nats_u),
    add_rel ⌊ ds_d4mC ⌋ ⌊ ds_d4mD ⌋ add_res
    ∧ ∃ (add_res_2 : Nats_u),
      add_rel ⌊ ds_d4mB ⌋ add_res add_res_2
      ∧ ∃ (add_res_3 : Nats_u),
        add_rel ⌊ ds_d4mB ⌋ ⌊ ds_d4mC ⌋ add_res_3
        ∧ ∃ (add_res_4 : Nats_u), add_rel add_res_3 ⌊ ds_d4mD ⌋ add_res_4 ∧ add_res_2 == add_res_4}}.

#[global] Hint Unfold add_assoc_spec: lia_unfold.

Theorem add_assoc (ds_d4mB ds_d4mC ds_d4mD : Nats): add_assoc_spec ds_d4mB ds_d4mC ds_d4mD.
Proof.
  destruct ds_d4mB as [ds_d4mB ds_d4mB_p].
  destruct ds_d4mC as [ds_d4mC ds_d4mC_p].
  destruct ds_d4mD as [ds_d4mD ds_d4mD_p].
  try revert ds_d4mD_p; generalize dependent ds_d4mD;
  try revert ds_d4mC_p; generalize dependent ds_d4mC;
  induction ds_d4mB as [m IH_m|];
  intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (add_res : Nats_u),
             add_rel ds_d4mC ds_d4mD add_res
             ∧ ∃ (add_res_2 : Nats_u),
               add_rel ds_d4mB add_res add_res_2
               ∧ ∃ (add_res_3 : Nats_u),
                 add_rel ds_d4mB ds_d4mC add_res_3
                 ∧ ∃ (add_res_4 : Nats_u), add_rel add_res_3 ds_d4mD add_res_4 ∧ add_res_2 == add_res_4)
            (IH_m
             ltac:(try clear IH_m; solver)
             ds_d4mC
             ltac:(try clear IH_m; solver)
             ds_d4mD
             ltac:(try clear IH_m; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (add_res : Nats_u),
             add_rel ds_d4mC ds_d4mD add_res
             ∧ ∃ (add_res_2 : Nats_u),
               add_rel ds_d4mB add_res add_res_2
               ∧ ∃ (add_res_3 : Nats_u),
                 add_rel ds_d4mB ds_d4mC add_res_3
                 ∧ ∃ (add_res_4 : Nats_u), add_rel add_res_3 ds_d4mD add_res_4 ∧ add_res_2 == add_res_4)
            (# unit)
            ltac:(solver)).
Qed.

Definition add_suc_r_spec (ds_d4mq ds_d4mr : Nats): Type :=
  {{∃ (add_res : Nats_u),
    add_rel ⌊ ds_d4mq ⌋ ⌊ ds_d4mr ⌋ add_res
    ∧ ∃ (add_res_2 : Nats_u),
      add_rel ⌊ ds_d4mq ⌋ (Suc_u ⌊ ds_d4mr ⌋) add_res_2 ∧ Suc_u add_res == add_res_2}}.

#[global] Hint Unfold add_suc_r_spec: lia_unfold.

Theorem add_suc_r (ds_d4mq ds_d4mr : Nats): add_suc_r_spec ds_d4mq ds_d4mr.
Proof.
  destruct ds_d4mq as [ds_d4mq ds_d4mq_p].
  destruct ds_d4mr as [ds_d4mr ds_d4mr_p].
  try revert ds_d4mr_p; generalize dependent ds_d4mr; induction ds_d4mq as [m IH_m|]; intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (add_res : Nats_u),
             add_rel ds_d4mq ds_d4mr add_res
             ∧ ∃ (add_res_2 : Nats_u), add_rel ds_d4mq (Suc_u ds_d4mr) add_res_2 ∧ Suc_u add_res == add_res_2)
            (IH_m ltac:(try clear IH_m; solver) ds_d4mr ltac:(try clear IH_m; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (add_res : Nats_u),
             add_rel ds_d4mq ds_d4mr add_res
             ∧ ∃ (add_res_2 : Nats_u), add_rel ds_d4mq (Suc_u ds_d4mr) add_res_2 ∧ Suc_u add_res == add_res_2)
            (# unit)
            ltac:(solver)).
Qed.

Definition add_zero_l_spec (ds_d4mE : Nats): Type :=
  {{∃ (add_res : Nats_u), add_rel Zero_u ⌊ ds_d4mE ⌋ add_res ∧ add_res == ⌊ ds_d4mE ⌋}}.

#[global] Hint Unfold add_zero_l_spec: lia_unfold.

Theorem add_zero_l (ds_d4mE : Nats): add_zero_l_spec ds_d4mE.
Proof.
  destruct ds_d4mE as [ds_d4mE ds_d4mE_p].
  induction ds_d4mE as [n IH_n|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (add_res : Nats_u), add_rel Zero_u ds_d4mE add_res ∧ add_res == ds_d4mE)
            (IH_n ltac:(try clear IH_n; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (add_res : Nats_u), add_rel Zero_u ds_d4mE add_res ∧ add_res == ds_d4mE)
            (# unit)
            ltac:(solver)).
Qed.

Definition add_zero_l_test_spec : Type :=
  {{∃ (add_res : Nats_u),
    add_rel Zero_u (Suc_u (Suc_u Zero_u)) add_res ∧ add_res == Suc_u (Suc_u Zero_u)}}.

#[global] Hint Unfold add_zero_l_test_spec: lia_unfold.

Theorem add_zero_l_test : add_zero_l_test_spec.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (add_res : Nats_u),
           add_rel Zero_u (Suc_u (Suc_u Zero_u)) add_res ∧ add_res == Suc_u (Suc_u Zero_u))
          (add_zero_l (Suc (Suc Zero)))
          ltac:(solver)).
Qed.

Definition add_zero_r_spec (ds_d4ms : Nats): Type :=
  {{∃ (add_res : Nats_u), add_rel ⌊ ds_d4ms ⌋ Zero_u add_res ∧ add_res == ⌊ ds_d4ms ⌋}}.

#[global] Hint Unfold add_zero_r_spec: lia_unfold.

Theorem add_zero_r (ds_d4ms : Nats): add_zero_r_spec ds_d4ms.
Proof.
  destruct ds_d4ms as [ds_d4ms ds_d4ms_p].
  induction ds_d4ms as [n IH_n|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (add_res : Nats_u), add_rel ds_d4ms Zero_u add_res ∧ add_res == ds_d4ms)
            (IH_n ltac:(try clear IH_n; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (add_res : Nats_u), add_rel ds_d4ms Zero_u add_res ∧ add_res == ds_d4ms)
            (# unit)
            ltac:(solver)).
Qed.

Definition eqN_spec (ds_d4m4 ds_d4m5 : Nats): Type :=
  Bool.

#[global] Hint Unfold eqN_spec: lia_unfold.

Definition eqN (ds_d4m4 ds_d4m5 : Nats): eqN_spec ds_d4m4 ds_d4m5.
Proof.
  destruct ds_d4m4 as [ds_d4m4 ds_d4m4_p].
  destruct ds_d4m5 as [ds_d4m5 ds_d4m5_p].
  try revert ds_d4m5_p; generalize dependent ds_d4m5; induction ds_d4m4 as [m IH_m|]; intros.
  - destruct ds_d4m5 as [n|].
    + refine (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver)).
    + refine (# false).
  - destruct ds_d4m5 as [lq_anf7205759403792810467|].
    + refine (# false).
    + refine (# true).
Defined.

Inductive eqN_rel: Nats_u → Nats_u → bool → Prop :=
  | eqN_Zero_Zero: eqN_rel Zero_u Zero_u true
  | eqN_Zero_Suc: ∀ lq_anf7205759403792810467, eqN_rel Zero_u (Suc_u lq_anf7205759403792810467) false
  | eqN_Suc_Zero: ∀ m, eqN_rel (Suc_u m) Zero_u false
  | eqN_Suc_Suc: ∀ m n (eqN_res : bool), eqN_rel m n eqN_res → eqN_rel (Suc_u m) (Suc_u n) eqN_res.

#[global] Hint Constructors eqN_rel: core_hint_db.

#[global] Instance eqN_lookup_rel: dictionary rel eqN := { lookup' := eqN_rel }.

#[global] Instance eqN_getF: getFunc eqN_rel := { getF' := eqN }.

Theorem eqN_rel_funct [ds_d4m4 ds_d4m5 : Nats_u]:
  ∀ (VV VV' : bool), eqN_rel ds_d4m4 ds_d4m5 VV → (eqN_rel ds_d4m4 ds_d4m5 VV' → VV = VV').
Proof.
  try revert ds_d4m5_p; generalize dependent ds_d4m5; induction ds_d4m4 as [m IH_m|]; intros;
  [destruct ds_d4m5 as [n|] | destruct ds_d4m5 as [lq_anf7205759403792810467|]];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve eqN_rel_funct: f_rel_funct_db.

Theorem eqN_Zero_Zero_lem eqN_Zero_Zero_lem_res:
  eqN_rel Zero_u Zero_u eqN_Zero_Zero_lem_res ↔ eqN_Zero_Zero_lem_res == true.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite eqN_Zero_Zero_lem: f_rel_back.

Theorem eqN_Zero_Suc_lem lq_anf7205759403792810467 eqN_Zero_Suc_lem_res:
  eqN_rel Zero_u (Suc_u lq_anf7205759403792810467) eqN_Zero_Suc_lem_res
  ↔ eqN_Zero_Suc_lem_res == false.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite eqN_Zero_Suc_lem: f_rel_back.

Theorem eqN_Suc_Zero_lem m eqN_Suc_Zero_lem_res:
  eqN_rel (Suc_u m) Zero_u eqN_Suc_Zero_lem_res ↔ eqN_Suc_Zero_lem_res == false.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite eqN_Suc_Zero_lem: f_rel_back.

Theorem eqN_Suc_Suc_lem m n eqN_Suc_Suc_lem_res:
  eqN_rel (Suc_u m) (Suc_u n) eqN_Suc_Suc_lem_res
  ↔ ∃ (eqN_res : bool), eqN_rel m n eqN_res ∧ eqN_Suc_Suc_lem_res == eqN_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite eqN_Suc_Suc_lem: f_rel_back.

Theorem eqN_rel_ex
  (ds_d4m4 : Nats_u)
  (ds_d4m4_p : Nats_wf ds_d4m4 ∧ True)
  (ds_d4m5 : Nats_u)
  (ds_d4m5_p : Nats_wf ds_d4m5 ∧ True):
  eqN_rel ds_d4m4 ds_d4m5 ⌊ eqN (exist _ ds_d4m4 ds_d4m4_p) (exist _ ds_d4m5 ds_d4m5_p) -⌋.
Proof.
  Opaque eqN.
  existence_lemma_pre eqN;
  try revert ds_d4m5_p; generalize dependent ds_d4m5; induction ds_d4m4 as [m IH_m|]; intros;
  [destruct ds_d4m5 as [n|];
   [fix_notations;
    pose proof (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver)) as IH_14792487;
    try clear IH_m |
    fix_notations] |
   destruct ds_d4m5 as [lq_anf7205759403792810467|];
   [fix_notations | fix_notations]];
  simpl in *.
  Transparent eqN.
  all: (existence_lemma_quicksolve eqN; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve eqN_rel_ex: rel_ax_db.

#[global] Opaque eqN.

Theorem eqN__eqN_rel_rw
  (ds_d4m4 : Nats_u)
  (ds_d4m4_p : Nats_wf ds_d4m4 ∧ True)
  (ds_d4m5 : Nats_u)
  (ds_d4m5_p : Nats_wf ds_d4m5 ∧ True)
  (VV : bool):
  ⌊ eqN (exist _ ds_d4m4 ds_d4m4_p) (exist _ ds_d4m5 ds_d4m5_p) -⌋ = VV ↔ eqN_rel ds_d4m4 ds_d4m5 VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite eqN__eqN_rel_rw: f_rel_funct_db.

#[global] Hint Resolve eqN__eqN_rel_rw: rel_ax_db.

#[global] Instance eqN_lookup_rw: dictionary rwLem eqN := { lookup' := eqN__eqN_rel_rw }.

Theorem eqN__eqN_rel (ds_d4m4 ds_d4m5 : Nats) (VV : bool):
  ⌊ eqN ds_d4m4 ds_d4m5 -⌋ = VV ↔ eqN_rel ⌊ ds_d4m4 ⌋ ⌊ ds_d4m5 ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite eqN__eqN_rel: f_rel_funct_db.

Theorem eqN__eqN_rel' (ds_d4m4_u ds_d4m5_u : Nats_u) (ds_d4m4 ds_d4m5 : Nats) (VV : bool):
  ds_d4m4_u = ⌊ ds_d4m4 ⌋
  → (ds_d4m5_u = ⌊ ds_d4m5 ⌋ → ⌊ eqN ds_d4m4 ds_d4m5 -⌋ = VV ↔ eqN_rel ds_d4m4_u ds_d4m5_u VV).
Proof.
  intros -> ->. refine (eqN__eqN_rel ds_d4m4 ds_d4m5 VV).
Qed.

#[global] Hint Resolve eqN__eqN_rel': f_rel_funct_db.

Theorem eqN_rel_mk
  (ds_d4m4 : Nats_u)
  (ds_d4m4_p : Nats_wf ds_d4m4 ∧ True)
  (ds_d4m5 : Nats_u)
  (ds_d4m5_p : Nats_wf ds_d4m5 ∧ True):
  {VV: _ | eqN_rel ds_d4m4 ds_d4m5 VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, eqN_rel ds_d4m4 ds_d4m5 VV)
          (eqN (exist _ ds_d4m4 ds_d4m4_p) (exist _ ds_d4m5 ds_d4m5_p))
          _);
  rewrite <- eqN__eqN_rel';
  quicksolve.
Qed.

#[global] Hint Resolve eqN_rel_mk: f_rel_funct_db.

#[global] Instance eqN_pack:
  @Pack
  (Nats ::RT λ (ds_d4m4 : Nats), Nats ::RT λ (ds_d4m5 : Nats), nilRT)
  (Nats_u ::UT (Nats_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((Nats
  ::RT λ (ds_d4m4 : Nats), Nats ::RT λ (ds_d4m5 : Nats), nilRT)) ((Nats_u ::UT (Nats_u ::UT nilUT))))
  bool
  (λ (x_40690009 : ArgList (Nats ::RT λ (ds_d4m4 : Nats), Nats ::RT λ (ds_d4m5 : Nats), nilRT))
     (v_x_40690009 : bool),
   ltac:(flattenP (λ (ds_d4m4 ds_d4m5 : Nats) (VV : bool), True) x_40690009 v_x_40690009)).
Proof.
  buildPackG eqN eqN_rel eqN__eqN_rel eqN_rel_funct.
Defined.

#[global] Instance eqN_upack: @uPack (Nats_u ::UT (Nats_u ::UT nilUT)) bool.
Proof.
  buildUPackG eqN_rel eqN_rel_funct.
Defined.

Definition test_eqN_spec : Type :=
  {r : bool | is_true r}.

#[global] Hint Unfold test_eqN_spec: lia_unfold.

Definition test_eqN : test_eqN_spec.
Proof.
  refine (subsumptionCast
          bool
          (λ (r : bool), is_true r)
          (eqN (Suc (Suc (Suc Zero))) (Suc (Suc (Suc Zero))))
          ltac:(solver)).
Defined.

Definition test_eqN'_spec : Type :=
  {r : bool | ¬ is_true r}.

#[global] Hint Unfold test_eqN'_spec: lia_unfold.

Definition test_eqN' : test_eqN'_spec.
Proof.
  refine (subsumptionCast
          bool
          (λ (r : bool), ¬ is_true r)
          (eqN (Suc (Suc Zero)) (Suc Zero))
          ltac:(solver)).
Defined.

Definition geqN_spec (ds_d4mj ds_d4mk : Nats): Type :=
  Bool.

#[global] Hint Unfold geqN_spec: lia_unfold.

Definition geqN (ds_d4mj ds_d4mk : Nats): geqN_spec ds_d4mj ds_d4mk.
Proof.
  destruct ds_d4mj as [ds_d4mj ds_d4mj_p].
  destruct ds_d4mk as [ds_d4mk ds_d4mk_p].
  try revert ds_d4mj_p; generalize dependent ds_d4mj;
  induction ds_d4mk as [lq_anf7205759403792810464 IH_lq_anf7205759403792810464|];
  intros.
  - destruct ds_d4mj as [m|].
    + refine (IH_lq_anf7205759403792810464
              ltac:(try clear IH_lq_anf7205759403792810464; solver)
              m
              ltac:(try clear IH_lq_anf7205759403792810464; solver)).
    + refine (# false).
  - refine (# true).
Defined.

Inductive geqN_rel: Nats_u → Nats_u → bool → Prop :=
  | geqN_x_Zero: ∀ ds_d4mj, geqN_rel ds_d4mj Zero_u true
  | geqN_Zero_Suc: ∀ lq_anf7205759403792810464,
                   geqN_rel Zero_u (Suc_u lq_anf7205759403792810464) false
  | geqN_Suc_Suc: ∀ m lq_anf7205759403792810464 (geqN_res : bool),
                  geqN_rel m lq_anf7205759403792810464 geqN_res
                  → geqN_rel (Suc_u m) (Suc_u lq_anf7205759403792810464) geqN_res.

#[global] Hint Constructors geqN_rel: core_hint_db.

#[global] Instance geqN_lookup_rel: dictionary rel geqN := { lookup' := geqN_rel }.

#[global] Instance geqN_getF: getFunc geqN_rel := { getF' := geqN }.

Theorem geqN_rel_funct [ds_d4mj ds_d4mk : Nats_u]:
  ∀ (VV VV' : bool), geqN_rel ds_d4mj ds_d4mk VV → (geqN_rel ds_d4mj ds_d4mk VV' → VV = VV').
Proof.
  try revert ds_d4mj_p; generalize dependent ds_d4mj;
  induction ds_d4mk as [lq_anf7205759403792810464 IH_lq_anf7205759403792810464|];
  intros;
  [destruct ds_d4mj as [m|] |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve geqN_rel_funct: f_rel_funct_db.

Theorem geqN_x_Zero_lem ds_d4mj geqN_x_Zero_lem_res:
  geqN_rel ds_d4mj Zero_u geqN_x_Zero_lem_res ↔ geqN_x_Zero_lem_res == true.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite geqN_x_Zero_lem: f_rel_back.

Theorem geqN_Zero_Suc_lem lq_anf7205759403792810464 geqN_Zero_Suc_lem_res:
  geqN_rel Zero_u (Suc_u lq_anf7205759403792810464) geqN_Zero_Suc_lem_res
  ↔ geqN_Zero_Suc_lem_res == false.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite geqN_Zero_Suc_lem: f_rel_back.

Theorem geqN_Suc_Suc_lem lq_anf7205759403792810464 m geqN_Suc_Suc_lem_res:
  geqN_rel (Suc_u m) (Suc_u lq_anf7205759403792810464) geqN_Suc_Suc_lem_res
  ↔ ∃ (geqN_res : bool),
    geqN_rel m lq_anf7205759403792810464 geqN_res ∧ geqN_Suc_Suc_lem_res == geqN_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite geqN_Suc_Suc_lem: f_rel_back.

Theorem geqN_rel_ex
  (ds_d4mj : Nats_u)
  (ds_d4mj_p : Nats_wf ds_d4mj ∧ True)
  (ds_d4mk : Nats_u)
  (ds_d4mk_p : Nats_wf ds_d4mk ∧ True):
  geqN_rel ds_d4mj ds_d4mk ⌊ geqN (exist _ ds_d4mj ds_d4mj_p) (exist _ ds_d4mk ds_d4mk_p) -⌋.
Proof.
  Opaque geqN.
  existence_lemma_pre geqN;
  try revert ds_d4mj_p; generalize dependent ds_d4mj;
  induction ds_d4mk as [lq_anf7205759403792810464 IH_lq_anf7205759403792810464|];
  intros;
  [destruct ds_d4mj as [m|];
   [fix_notations;
    pose proof (IH_lq_anf7205759403792810464
                ltac:(try clear IH_lq_anf7205759403792810464; solver)
                m
                ltac:(try clear IH_lq_anf7205759403792810464; solver)) as IH_47961826;
    try clear IH_lq_anf7205759403792810464 |
    fix_notations] |
   fix_notations];
  simpl in *.
  Transparent geqN.
  all: (existence_lemma_quicksolve geqN; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve geqN_rel_ex: rel_ax_db.

#[global] Opaque geqN.

Theorem geqN__geqN_rel_rw
  (ds_d4mj : Nats_u)
  (ds_d4mj_p : Nats_wf ds_d4mj ∧ True)
  (ds_d4mk : Nats_u)
  (ds_d4mk_p : Nats_wf ds_d4mk ∧ True)
  (VV : bool):
  ⌊ geqN (exist _ ds_d4mj ds_d4mj_p) (exist _ ds_d4mk ds_d4mk_p) -⌋ = VV
  ↔ geqN_rel ds_d4mj ds_d4mk VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite geqN__geqN_rel_rw: f_rel_funct_db.

#[global] Hint Resolve geqN__geqN_rel_rw: rel_ax_db.

#[global] Instance geqN_lookup_rw: dictionary rwLem geqN := { lookup' := geqN__geqN_rel_rw }.

Theorem geqN__geqN_rel (ds_d4mj ds_d4mk : Nats) (VV : bool):
  ⌊ geqN ds_d4mj ds_d4mk -⌋ = VV ↔ geqN_rel ⌊ ds_d4mj ⌋ ⌊ ds_d4mk ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite geqN__geqN_rel: f_rel_funct_db.

Theorem geqN__geqN_rel' (ds_d4mj_u ds_d4mk_u : Nats_u) (ds_d4mj ds_d4mk : Nats) (VV : bool):
  ds_d4mj_u = ⌊ ds_d4mj ⌋
  → (ds_d4mk_u = ⌊ ds_d4mk ⌋ → ⌊ geqN ds_d4mj ds_d4mk -⌋ = VV ↔ geqN_rel ds_d4mj_u ds_d4mk_u VV).
Proof.
  intros -> ->. refine (geqN__geqN_rel ds_d4mj ds_d4mk VV).
Qed.

#[global] Hint Resolve geqN__geqN_rel': f_rel_funct_db.

Theorem geqN_rel_mk
  (ds_d4mj : Nats_u)
  (ds_d4mj_p : Nats_wf ds_d4mj ∧ True)
  (ds_d4mk : Nats_u)
  (ds_d4mk_p : Nats_wf ds_d4mk ∧ True):
  {VV: _ | geqN_rel ds_d4mj ds_d4mk VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, geqN_rel ds_d4mj ds_d4mk VV)
          (geqN (exist _ ds_d4mj ds_d4mj_p) (exist _ ds_d4mk ds_d4mk_p))
          _);
  rewrite <- geqN__geqN_rel';
  quicksolve.
Qed.

#[global] Hint Resolve geqN_rel_mk: f_rel_funct_db.

#[global] Instance geqN_pack:
  @Pack
  (Nats ::RT λ (ds_d4mj : Nats), Nats ::RT λ (ds_d4mk : Nats), nilRT)
  (Nats_u ::UT (Nats_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((Nats
  ::RT λ (ds_d4mj : Nats), Nats ::RT λ (ds_d4mk : Nats), nilRT)) ((Nats_u ::UT (Nats_u ::UT nilUT))))
  bool
  (λ (x_24036052 : ArgList (Nats ::RT λ (ds_d4mj : Nats), Nats ::RT λ (ds_d4mk : Nats), nilRT))
     (v_x_24036052 : bool),
   ltac:(flattenP (λ (ds_d4mj ds_d4mk : Nats) (VV : bool), True) x_24036052 v_x_24036052)).
Proof.
  buildPackG geqN geqN_rel geqN__geqN_rel geqN_rel_funct.
Defined.

#[global] Instance geqN_upack: @uPack (Nats_u ::UT (Nats_u ::UT nilUT)) bool.
Proof.
  buildUPackG geqN_rel geqN_rel_funct.
Defined.

Definition mult_spec (ds_d4mJ ds_d4mK : Nats): Type :=
  Nats.

#[global] Hint Unfold mult_spec: lia_unfold.

Definition mult (ds_d4mJ ds_d4mK : Nats): mult_spec ds_d4mJ ds_d4mK.
Proof.
  destruct ds_d4mJ as [ds_d4mJ ds_d4mJ_p].
  destruct ds_d4mK as [ds_d4mK ds_d4mK_p].
  try revert ds_d4mK_p; generalize dependent ds_d4mK; induction ds_d4mJ as [m IH_m|]; intros.
  - refine (add
            (exist (λ (ds_d4mK : Nats_u), Nats_wf ds_d4mK ∧ True) ds_d4mK ltac:(solver))
            (IH_m ltac:(try clear IH_m; solver) ds_d4mK ltac:(try clear IH_m; solver))).
  - refine Zero.
Defined.

Inductive mult_rel: Nats_u → Nats_u → Nats_u → Prop :=
  | mult_Zero_x: ∀ ds_d4mK, mult_rel Zero_u ds_d4mK Zero_u
  | mult_Suc_x: ∀ m ds_d4mK (mult_res : Nats_u),
                mult_rel m ds_d4mK mult_res
                → ∀ (add_res : Nats_u), add_rel ds_d4mK mult_res add_res → mult_rel (Suc_u m) ds_d4mK add_res.

#[global] Hint Constructors mult_rel: core_hint_db.

#[global] Instance mult_lookup_rel: dictionary rel mult := { lookup' := mult_rel }.

#[global] Instance mult_getF: getFunc mult_rel := { getF' := mult }.

Theorem mult_rel_funct [ds_d4mJ ds_d4mK : Nats_u]:
  ∀ (VV VV' : Nats_u), mult_rel ds_d4mJ ds_d4mK VV → (mult_rel ds_d4mJ ds_d4mK VV' → VV = VV').
Proof.
  try revert ds_d4mK_p; generalize dependent ds_d4mK; induction ds_d4mJ as [m IH_m|]; intros;
  rel_functionhood_body.
Qed.

#[global] Hint Resolve mult_rel_funct: f_rel_funct_db.

Theorem mult_Zero_x_lem ds_d4mK mult_Zero_x_lem_res:
  mult_rel Zero_u ds_d4mK mult_Zero_x_lem_res ↔ mult_Zero_x_lem_res == Zero_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite mult_Zero_x_lem: f_rel_back.

Theorem mult_Suc_x_lem ds_d4mK m mult_Suc_x_lem_res:
  mult_rel (Suc_u m) ds_d4mK mult_Suc_x_lem_res
  ↔ ∃ (mult_res : Nats_u),
    mult_rel m ds_d4mK mult_res
    ∧ ∃ (add_res : Nats_u), add_rel ds_d4mK mult_res add_res ∧ mult_Suc_x_lem_res == add_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite mult_Suc_x_lem: f_rel_back.

Theorem mult_rel_ex
  (ds_d4mJ : Nats_u)
  (ds_d4mJ_p : Nats_wf ds_d4mJ ∧ True)
  (ds_d4mK : Nats_u)
  (ds_d4mK_p : Nats_wf ds_d4mK ∧ True):
  mult_rel ds_d4mJ ds_d4mK ⌊ mult (exist _ ds_d4mJ ds_d4mJ_p) (exist _ ds_d4mK ds_d4mK_p) -⌋.
Proof.
  Opaque mult.
  existence_lemma_pre mult;
  try revert ds_d4mK_p; generalize dependent ds_d4mK; induction ds_d4mJ as [m IH_m|]; intros;
  [fix_notations;
   pose proof (IH_m
               ltac:(try clear IH_m; solver)
               ds_d4mK
               ltac:(try clear IH_m; solver)) as IH_10580583;
   try clear IH_m |
   fix_notations];
  simpl in *.
  Transparent mult.
  all: (existence_lemma_quicksolve mult; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve mult_rel_ex: rel_ax_db.

#[global] Opaque mult.

Theorem mult__mult_rel_rw
  (ds_d4mJ : Nats_u)
  (ds_d4mJ_p : Nats_wf ds_d4mJ ∧ True)
  (ds_d4mK : Nats_u)
  (ds_d4mK_p : Nats_wf ds_d4mK ∧ True)
  (VV : Nats_u):
  ⌊ mult (exist _ ds_d4mJ ds_d4mJ_p) (exist _ ds_d4mK ds_d4mK_p) -⌋ = VV
  ↔ mult_rel ds_d4mJ ds_d4mK VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite mult__mult_rel_rw: f_rel_funct_db.

#[global] Hint Resolve mult__mult_rel_rw: rel_ax_db.

#[global] Instance mult_lookup_rw: dictionary rwLem mult := { lookup' := mult__mult_rel_rw }.

Theorem mult__mult_rel (ds_d4mJ ds_d4mK : Nats) (VV : Nats_u):
  ⌊ mult ds_d4mJ ds_d4mK -⌋ = VV ↔ mult_rel ⌊ ds_d4mJ ⌋ ⌊ ds_d4mK ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite mult__mult_rel: f_rel_funct_db.

Theorem mult__mult_rel' (ds_d4mJ_u ds_d4mK_u : Nats_u) (ds_d4mJ ds_d4mK : Nats) (VV : Nats_u):
  ds_d4mJ_u = ⌊ ds_d4mJ ⌋
  → (ds_d4mK_u = ⌊ ds_d4mK ⌋ → ⌊ mult ds_d4mJ ds_d4mK -⌋ = VV ↔ mult_rel ds_d4mJ_u ds_d4mK_u VV).
Proof.
  intros -> ->. refine (mult__mult_rel ds_d4mJ ds_d4mK VV).
Qed.

#[global] Hint Resolve mult__mult_rel': f_rel_funct_db.

Theorem mult_rel_mk
  (ds_d4mJ : Nats_u)
  (ds_d4mJ_p : Nats_wf ds_d4mJ ∧ True)
  (ds_d4mK : Nats_u)
  (ds_d4mK_p : Nats_wf ds_d4mK ∧ True):
  {VV: _ | mult_rel ds_d4mJ ds_d4mK VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, mult_rel ds_d4mJ ds_d4mK VV)
          (mult (exist _ ds_d4mJ ds_d4mJ_p) (exist _ ds_d4mK ds_d4mK_p))
          _);
  rewrite <- mult__mult_rel';
  quicksolve.
Qed.

#[global] Hint Resolve mult_rel_mk: f_rel_funct_db.

#[global] Instance mult_pack:
  @Pack
  (Nats ::RT λ (ds_d4mJ : Nats), Nats ::RT λ (ds_d4mK : Nats), nilRT)
  (Nats_u ::UT (Nats_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((Nats
  ::RT λ (ds_d4mJ : Nats), Nats ::RT λ (ds_d4mK : Nats), nilRT)) ((Nats_u ::UT (Nats_u ::UT nilUT))))
  Nats_u
  (λ (x_18265935 : ArgList (Nats ::RT λ (ds_d4mJ : Nats), Nats ::RT λ (ds_d4mK : Nats), nilRT))
     (v_x_18265935 : Nats_u),
   ltac:(flattenP (λ (ds_d4mJ ds_d4mK : Nats) (VV : Nats_u), Nats_wf VV ∧ True) x_18265935 v_x_18265935)).
Proof.
  buildPackG mult mult_rel mult__mult_rel mult_rel_funct.
Defined.

#[global] Instance mult_upack: @uPack (Nats_u ::UT (Nats_u ::UT nilUT)) Nats_u.
Proof.
  buildUPackG mult_rel mult_rel_funct.
Defined.

Definition add_dist_rmult_spec (ds_d4mL ds_d4mM ds_d4mN : Nats): Type :=
  {{∃ (add_res : Nats_u),
    add_rel ⌊ ds_d4mL ⌋ ⌊ ds_d4mM ⌋ add_res
    ∧ ∃ (mult_res : Nats_u),
      mult_rel add_res ⌊ ds_d4mN ⌋ mult_res
      ∧ ∃ (mult_res_2 : Nats_u),
        mult_rel ⌊ ds_d4mM ⌋ ⌊ ds_d4mN ⌋ mult_res_2
        ∧ ∃ (mult_res_3 : Nats_u),
          mult_rel ⌊ ds_d4mL ⌋ ⌊ ds_d4mN ⌋ mult_res_3
          ∧ ∃ (add_res_2 : Nats_u), add_rel mult_res_3 mult_res_2 add_res_2 ∧ mult_res == add_res_2}}.

#[global] Hint Unfold add_dist_rmult_spec: lia_unfold.

Theorem add_dist_rmult (ds_d4mL ds_d4mM ds_d4mN : Nats):
  add_dist_rmult_spec ds_d4mL ds_d4mM ds_d4mN.
Proof.
  destruct ds_d4mL as [ds_d4mL ds_d4mL_p].
  destruct ds_d4mM as [ds_d4mM ds_d4mM_p].
  destruct ds_d4mN as [ds_d4mN ds_d4mN_p].
  try revert ds_d4mN_p; generalize dependent ds_d4mN;
  try revert ds_d4mM_p; generalize dependent ds_d4mM;
  induction ds_d4mL as [m IH_m|];
  intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (add_res : Nats_u),
             add_rel ds_d4mL ds_d4mM add_res
             ∧ ∃ (mult_res : Nats_u),
               mult_rel add_res ds_d4mN mult_res
               ∧ ∃ (mult_res_2 : Nats_u),
                 mult_rel ds_d4mM ds_d4mN mult_res_2
                 ∧ ∃ (mult_res_3 : Nats_u),
                   mult_rel ds_d4mL ds_d4mN mult_res_3
                   ∧ ∃ (add_res_2 : Nats_u), add_rel mult_res_3 mult_res_2 add_res_2 ∧ mult_res == add_res_2)
            (let _: ∃ (add_res : Nats_u),
                    add_rel
                    ⌊ mult
                      (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver))
                      (exist (λ (ds_d4mN : Nats_u), Nats_wf ds_d4mN ∧ True) ds_d4mN ltac:(solver)) ⌋
                    ⌊ mult
                      (exist (λ (ds_d4mM : Nats_u), Nats_wf ds_d4mM ∧ True) ds_d4mM ltac:(solver))
                      (exist (λ (ds_d4mN : Nats_u), Nats_wf ds_d4mN ∧ True) ds_d4mN ltac:(solver)) ⌋
                    add_res
                    ∧ ∃ (add_res_2 : Nats_u),
                      add_rel ds_d4mN add_res add_res_2
                      ∧ ∃ (add_res_3 : Nats_u),
                        add_rel
                        ds_d4mN
                        ⌊ mult
                          (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver))
                          (exist (λ (ds_d4mN : Nats_u), Nats_wf ds_d4mN ∧ True) ds_d4mN ltac:(solver)) ⌋
                        add_res_3
                        ∧ ∃ (add_res_4 : Nats_u),
                          add_rel
                          add_res_3
                          ⌊ mult
                            (exist (λ (ds_d4mM : Nats_u), Nats_wf ds_d4mM ∧ True) ds_d4mM ltac:(solver))
                            (exist (λ (ds_d4mN : Nats_u), Nats_wf ds_d4mN ∧ True) ds_d4mN ltac:(solver)) ⌋
                          add_res_4
                          ∧ add_res_2 == add_res_4 :=
             ⌈ add_assoc
               (exist (λ (ds_d4mN : Nats_u), Nats_wf ds_d4mN ∧ True) ds_d4mN ltac:(solver))
               (mult
                (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver))
                (exist (λ (ds_d4mN : Nats_u), Nats_wf ds_d4mN ∧ True) ds_d4mN ltac:(solver)))
               (mult
                (exist (λ (ds_d4mM : Nats_u), Nats_wf ds_d4mM ∧ True) ds_d4mM ltac:(solver))
                (exist (λ (ds_d4mN : Nats_u), Nats_wf ds_d4mN ∧ True) ds_d4mN ltac:(solver))) ⌉ in
             IH_m
             ltac:(try clear IH_m; solver)
             ds_d4mM
             ltac:(try clear IH_m; solver)
             ds_d4mN
             ltac:(try clear IH_m; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (add_res : Nats_u),
             add_rel ds_d4mL ds_d4mM add_res
             ∧ ∃ (mult_res : Nats_u),
               mult_rel add_res ds_d4mN mult_res
               ∧ ∃ (mult_res_2 : Nats_u),
                 mult_rel ds_d4mM ds_d4mN mult_res_2
                 ∧ ∃ (mult_res_3 : Nats_u),
                   mult_rel ds_d4mL ds_d4mN mult_res_3
                   ∧ ∃ (add_res_2 : Nats_u), add_rel mult_res_3 mult_res_2 add_res_2 ∧ mult_res == add_res_2)
            (# unit)
            ltac:(solver)).
Qed.

Definition one_spec : Type :=
  Nats.

#[global] Hint Unfold one_spec: lia_unfold.

Definition one : one_spec.
Proof.
  refine (Suc Zero).
Defined.

Definition sub_spec
  (ds_d4lZ : Nats)
  (ds_d4m0 : {ds_d4m0: Nats_u | Nats_wf ds_d4m0
                                ∧ ∃ (geqN_res : bool), geqN_rel ⌊ ds_d4lZ ⌋ ds_d4m0 geqN_res ∧ is_true geqN_res}):
  Type :=
  {o: Nats_u | Nats_wf o ∧ (o ≠ Zero_u ↔ ⌊ ds_d4lZ ⌋ ≠ ⌊ ds_d4m0 ⌋)}.

#[global] Hint Unfold sub_spec: lia_unfold.

Definition sub
  (ds_d4lZ : Nats)
  (ds_d4m0 : {ds_d4m0: Nats_u | Nats_wf ds_d4m0
                                ∧ ∃ (geqN_res : bool), geqN_rel ⌊ ds_d4lZ ⌋ ds_d4m0 geqN_res ∧ is_true geqN_res}):
  sub_spec ds_d4lZ ds_d4m0.
Proof.
  destruct ds_d4lZ as [ds_d4lZ ds_d4lZ_p].
  destruct ds_d4m0 as [ds_d4m0 ds_d4m0_p].
  try revert ds_d4m0_p; generalize dependent ds_d4m0; induction ds_d4lZ as [m IH_m|]; intros.
  - destruct ds_d4m0 as [n|].
    + refine (subsumptionCast
              Nats_u
              (λ (o : Nats_u), Nats_wf o ∧ (o ≠ Zero_u ↔ ds_d4lZ ≠ ds_d4m0))
              (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver))
              ltac:(solver)).
    + refine (subsumptionCast
              Nats_u
              (λ (o : Nats_u), Nats_wf o ∧ (o ≠ Zero_u ↔ ds_d4lZ ≠ ds_d4m0))
              (Suc (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver)))
              ltac:(solver)).
  - destruct ds_d4m0 as [lq_anf7205759403792810483|].
    + intros; exfalso; solver.
    + refine (subsumptionCast
              Nats_u
              (λ (o : Nats_u), Nats_wf o ∧ (o ≠ Zero_u ↔ ds_d4lZ ≠ ds_d4m0))
              Zero
              ltac:(solver)).
Defined.

Inductive sub_rel: Nats_u → Nats_u → Nats_u → Prop :=
  | sub_Zero_Zero: sub_rel Zero_u Zero_u Zero_u
  | sub_Suc_Zero: ∀ m, sub_rel (Suc_u m) Zero_u (Suc_u m)
  | sub_Suc_Suc: ∀ m n (sub_res : Nats_u), sub_rel m n sub_res → sub_rel (Suc_u m) (Suc_u n) sub_res.

#[global] Hint Constructors sub_rel: core_hint_db.

#[global] Instance sub_lookup_rel: dictionary rel sub := { lookup' := sub_rel }.

#[global] Instance sub_getF: getFunc sub_rel := { getF' := sub }.

Theorem sub_rel_funct [ds_d4lZ ds_d4m0 : Nats_u]:
  ∀ (o o' : Nats_u), sub_rel ds_d4lZ ds_d4m0 o → (sub_rel ds_d4lZ ds_d4m0 o' → o = o').
Proof.
  try revert ds_d4m0_p; generalize dependent ds_d4m0; induction ds_d4lZ as [m IH_m|]; intros;
  [destruct ds_d4m0 as [n|] | destruct ds_d4m0 as [lq_anf7205759403792810483|]];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve sub_rel_funct: f_rel_funct_db.

Theorem sub_Zero_Zero_lem sub_Zero_Zero_lem_res:
  sub_rel Zero_u Zero_u sub_Zero_Zero_lem_res ↔ sub_Zero_Zero_lem_res == Zero_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite sub_Zero_Zero_lem: f_rel_back.

Theorem sub_Suc_Zero_lem m sub_Suc_Zero_lem_res:
  sub_rel (Suc_u m) Zero_u sub_Suc_Zero_lem_res ↔ sub_Suc_Zero_lem_res == Suc_u m.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite sub_Suc_Zero_lem: f_rel_back.

Theorem sub_Suc_Suc_lem m n sub_Suc_Suc_lem_res:
  sub_rel (Suc_u m) (Suc_u n) sub_Suc_Suc_lem_res
  ↔ ∃ (sub_res : Nats_u), sub_rel m n sub_res ∧ sub_Suc_Suc_lem_res == sub_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite sub_Suc_Suc_lem: f_rel_back.

Theorem sub_rel_ex
  (ds_d4lZ : Nats_u)
  (ds_d4lZ_p : Nats_wf ds_d4lZ ∧ True)
  (ds_d4m0 : Nats_u)
  (ds_d4m0_p : Nats_wf ds_d4m0
               ∧ ∃ (geqN_res : bool), geqN_rel ds_d4lZ ds_d4m0 geqN_res ∧ is_true geqN_res):
  sub_rel ds_d4lZ ds_d4m0 ⌊ sub (exist _ ds_d4lZ ds_d4lZ_p) (exist _ ds_d4m0 ds_d4m0_p) -⌋.
Proof.
  Opaque sub.
  existence_lemma_pre sub;
  try revert ds_d4m0_p; generalize dependent ds_d4m0; induction ds_d4lZ as [m IH_m|]; intros;
  [destruct ds_d4m0 as [n|];
   [fix_notations;
    pose proof (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver)) as IH_14792487;
    try clear IH_m |
    fix_notations] |
   destruct ds_d4m0 as [lq_anf7205759403792810483|];
   [ | fix_notations]];
  simpl in *.
  Transparent sub.
  all: (existence_lemma_quicksolve sub; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve sub_rel_ex: rel_ax_db.

#[global] Opaque sub.

Theorem sub__sub_rel_rw
  (ds_d4lZ : Nats_u)
  (ds_d4lZ_p : Nats_wf ds_d4lZ ∧ True)
  (ds_d4m0 : Nats_u)
  (ds_d4m0_p : Nats_wf ds_d4m0
               ∧ ∃ (geqN_res : bool), geqN_rel ds_d4lZ ds_d4m0 geqN_res ∧ is_true geqN_res)
  (o : Nats_u):
  ⌊ sub (exist _ ds_d4lZ ds_d4lZ_p) (exist _ ds_d4m0 ds_d4m0_p) -⌋ = o ↔ sub_rel ds_d4lZ ds_d4m0 o.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite sub__sub_rel_rw: f_rel_funct_db.

#[global] Hint Resolve sub__sub_rel_rw: rel_ax_db.

#[global] Instance sub_lookup_rw: dictionary rwLem sub := { lookup' := sub__sub_rel_rw }.

Theorem sub__sub_rel
  (ds_d4lZ : Nats)
  (ds_d4m0 : {ds_d4m0: Nats_u | Nats_wf ds_d4m0
                                ∧ ∃ (geqN_res : bool), geqN_rel ⌊ ds_d4lZ ⌋ ds_d4m0 geqN_res ∧ is_true geqN_res})
  (o : Nats_u):
  ⌊ sub ds_d4lZ ds_d4m0 -⌋ = o ↔ sub_rel ⌊ ds_d4lZ ⌋ ⌊ ds_d4m0 ⌋ o.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite sub__sub_rel: f_rel_funct_db.

Theorem sub__sub_rel'
  (ds_d4lZ_u ds_d4m0_u : Nats_u)
  (ds_d4lZ : Nats)
  (ds_d4m0 : {ds_d4m0: Nats_u | Nats_wf ds_d4m0
                                ∧ ∃ (geqN_res : bool), geqN_rel ⌊ ds_d4lZ ⌋ ds_d4m0 geqN_res ∧ is_true geqN_res})
  (o : Nats_u):
  ds_d4lZ_u = ⌊ ds_d4lZ ⌋
  → (ds_d4m0_u = ⌊ ds_d4m0 ⌋ → ⌊ sub ds_d4lZ ds_d4m0 -⌋ = o ↔ sub_rel ds_d4lZ_u ds_d4m0_u o).
Proof.
  intros -> ->. refine (sub__sub_rel ds_d4lZ ds_d4m0 o).
Qed.

#[global] Hint Resolve sub__sub_rel': f_rel_funct_db.

Theorem sub_rel_mk
  (ds_d4lZ : Nats_u)
  (ds_d4lZ_p : Nats_wf ds_d4lZ ∧ True)
  (ds_d4m0 : Nats_u)
  (ds_d4m0_p : Nats_wf ds_d4m0
               ∧ ∃ (geqN_res : bool), geqN_rel ds_d4lZ ds_d4m0 geqN_res ∧ is_true geqN_res):
  {o: _ | sub_rel ds_d4lZ ds_d4m0 o}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ o, sub_rel ds_d4lZ ds_d4m0 o)
          (sub (exist _ ds_d4lZ ds_d4lZ_p) (exist _ ds_d4m0 ds_d4m0_p))
          _);
  rewrite <- sub__sub_rel';
  quicksolve.
Qed.

#[global] Hint Resolve sub_rel_mk: f_rel_funct_db.

#[global] Instance sub_pack:
  @Pack
  (Nats
   ::RT λ (ds_d4lZ : Nats),
        {ds_d4m0: Nats_u | Nats_wf ds_d4m0
                           ∧ ∃ (geqN_res : bool), geqN_rel ⌊ ds_d4lZ ⌋ ds_d4m0 geqN_res ∧ is_true geqN_res}
        ::RT λ (ds_d4m0 : {ds_d4m0: Nats_u | Nats_wf ds_d4m0
                                             ∧ ∃ (geqN_res : bool),
                                               geqN_rel ⌊ ds_d4lZ ⌋ ds_d4m0 geqN_res ∧ is_true geqN_res}),
             nilRT)
  (Nats_u ::UT (Nats_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((Nats
  ::RT λ (ds_d4lZ : Nats),
       {ds_d4m0: Nats_u | Nats_wf ds_d4m0
                          ∧ ∃ (geqN_res : bool),
                            geqN_rel ⌊ ds_d4lZ ⌋ ds_d4m0 geqN_res ∧ is_true geqN_res}
       ::RT λ (ds_d4m0 : {ds_d4m0: Nats_u | Nats_wf ds_d4m0
                                            ∧ ∃ (geqN_res : bool),
                                              geqN_rel ⌊ ds_d4lZ ⌋ ds_d4m0 geqN_res
                                              ∧ is_true geqN_res}),
            nilRT)) ((Nats_u ::UT (Nats_u ::UT nilUT))))
  Nats_u
  (λ (x_24742908 : ArgList (Nats
                            ::RT λ (ds_d4lZ : Nats),
                                 {ds_d4m0: Nats_u | Nats_wf ds_d4m0
                                                    ∧ ∃ (geqN_res : bool),
                                                      geqN_rel ⌊ ds_d4lZ ⌋ ds_d4m0 geqN_res ∧ is_true geqN_res}
                                 ::RT λ (ds_d4m0 : {ds_d4m0: Nats_u | Nats_wf ds_d4m0
                                                                      ∧ ∃ (geqN_res : bool),
                                                                        geqN_rel ⌊ ds_d4lZ ⌋ ds_d4m0 geqN_res
                                                                        ∧ is_true geqN_res}),
                                      nilRT))
     (v_x_24742908 : Nats_u),
   ltac:(flattenP (λ (ds_d4lZ : Nats)
   (ds_d4m0 : {ds_d4m0: Nats_u | Nats_wf ds_d4m0
                                 ∧ ∃ (geqN_res : bool),
                                   geqN_rel ⌊ ds_d4lZ ⌋ ds_d4m0 geqN_res ∧ is_true geqN_res})
   (o : Nats_u),
 Nats_wf o ∧ (o ≠ Zero_u ↔ ⌊ ds_d4lZ ⌋ ≠ ⌊ ds_d4m0 ⌋)) x_24742908 v_x_24742908)).
Proof.
  buildPackG sub sub_rel sub__sub_rel sub_rel_funct.
Defined.

#[global] Instance sub_upack: @uPack (Nats_u ::UT (Nats_u ::UT nilUT)) Nats_u.
Proof.
  buildUPackG sub_rel sub_rel_funct.
Defined.

Definition add_sub_spec (ds_d4mt ds_d4mu : Nats): Type :=
  {{∃ (add_res : Nats_u),
    add_rel ⌊ ds_d4mt ⌋ ⌊ ds_d4mu ⌋ add_res
    ∧ ∃ (sub_res : Nats_u), sub_rel add_res ⌊ ds_d4mu ⌋ sub_res ∧ sub_res == ⌊ ds_d4mt ⌋}}.

#[global] Hint Unfold add_sub_spec: lia_unfold.

Theorem add_sub (ds_d4mt ds_d4mu : Nats): add_sub_spec ds_d4mt ds_d4mu.
Proof.
  destruct ds_d4mt as [ds_d4mt ds_d4mt_p].
  destruct ds_d4mu as [ds_d4mu ds_d4mu_p].
  destruct ds_d4mt as [m|].
  - induction ds_d4mu as [lq_anf7205759403792810453 IH_lq_anf7205759403792810453|].
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∃ (add_res : Nats_u),
               add_rel ds_d4mt ds_d4mu add_res
               ∧ ∃ (sub_res : Nats_u), sub_rel add_res ds_d4mu sub_res ∧ sub_res == ds_d4mt)
              (let _: ∃ (add_res : Nats_u),
                      add_rel (Suc_u m) lq_anf7205759403792810453 add_res
                      ∧ ∃ (sub_res : Nats_u), sub_rel add_res lq_anf7205759403792810453 sub_res ∧ sub_res == Suc_u m :=
               ⌈ IH_lq_anf7205759403792810453 ltac:(try clear IH_lq_anf7205759403792810453; solver) ⌉ in
               add_suc_r
               (Suc (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver)))
               (exist (λ (n : Nats_u), Nats_wf n ∧ True) lq_anf7205759403792810453 ltac:(solver)))
              ltac:(solver)).
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∃ (add_res : Nats_u),
               add_rel ds_d4mt ds_d4mu add_res
               ∧ ∃ (sub_res : Nats_u), sub_rel add_res ds_d4mu sub_res ∧ sub_res == ds_d4mt)
              (add_zero_r (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver)))
              ltac:(solver)).
  - induction ds_d4mu as [lq_anf7205759403792810445 IH_lq_anf7205759403792810445|].
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∃ (add_res : Nats_u),
               add_rel ds_d4mt ds_d4mu add_res
               ∧ ∃ (sub_res : Nats_u), sub_rel add_res ds_d4mu sub_res ∧ sub_res == ds_d4mt)
              (let _: ∃ (add_res : Nats_u),
                      add_rel Zero_u lq_anf7205759403792810445 add_res
                      ∧ ∃ (sub_res : Nats_u), sub_rel add_res lq_anf7205759403792810445 sub_res ∧ sub_res == Zero_u :=
               ⌈ IH_lq_anf7205759403792810445 ltac:(try clear IH_lq_anf7205759403792810445; solver) ⌉ in
               add_suc_r Zero (exist (λ (n : Nats_u), Nats_wf n ∧ True) lq_anf7205759403792810445 ltac:(solver)))
              ltac:(solver)).
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∃ (add_res : Nats_u),
               add_rel ds_d4mt ds_d4mu add_res
               ∧ ∃ (sub_res : Nats_u), sub_rel add_res ds_d4mu sub_res ∧ sub_res == ds_d4mt)
              (# unit)
              ltac:(solver)).
Qed.

Definition sub_self_spec (ds_d4lT ds_d4lU : Nats): Type :=
  {{∃ (eqN_res : bool), eqN_rel ⌊ ds_d4lT ⌋ ⌊ ds_d4lU ⌋ eqN_res ∧ is_true eqN_res
    → ∃ (sub_res : Nats_u), sub_rel ⌊ ds_d4lT ⌋ ⌊ ds_d4lU ⌋ sub_res ∧ sub_res == Zero_u}}.

#[global] Hint Unfold sub_self_spec: lia_unfold.

Theorem sub_self (ds_d4lT ds_d4lU : Nats): sub_self_spec ds_d4lT ds_d4lU.
Proof.
  destruct ds_d4lT as [ds_d4lT ds_d4lT_p].
  destruct ds_d4lU as [ds_d4lU ds_d4lU_p].
  try revert ds_d4lU_p; generalize dependent ds_d4lU; induction ds_d4lT as [m IH_m|]; intros.
  - destruct ds_d4lU as [n|].
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∃ (eqN_res : bool), eqN_rel ds_d4lT ds_d4lU eqN_res ∧ is_true eqN_res
               → ∃ (sub_res : Nats_u), sub_rel ds_d4lT ds_d4lU sub_res ∧ sub_res == Zero_u)
              (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver))
              ltac:(solver)).
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∃ (eqN_res : bool), eqN_rel ds_d4lT ds_d4lU eqN_res ∧ is_true eqN_res
               → ∃ (sub_res : Nats_u), sub_rel ds_d4lT ds_d4lU sub_res ∧ sub_res == Zero_u)
              (# unit)
              ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (eqN_res : bool), eqN_rel ds_d4lT ds_d4lU eqN_res ∧ is_true eqN_res
             → ∃ (sub_res : Nats_u), sub_rel ds_d4lT ds_d4lU sub_res ∧ sub_res == Zero_u)
            (# unit)
            ltac:(solver)).
Qed.

Definition two_spec : Type :=
  Nats.

#[global] Hint Unfold two_spec: lia_unfold.

Definition two : two_spec.
Proof.
  refine (Suc one).
Defined.
