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

Definition add_spec (ds_d4mE n : Nats): Type :=
  Nats.

#[global] Hint Unfold add_spec: lia_unfold.

Definition add (ds_d4mE n : Nats): add_spec ds_d4mE n.
Proof.
  destruct ds_d4mE as [ds_d4mE ds_d4mE_p].
  destruct n as [n n_p].
  try revert n_p; generalize dependent n; induction ds_d4mE as [m IH_m|]; intros.
  - refine (Suc (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver))).
  - refine (exist (λ (n : Nats_u), Nats_wf n ∧ True) n ltac:(solver)).
Defined.

Inductive add_rel: Nats_u → Nats_u → Nats_u → Prop :=
  | add_Suc_x: ∀ m n (add_res : Nats_u), add_rel m n add_res → add_rel (Suc_u m) n (Suc_u add_res)
  | add_Zero_x: ∀ n, add_rel Zero_u n n.

#[global] Hint Constructors add_rel: core_hint_db.

#[global] Instance add_lookup_rel: dictionary rel add := { lookup' := add_rel }.

#[global] Instance add_getF: getFunc add_rel := { getF' := add }.

Theorem add_rel_funct [ds_d4mE n : Nats_u]:
  ∀ (VV VV' : Nats_u), add_rel ds_d4mE n VV → (add_rel ds_d4mE n VV' → VV = VV').
Proof.
  try revert n_p; generalize dependent n; induction ds_d4mE as [m IH_m|]; intros;
  rel_functionhood_body.
Qed.

#[global] Hint Resolve add_rel_funct: f_rel_funct_db.

Theorem add_Suc_x_lem m n add_Suc_x_lem_res:
  add_rel (Suc_u m) n add_Suc_x_lem_res
  ↔ ∃ (add_res : Nats_u), add_rel m n add_res ∧ add_Suc_x_lem_res == Suc_u add_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite add_Suc_x_lem: f_rel_back.

Theorem add_Zero_x_lem n add_Zero_x_lem_res:
  add_rel Zero_u n add_Zero_x_lem_res ↔ add_Zero_x_lem_res == n.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite add_Zero_x_lem: f_rel_back.

Theorem add_rel_ex
  (ds_d4mE : Nats_u) (ds_d4mE_p : Nats_wf ds_d4mE ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True):
  add_rel ds_d4mE n ⌊ add (exist _ ds_d4mE ds_d4mE_p) (exist _ n n_p) -⌋.
Proof.
  Opaque add.
  existence_lemma_pre add;
  try revert n_p; generalize dependent n; induction ds_d4mE as [m IH_m|]; intros;
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
  (ds_d4mE : Nats_u)
  (ds_d4mE_p : Nats_wf ds_d4mE ∧ True)
  (n : Nats_u)
  (n_p : Nats_wf n ∧ True)
  (VV : Nats_u):
  ⌊ add (exist _ ds_d4mE ds_d4mE_p) (exist _ n n_p) -⌋ = VV ↔ add_rel ds_d4mE n VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite add__add_rel_rw: f_rel_funct_db.

#[global] Hint Resolve add__add_rel_rw: rel_ax_db.

#[global] Instance add_lookup_rw: dictionary rwLem add := { lookup' := add__add_rel_rw }.

Theorem add__add_rel (ds_d4mE n : Nats) (VV : Nats_u):
  ⌊ add ds_d4mE n -⌋ = VV ↔ add_rel ⌊ ds_d4mE ⌋ ⌊ n ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite add__add_rel: f_rel_funct_db.

Theorem add__add_rel' (ds_d4mE_u n_u : Nats_u) (ds_d4mE n : Nats) (VV : Nats_u):
  ds_d4mE_u = ⌊ ds_d4mE ⌋ → (n_u = ⌊ n ⌋ → ⌊ add ds_d4mE n -⌋ = VV ↔ add_rel ds_d4mE_u n_u VV).
Proof.
  intros -> ->. refine (add__add_rel ds_d4mE n VV).
Qed.

#[global] Hint Resolve add__add_rel': f_rel_funct_db.

Theorem add_rel_mk
  (ds_d4mE : Nats_u) (ds_d4mE_p : Nats_wf ds_d4mE ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True):
  {VV: _ | add_rel ds_d4mE n VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, add_rel ds_d4mE n VV)
          (add (exist _ ds_d4mE ds_d4mE_p) (exist _ n n_p))
          _);
  rewrite <- add__add_rel';
  quicksolve.
Qed.

#[global] Hint Resolve add_rel_mk: f_rel_funct_db.

#[global] Instance add_pack:
  @Pack
  (Nats ::RT λ (ds_d4mE : Nats), Nats ::RT λ (n : Nats), nilRT)
  (Nats_u ::UT (Nats_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((Nats ::RT λ (ds_d4mE : Nats), Nats ::RT λ (n : Nats), nilRT)) ((Nats_u ::UT (Nats_u ::UT nilUT))))
  Nats_u
  (λ (x_44855413 : ArgList (Nats ::RT λ (ds_d4mE : Nats), Nats ::RT λ (n : Nats), nilRT))
     (v_x_44855413 : Nats_u),
   ltac:(flattenP (λ (ds_d4mE n : Nats) (VV : Nats_u), Nats_wf VV ∧ True) x_44855413 v_x_44855413)).
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

Definition add_assoc_spec (ds_d4my ds_d4mz ds_d4mA : Nats): Type :=
  {{∃ (add_res : Nats_u),
    add_rel ⌊ ds_d4mz ⌋ ⌊ ds_d4mA ⌋ add_res
    ∧ ∃ (add_res_2 : Nats_u),
      add_rel ⌊ ds_d4my ⌋ add_res add_res_2
      ∧ ∃ (add_res_3 : Nats_u),
        add_rel ⌊ ds_d4my ⌋ ⌊ ds_d4mz ⌋ add_res_3
        ∧ ∃ (add_res_4 : Nats_u), add_rel add_res_3 ⌊ ds_d4mA ⌋ add_res_4 ∧ add_res_2 == add_res_4}}.

#[global] Hint Unfold add_assoc_spec: lia_unfold.

Theorem add_assoc (ds_d4my ds_d4mz ds_d4mA : Nats): add_assoc_spec ds_d4my ds_d4mz ds_d4mA.
Proof.
  destruct ds_d4my as [ds_d4my ds_d4my_p].
  destruct ds_d4mz as [ds_d4mz ds_d4mz_p].
  destruct ds_d4mA as [ds_d4mA ds_d4mA_p].
  try revert ds_d4mA_p; generalize dependent ds_d4mA;
  try revert ds_d4mz_p; generalize dependent ds_d4mz;
  induction ds_d4my as [m IH_m|];
  intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (add_res : Nats_u),
             add_rel ds_d4mz ds_d4mA add_res
             ∧ ∃ (add_res_2 : Nats_u),
               add_rel (Suc_u m) add_res add_res_2
               ∧ ∃ (add_res_3 : Nats_u),
                 add_rel (Suc_u m) ds_d4mz add_res_3
                 ∧ ∃ (add_res_4 : Nats_u), add_rel add_res_3 ds_d4mA add_res_4 ∧ add_res_2 == add_res_4)
            (IH_m
             ltac:(try clear IH_m; solver)
             ds_d4mz
             ltac:(try clear IH_m; solver)
             ds_d4mA
             ltac:(try clear IH_m; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (add_res : Nats_u),
             add_rel ds_d4mz ds_d4mA add_res
             ∧ ∃ (add_res_2 : Nats_u),
               add_rel Zero_u add_res add_res_2
               ∧ ∃ (add_res_3 : Nats_u),
                 add_rel Zero_u ds_d4mz add_res_3
                 ∧ ∃ (add_res_4 : Nats_u), add_rel add_res_3 ds_d4mA add_res_4 ∧ add_res_2 == add_res_4)
            (# unit)
            ltac:(solver)).
Qed.

Definition add_suc_r_spec (ds_d4mn ds_d4mo : Nats): Type :=
  {{∃ (add_res : Nats_u),
    add_rel ⌊ ds_d4mn ⌋ ⌊ ds_d4mo ⌋ add_res
    ∧ ∃ (add_res_2 : Nats_u),
      add_rel ⌊ ds_d4mn ⌋ (Suc_u ⌊ ds_d4mo ⌋) add_res_2 ∧ Suc_u add_res == add_res_2}}.

#[global] Hint Unfold add_suc_r_spec: lia_unfold.

Theorem add_suc_r (ds_d4mn ds_d4mo : Nats): add_suc_r_spec ds_d4mn ds_d4mo.
Proof.
  destruct ds_d4mn as [ds_d4mn ds_d4mn_p].
  destruct ds_d4mo as [ds_d4mo ds_d4mo_p].
  try revert ds_d4mo_p; generalize dependent ds_d4mo; induction ds_d4mn as [m IH_m|]; intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (add_res : Nats_u),
             add_rel (Suc_u m) ds_d4mo add_res
             ∧ ∃ (add_res_2 : Nats_u), add_rel (Suc_u m) (Suc_u ds_d4mo) add_res_2 ∧ Suc_u add_res == add_res_2)
            (IH_m ltac:(try clear IH_m; solver) ds_d4mo ltac:(try clear IH_m; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (add_res : Nats_u),
             add_rel Zero_u ds_d4mo add_res
             ∧ ∃ (add_res_2 : Nats_u), add_rel Zero_u (Suc_u ds_d4mo) add_res_2 ∧ Suc_u add_res == add_res_2)
            (# unit)
            ltac:(solver)).
Qed.

Definition add_zero_l_spec (ds_d4mB : Nats): Type :=
  {{∃ (add_res : Nats_u), add_rel Zero_u ⌊ ds_d4mB ⌋ add_res ∧ add_res == ⌊ ds_d4mB ⌋}}.

#[global] Hint Unfold add_zero_l_spec: lia_unfold.

Theorem add_zero_l (ds_d4mB : Nats): add_zero_l_spec ds_d4mB.
Proof.
  destruct ds_d4mB as [ds_d4mB ds_d4mB_p].
  induction ds_d4mB as [n IH_n|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (add_res : Nats_u), add_rel Zero_u (Suc_u n) add_res ∧ add_res == Suc_u n)
            (IH_n ltac:(try clear IH_n; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (add_res : Nats_u), add_rel Zero_u Zero_u add_res ∧ add_res == Zero_u)
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

Definition add_zero_r_spec (ds_d4mp : Nats): Type :=
  {{∃ (add_res : Nats_u), add_rel ⌊ ds_d4mp ⌋ Zero_u add_res ∧ add_res == ⌊ ds_d4mp ⌋}}.

#[global] Hint Unfold add_zero_r_spec: lia_unfold.

Theorem add_zero_r (ds_d4mp : Nats): add_zero_r_spec ds_d4mp.
Proof.
  destruct ds_d4mp as [ds_d4mp ds_d4mp_p].
  induction ds_d4mp as [n IH_n|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (add_res : Nats_u), add_rel (Suc_u n) Zero_u add_res ∧ add_res == Suc_u n)
            (IH_n ltac:(try clear IH_n; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (add_res : Nats_u), add_rel Zero_u Zero_u add_res ∧ add_res == Zero_u)
            (# unit)
            ltac:(solver)).
Qed.

Definition eqN_spec (ds_d4m1 ds_d4m2 : Nats): Type :=
  Bool.

#[global] Hint Unfold eqN_spec: lia_unfold.

Definition eqN (ds_d4m1 ds_d4m2 : Nats): eqN_spec ds_d4m1 ds_d4m2.
Proof.
  destruct ds_d4m1 as [ds_d4m1 ds_d4m1_p].
  destruct ds_d4m2 as [ds_d4m2 ds_d4m2_p].
  try revert ds_d4m2_p; generalize dependent ds_d4m2; induction ds_d4m1 as [m IH_m|]; intros.
  - destruct ds_d4m2 as [n|].
    + refine (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver)).
    + refine (# false).
  - destruct ds_d4m2 as [lq_anf7205759403792810464|].
    + refine (# false).
    + refine (# true).
Defined.

Inductive eqN_rel: Nats_u → Nats_u → bool → Prop :=
  | eqN_Suc_Suc: ∀ m n (eqN_res : bool), eqN_rel m n eqN_res → eqN_rel (Suc_u m) (Suc_u n) eqN_res
  | eqN_Suc_Zero: ∀ m, eqN_rel (Suc_u m) Zero_u false
  | eqN_Zero_Suc: ∀ lq_anf7205759403792810464, eqN_rel Zero_u (Suc_u lq_anf7205759403792810464) false
  | eqN_Zero_Zero: eqN_rel Zero_u Zero_u true.

#[global] Hint Constructors eqN_rel: core_hint_db.

#[global] Instance eqN_lookup_rel: dictionary rel eqN := { lookup' := eqN_rel }.

#[global] Instance eqN_getF: getFunc eqN_rel := { getF' := eqN }.

Theorem eqN_rel_funct [ds_d4m1 ds_d4m2 : Nats_u]:
  ∀ (VV VV' : bool), eqN_rel ds_d4m1 ds_d4m2 VV → (eqN_rel ds_d4m1 ds_d4m2 VV' → VV = VV').
Proof.
  try revert ds_d4m2_p; generalize dependent ds_d4m2; induction ds_d4m1 as [m IH_m|]; intros;
  [destruct ds_d4m2 as [n|] | destruct ds_d4m2 as [lq_anf7205759403792810464|]];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve eqN_rel_funct: f_rel_funct_db.

Theorem eqN_Suc_Suc_lem m n eqN_Suc_Suc_lem_res:
  eqN_rel (Suc_u m) (Suc_u n) eqN_Suc_Suc_lem_res
  ↔ ∃ (eqN_res : bool), eqN_rel m n eqN_res ∧ eqN_Suc_Suc_lem_res == eqN_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite eqN_Suc_Suc_lem: f_rel_back.

Theorem eqN_Suc_Zero_lem m eqN_Suc_Zero_lem_res:
  eqN_rel (Suc_u m) Zero_u eqN_Suc_Zero_lem_res ↔ eqN_Suc_Zero_lem_res == false.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite eqN_Suc_Zero_lem: f_rel_back.

Theorem eqN_Zero_Suc_lem lq_anf7205759403792810464 eqN_Zero_Suc_lem_res:
  eqN_rel Zero_u (Suc_u lq_anf7205759403792810464) eqN_Zero_Suc_lem_res
  ↔ eqN_Zero_Suc_lem_res == false.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite eqN_Zero_Suc_lem: f_rel_back.

Theorem eqN_Zero_Zero_lem eqN_Zero_Zero_lem_res:
  eqN_rel Zero_u Zero_u eqN_Zero_Zero_lem_res ↔ eqN_Zero_Zero_lem_res == true.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite eqN_Zero_Zero_lem: f_rel_back.

Theorem eqN_rel_ex
  (ds_d4m1 : Nats_u)
  (ds_d4m1_p : Nats_wf ds_d4m1 ∧ True)
  (ds_d4m2 : Nats_u)
  (ds_d4m2_p : Nats_wf ds_d4m2 ∧ True):
  eqN_rel ds_d4m1 ds_d4m2 ⌊ eqN (exist _ ds_d4m1 ds_d4m1_p) (exist _ ds_d4m2 ds_d4m2_p) -⌋.
Proof.
  Opaque eqN.
  existence_lemma_pre eqN;
  try revert ds_d4m2_p; generalize dependent ds_d4m2; induction ds_d4m1 as [m IH_m|]; intros;
  [destruct ds_d4m2 as [n|];
   [fix_notations;
    pose proof (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver)) as IH_14792487;
    try clear IH_m |
    fix_notations] |
   destruct ds_d4m2 as [lq_anf7205759403792810464|];
   [fix_notations | fix_notations]];
  simpl in *.
  Transparent eqN.
  all: (existence_lemma_quicksolve eqN; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve eqN_rel_ex: rel_ax_db.

#[global] Opaque eqN.

Theorem eqN__eqN_rel_rw
  (ds_d4m1 : Nats_u)
  (ds_d4m1_p : Nats_wf ds_d4m1 ∧ True)
  (ds_d4m2 : Nats_u)
  (ds_d4m2_p : Nats_wf ds_d4m2 ∧ True)
  (VV : bool):
  ⌊ eqN (exist _ ds_d4m1 ds_d4m1_p) (exist _ ds_d4m2 ds_d4m2_p) -⌋ = VV ↔ eqN_rel ds_d4m1 ds_d4m2 VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite eqN__eqN_rel_rw: f_rel_funct_db.

#[global] Hint Resolve eqN__eqN_rel_rw: rel_ax_db.

#[global] Instance eqN_lookup_rw: dictionary rwLem eqN := { lookup' := eqN__eqN_rel_rw }.

Theorem eqN__eqN_rel (ds_d4m1 ds_d4m2 : Nats) (VV : bool):
  ⌊ eqN ds_d4m1 ds_d4m2 -⌋ = VV ↔ eqN_rel ⌊ ds_d4m1 ⌋ ⌊ ds_d4m2 ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite eqN__eqN_rel: f_rel_funct_db.

Theorem eqN__eqN_rel' (ds_d4m1_u ds_d4m2_u : Nats_u) (ds_d4m1 ds_d4m2 : Nats) (VV : bool):
  ds_d4m1_u = ⌊ ds_d4m1 ⌋
  → (ds_d4m2_u = ⌊ ds_d4m2 ⌋ → ⌊ eqN ds_d4m1 ds_d4m2 -⌋ = VV ↔ eqN_rel ds_d4m1_u ds_d4m2_u VV).
Proof.
  intros -> ->. refine (eqN__eqN_rel ds_d4m1 ds_d4m2 VV).
Qed.

#[global] Hint Resolve eqN__eqN_rel': f_rel_funct_db.

Theorem eqN_rel_mk
  (ds_d4m1 : Nats_u)
  (ds_d4m1_p : Nats_wf ds_d4m1 ∧ True)
  (ds_d4m2 : Nats_u)
  (ds_d4m2_p : Nats_wf ds_d4m2 ∧ True):
  {VV: _ | eqN_rel ds_d4m1 ds_d4m2 VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, eqN_rel ds_d4m1 ds_d4m2 VV)
          (eqN (exist _ ds_d4m1 ds_d4m1_p) (exist _ ds_d4m2 ds_d4m2_p))
          _);
  rewrite <- eqN__eqN_rel';
  quicksolve.
Qed.

#[global] Hint Resolve eqN_rel_mk: f_rel_funct_db.

#[global] Instance eqN_pack:
  @Pack
  (Nats ::RT λ (ds_d4m1 : Nats), Nats ::RT λ (ds_d4m2 : Nats), nilRT)
  (Nats_u ::UT (Nats_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((Nats
  ::RT λ (ds_d4m1 : Nats), Nats ::RT λ (ds_d4m2 : Nats), nilRT)) ((Nats_u ::UT (Nats_u ::UT nilUT))))
  bool
  (λ (x_41244053 : ArgList (Nats ::RT λ (ds_d4m1 : Nats), Nats ::RT λ (ds_d4m2 : Nats), nilRT))
     (v_x_41244053 : bool),
   ltac:(flattenP (λ (ds_d4m1 ds_d4m2 : Nats) (VV : bool), True) x_41244053 v_x_41244053)).
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

Definition geqN_spec (ds_d4mg ds_d4mh : Nats): Type :=
  Bool.

#[global] Hint Unfold geqN_spec: lia_unfold.

Definition geqN (ds_d4mg ds_d4mh : Nats): geqN_spec ds_d4mg ds_d4mh.
Proof.
  destruct ds_d4mg as [ds_d4mg ds_d4mg_p].
  destruct ds_d4mh as [ds_d4mh ds_d4mh_p].
  try revert ds_d4mg_p; generalize dependent ds_d4mg;
  induction ds_d4mh as [lq_anf7205759403792810461 IH_lq_anf7205759403792810461|];
  intros.
  - destruct ds_d4mg as [m|].
    + refine (IH_lq_anf7205759403792810461
              ltac:(try clear IH_lq_anf7205759403792810461; solver)
              m
              ltac:(try clear IH_lq_anf7205759403792810461; solver)).
    + refine (# false).
  - refine (# true).
Defined.

Inductive geqN_rel: Nats_u → Nats_u → bool → Prop :=
  | geqN_Suc_Suc: ∀ m lq_anf7205759403792810461 (geqN_res : bool),
                  geqN_rel m lq_anf7205759403792810461 geqN_res
                  → geqN_rel (Suc_u m) (Suc_u lq_anf7205759403792810461) geqN_res
  | geqN_Zero_Suc: ∀ lq_anf7205759403792810461,
                   geqN_rel Zero_u (Suc_u lq_anf7205759403792810461) false
  | geqN_x_Zero: ∀ ds_d4mg, geqN_rel ds_d4mg Zero_u true.

#[global] Hint Constructors geqN_rel: core_hint_db.

#[global] Instance geqN_lookup_rel: dictionary rel geqN := { lookup' := geqN_rel }.

#[global] Instance geqN_getF: getFunc geqN_rel := { getF' := geqN }.

Theorem geqN_rel_funct [ds_d4mg ds_d4mh : Nats_u]:
  ∀ (VV VV' : bool), geqN_rel ds_d4mg ds_d4mh VV → (geqN_rel ds_d4mg ds_d4mh VV' → VV = VV').
Proof.
  try revert ds_d4mg_p; generalize dependent ds_d4mg;
  induction ds_d4mh as [lq_anf7205759403792810461 IH_lq_anf7205759403792810461|];
  intros;
  [destruct ds_d4mg as [m|] |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve geqN_rel_funct: f_rel_funct_db.

Theorem geqN_Suc_Suc_lem lq_anf7205759403792810461 m geqN_Suc_Suc_lem_res:
  geqN_rel (Suc_u m) (Suc_u lq_anf7205759403792810461) geqN_Suc_Suc_lem_res
  ↔ ∃ (geqN_res : bool),
    geqN_rel m lq_anf7205759403792810461 geqN_res ∧ geqN_Suc_Suc_lem_res == geqN_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite geqN_Suc_Suc_lem: f_rel_back.

Theorem geqN_Zero_Suc_lem lq_anf7205759403792810461 geqN_Zero_Suc_lem_res:
  geqN_rel Zero_u (Suc_u lq_anf7205759403792810461) geqN_Zero_Suc_lem_res
  ↔ geqN_Zero_Suc_lem_res == false.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite geqN_Zero_Suc_lem: f_rel_back.

Theorem geqN_x_Zero_lem ds_d4mg geqN_x_Zero_lem_res:
  geqN_rel ds_d4mg Zero_u geqN_x_Zero_lem_res ↔ geqN_x_Zero_lem_res == true.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite geqN_x_Zero_lem: f_rel_back.

Theorem geqN_rel_ex
  (ds_d4mg : Nats_u)
  (ds_d4mg_p : Nats_wf ds_d4mg ∧ True)
  (ds_d4mh : Nats_u)
  (ds_d4mh_p : Nats_wf ds_d4mh ∧ True):
  geqN_rel ds_d4mg ds_d4mh ⌊ geqN (exist _ ds_d4mg ds_d4mg_p) (exist _ ds_d4mh ds_d4mh_p) -⌋.
Proof.
  Opaque geqN.
  existence_lemma_pre geqN;
  try revert ds_d4mg_p; generalize dependent ds_d4mg;
  induction ds_d4mh as [lq_anf7205759403792810461 IH_lq_anf7205759403792810461|];
  intros;
  [destruct ds_d4mg as [m|];
   [fix_notations;
    pose proof (IH_lq_anf7205759403792810461
                ltac:(try clear IH_lq_anf7205759403792810461; solver)
                m
                ltac:(try clear IH_lq_anf7205759403792810461; solver)) as IH_28387485;
    try clear IH_lq_anf7205759403792810461 |
    fix_notations] |
   fix_notations];
  simpl in *.
  Transparent geqN.
  all: (existence_lemma_quicksolve geqN; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve geqN_rel_ex: rel_ax_db.

#[global] Opaque geqN.

Theorem geqN__geqN_rel_rw
  (ds_d4mg : Nats_u)
  (ds_d4mg_p : Nats_wf ds_d4mg ∧ True)
  (ds_d4mh : Nats_u)
  (ds_d4mh_p : Nats_wf ds_d4mh ∧ True)
  (VV : bool):
  ⌊ geqN (exist _ ds_d4mg ds_d4mg_p) (exist _ ds_d4mh ds_d4mh_p) -⌋ = VV
  ↔ geqN_rel ds_d4mg ds_d4mh VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite geqN__geqN_rel_rw: f_rel_funct_db.

#[global] Hint Resolve geqN__geqN_rel_rw: rel_ax_db.

#[global] Instance geqN_lookup_rw: dictionary rwLem geqN := { lookup' := geqN__geqN_rel_rw }.

Theorem geqN__geqN_rel (ds_d4mg ds_d4mh : Nats) (VV : bool):
  ⌊ geqN ds_d4mg ds_d4mh -⌋ = VV ↔ geqN_rel ⌊ ds_d4mg ⌋ ⌊ ds_d4mh ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite geqN__geqN_rel: f_rel_funct_db.

Theorem geqN__geqN_rel' (ds_d4mg_u ds_d4mh_u : Nats_u) (ds_d4mg ds_d4mh : Nats) (VV : bool):
  ds_d4mg_u = ⌊ ds_d4mg ⌋
  → (ds_d4mh_u = ⌊ ds_d4mh ⌋ → ⌊ geqN ds_d4mg ds_d4mh -⌋ = VV ↔ geqN_rel ds_d4mg_u ds_d4mh_u VV).
Proof.
  intros -> ->. refine (geqN__geqN_rel ds_d4mg ds_d4mh VV).
Qed.

#[global] Hint Resolve geqN__geqN_rel': f_rel_funct_db.

Theorem geqN_rel_mk
  (ds_d4mg : Nats_u)
  (ds_d4mg_p : Nats_wf ds_d4mg ∧ True)
  (ds_d4mh : Nats_u)
  (ds_d4mh_p : Nats_wf ds_d4mh ∧ True):
  {VV: _ | geqN_rel ds_d4mg ds_d4mh VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, geqN_rel ds_d4mg ds_d4mh VV)
          (geqN (exist _ ds_d4mg ds_d4mg_p) (exist _ ds_d4mh ds_d4mh_p))
          _);
  rewrite <- geqN__geqN_rel';
  quicksolve.
Qed.

#[global] Hint Resolve geqN_rel_mk: f_rel_funct_db.

#[global] Instance geqN_pack:
  @Pack
  (Nats ::RT λ (ds_d4mg : Nats), Nats ::RT λ (ds_d4mh : Nats), nilRT)
  (Nats_u ::UT (Nats_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((Nats
  ::RT λ (ds_d4mg : Nats), Nats ::RT λ (ds_d4mh : Nats), nilRT)) ((Nats_u ::UT (Nats_u ::UT nilUT))))
  bool
  (λ (x_35960879 : ArgList (Nats ::RT λ (ds_d4mg : Nats), Nats ::RT λ (ds_d4mh : Nats), nilRT))
     (v_x_35960879 : bool),
   ltac:(flattenP (λ (ds_d4mg ds_d4mh : Nats) (VV : bool), True) x_35960879 v_x_35960879)).
Proof.
  buildPackG geqN geqN_rel geqN__geqN_rel geqN_rel_funct.
Defined.

#[global] Instance geqN_upack: @uPack (Nats_u ::UT (Nats_u ::UT nilUT)) bool.
Proof.
  buildUPackG geqN_rel geqN_rel_funct.
Defined.

Definition mult_spec (ds_d4mG ds_d4mH : Nats): Type :=
  Nats.

#[global] Hint Unfold mult_spec: lia_unfold.

Definition mult (ds_d4mG ds_d4mH : Nats): mult_spec ds_d4mG ds_d4mH.
Proof.
  destruct ds_d4mG as [ds_d4mG ds_d4mG_p].
  destruct ds_d4mH as [ds_d4mH ds_d4mH_p].
  try revert ds_d4mH_p; generalize dependent ds_d4mH; induction ds_d4mG as [m IH_m|]; intros.
  - refine (add
            (exist (λ (ds_d4mH : Nats_u), Nats_wf ds_d4mH ∧ True) ds_d4mH ltac:(solver))
            (IH_m ltac:(try clear IH_m; solver) ds_d4mH ltac:(try clear IH_m; solver))).
  - refine Zero.
Defined.

Inductive mult_rel: Nats_u → Nats_u → Nats_u → Prop :=
  | mult_Suc_x: ∀ m ds_d4mH (mult_res : Nats_u),
                mult_rel m ds_d4mH mult_res
                → ∀ (add_res : Nats_u), add_rel ds_d4mH mult_res add_res → mult_rel (Suc_u m) ds_d4mH add_res
  | mult_Zero_x: ∀ ds_d4mH, mult_rel Zero_u ds_d4mH Zero_u.

#[global] Hint Constructors mult_rel: core_hint_db.

#[global] Instance mult_lookup_rel: dictionary rel mult := { lookup' := mult_rel }.

#[global] Instance mult_getF: getFunc mult_rel := { getF' := mult }.

Theorem mult_rel_funct [ds_d4mG ds_d4mH : Nats_u]:
  ∀ (VV VV' : Nats_u), mult_rel ds_d4mG ds_d4mH VV → (mult_rel ds_d4mG ds_d4mH VV' → VV = VV').
Proof.
  try revert ds_d4mH_p; generalize dependent ds_d4mH; induction ds_d4mG as [m IH_m|]; intros;
  rel_functionhood_body.
Qed.

#[global] Hint Resolve mult_rel_funct: f_rel_funct_db.

Theorem mult_Suc_x_lem ds_d4mH m mult_Suc_x_lem_res:
  mult_rel (Suc_u m) ds_d4mH mult_Suc_x_lem_res
  ↔ ∃ (mult_res : Nats_u),
    mult_rel m ds_d4mH mult_res
    ∧ ∃ (add_res : Nats_u), add_rel ds_d4mH mult_res add_res ∧ mult_Suc_x_lem_res == add_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite mult_Suc_x_lem: f_rel_back.

Theorem mult_Zero_x_lem ds_d4mH mult_Zero_x_lem_res:
  mult_rel Zero_u ds_d4mH mult_Zero_x_lem_res ↔ mult_Zero_x_lem_res == Zero_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite mult_Zero_x_lem: f_rel_back.

Theorem mult_rel_ex
  (ds_d4mG : Nats_u)
  (ds_d4mG_p : Nats_wf ds_d4mG ∧ True)
  (ds_d4mH : Nats_u)
  (ds_d4mH_p : Nats_wf ds_d4mH ∧ True):
  mult_rel ds_d4mG ds_d4mH ⌊ mult (exist _ ds_d4mG ds_d4mG_p) (exist _ ds_d4mH ds_d4mH_p) -⌋.
Proof.
  Opaque mult.
  existence_lemma_pre mult;
  try revert ds_d4mH_p; generalize dependent ds_d4mH; induction ds_d4mG as [m IH_m|]; intros;
  [fix_notations;
   pose proof (IH_m
               ltac:(try clear IH_m; solver)
               ds_d4mH
               ltac:(try clear IH_m; solver)) as IH_74478145;
   try clear IH_m |
   fix_notations];
  simpl in *.
  Transparent mult.
  all: (existence_lemma_quicksolve mult; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve mult_rel_ex: rel_ax_db.

#[global] Opaque mult.

Theorem mult__mult_rel_rw
  (ds_d4mG : Nats_u)
  (ds_d4mG_p : Nats_wf ds_d4mG ∧ True)
  (ds_d4mH : Nats_u)
  (ds_d4mH_p : Nats_wf ds_d4mH ∧ True)
  (VV : Nats_u):
  ⌊ mult (exist _ ds_d4mG ds_d4mG_p) (exist _ ds_d4mH ds_d4mH_p) -⌋ = VV
  ↔ mult_rel ds_d4mG ds_d4mH VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite mult__mult_rel_rw: f_rel_funct_db.

#[global] Hint Resolve mult__mult_rel_rw: rel_ax_db.

#[global] Instance mult_lookup_rw: dictionary rwLem mult := { lookup' := mult__mult_rel_rw }.

Theorem mult__mult_rel (ds_d4mG ds_d4mH : Nats) (VV : Nats_u):
  ⌊ mult ds_d4mG ds_d4mH -⌋ = VV ↔ mult_rel ⌊ ds_d4mG ⌋ ⌊ ds_d4mH ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite mult__mult_rel: f_rel_funct_db.

Theorem mult__mult_rel' (ds_d4mG_u ds_d4mH_u : Nats_u) (ds_d4mG ds_d4mH : Nats) (VV : Nats_u):
  ds_d4mG_u = ⌊ ds_d4mG ⌋
  → (ds_d4mH_u = ⌊ ds_d4mH ⌋ → ⌊ mult ds_d4mG ds_d4mH -⌋ = VV ↔ mult_rel ds_d4mG_u ds_d4mH_u VV).
Proof.
  intros -> ->. refine (mult__mult_rel ds_d4mG ds_d4mH VV).
Qed.

#[global] Hint Resolve mult__mult_rel': f_rel_funct_db.

Theorem mult_rel_mk
  (ds_d4mG : Nats_u)
  (ds_d4mG_p : Nats_wf ds_d4mG ∧ True)
  (ds_d4mH : Nats_u)
  (ds_d4mH_p : Nats_wf ds_d4mH ∧ True):
  {VV: _ | mult_rel ds_d4mG ds_d4mH VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, mult_rel ds_d4mG ds_d4mH VV)
          (mult (exist _ ds_d4mG ds_d4mG_p) (exist _ ds_d4mH ds_d4mH_p))
          _);
  rewrite <- mult__mult_rel';
  quicksolve.
Qed.

#[global] Hint Resolve mult_rel_mk: f_rel_funct_db.

#[global] Instance mult_pack:
  @Pack
  (Nats ::RT λ (ds_d4mG : Nats), Nats ::RT λ (ds_d4mH : Nats), nilRT)
  (Nats_u ::UT (Nats_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((Nats
  ::RT λ (ds_d4mG : Nats), Nats ::RT λ (ds_d4mH : Nats), nilRT)) ((Nats_u ::UT (Nats_u ::UT nilUT))))
  Nats_u
  (λ (x_75073885 : ArgList (Nats ::RT λ (ds_d4mG : Nats), Nats ::RT λ (ds_d4mH : Nats), nilRT))
     (v_x_75073885 : Nats_u),
   ltac:(flattenP (λ (ds_d4mG ds_d4mH : Nats) (VV : Nats_u), Nats_wf VV ∧ True) x_75073885 v_x_75073885)).
Proof.
  buildPackG mult mult_rel mult__mult_rel mult_rel_funct.
Defined.

#[global] Instance mult_upack: @uPack (Nats_u ::UT (Nats_u ::UT nilUT)) Nats_u.
Proof.
  buildUPackG mult_rel mult_rel_funct.
Defined.

Definition add_dist_rmult_spec (ds_d4mI ds_d4mJ ds_d4mK : Nats): Type :=
  {{∃ (add_res : Nats_u),
    add_rel ⌊ ds_d4mI ⌋ ⌊ ds_d4mJ ⌋ add_res
    ∧ ∃ (mult_res : Nats_u),
      mult_rel add_res ⌊ ds_d4mK ⌋ mult_res
      ∧ ∃ (mult_res_2 : Nats_u),
        mult_rel ⌊ ds_d4mJ ⌋ ⌊ ds_d4mK ⌋ mult_res_2
        ∧ ∃ (mult_res_3 : Nats_u),
          mult_rel ⌊ ds_d4mI ⌋ ⌊ ds_d4mK ⌋ mult_res_3
          ∧ ∃ (add_res_2 : Nats_u), add_rel mult_res_3 mult_res_2 add_res_2 ∧ mult_res == add_res_2}}.

#[global] Hint Unfold add_dist_rmult_spec: lia_unfold.

Theorem add_dist_rmult (ds_d4mI ds_d4mJ ds_d4mK : Nats):
  add_dist_rmult_spec ds_d4mI ds_d4mJ ds_d4mK.
Proof.
  destruct ds_d4mI as [ds_d4mI ds_d4mI_p].
  destruct ds_d4mJ as [ds_d4mJ ds_d4mJ_p].
  destruct ds_d4mK as [ds_d4mK ds_d4mK_p].
  try revert ds_d4mK_p; generalize dependent ds_d4mK;
  try revert ds_d4mJ_p; generalize dependent ds_d4mJ;
  induction ds_d4mI as [m IH_m|];
  intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (add_res : Nats_u),
             add_rel (Suc_u m) ds_d4mJ add_res
             ∧ ∃ (mult_res : Nats_u),
               mult_rel add_res ds_d4mK mult_res
               ∧ ∃ (mult_res_2 : Nats_u),
                 mult_rel ds_d4mJ ds_d4mK mult_res_2
                 ∧ ∃ (mult_res_3 : Nats_u),
                   mult_rel (Suc_u m) ds_d4mK mult_res_3
                   ∧ ∃ (add_res_2 : Nats_u), add_rel mult_res_3 mult_res_2 add_res_2 ∧ mult_res == add_res_2)
            (let _: ∃ (add_res : Nats_u),
                    add_rel
                    ⌊ mult
                      (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver))
                      (exist (λ (ds_d4mK : Nats_u), Nats_wf ds_d4mK ∧ True) ds_d4mK ltac:(solver)) ⌋
                    ⌊ mult
                      (exist (λ (ds_d4mJ : Nats_u), Nats_wf ds_d4mJ ∧ True) ds_d4mJ ltac:(solver))
                      (exist (λ (ds_d4mK : Nats_u), Nats_wf ds_d4mK ∧ True) ds_d4mK ltac:(solver)) ⌋
                    add_res
                    ∧ ∃ (add_res_2 : Nats_u),
                      add_rel ds_d4mK add_res add_res_2
                      ∧ ∃ (add_res_3 : Nats_u),
                        add_rel
                        ds_d4mK
                        ⌊ mult
                          (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver))
                          (exist (λ (ds_d4mK : Nats_u), Nats_wf ds_d4mK ∧ True) ds_d4mK ltac:(solver)) ⌋
                        add_res_3
                        ∧ ∃ (add_res_4 : Nats_u),
                          add_rel
                          add_res_3
                          ⌊ mult
                            (exist (λ (ds_d4mJ : Nats_u), Nats_wf ds_d4mJ ∧ True) ds_d4mJ ltac:(solver))
                            (exist (λ (ds_d4mK : Nats_u), Nats_wf ds_d4mK ∧ True) ds_d4mK ltac:(solver)) ⌋
                          add_res_4
                          ∧ add_res_2 == add_res_4 :=
             ⌈ add_assoc
               (exist (λ (ds_d4mK : Nats_u), Nats_wf ds_d4mK ∧ True) ds_d4mK ltac:(solver))
               (mult
                (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver))
                (exist (λ (ds_d4mK : Nats_u), Nats_wf ds_d4mK ∧ True) ds_d4mK ltac:(solver)))
               (mult
                (exist (λ (ds_d4mJ : Nats_u), Nats_wf ds_d4mJ ∧ True) ds_d4mJ ltac:(solver))
                (exist (λ (ds_d4mK : Nats_u), Nats_wf ds_d4mK ∧ True) ds_d4mK ltac:(solver))) ⌉ in
             IH_m
             ltac:(try clear IH_m; solver)
             ds_d4mJ
             ltac:(try clear IH_m; solver)
             ds_d4mK
             ltac:(try clear IH_m; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (add_res : Nats_u),
             add_rel Zero_u ds_d4mJ add_res
             ∧ ∃ (mult_res : Nats_u),
               mult_rel add_res ds_d4mK mult_res
               ∧ ∃ (mult_res_2 : Nats_u),
                 mult_rel ds_d4mJ ds_d4mK mult_res_2
                 ∧ ∃ (mult_res_3 : Nats_u),
                   mult_rel Zero_u ds_d4mK mult_res_3
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
  (ds_d4lW : Nats)
  (ds_d4lX : {ds_d4lX: Nats_u | Nats_wf ds_d4lX
                                ∧ ∃ (geqN_res : bool), geqN_rel ⌊ ds_d4lW ⌋ ds_d4lX geqN_res ∧ is_true geqN_res}):
  Type :=
  {o: Nats_u | Nats_wf o ∧ (o ≠ Zero_u ↔ ⌊ ds_d4lW ⌋ ≠ ⌊ ds_d4lX ⌋)}.

#[global] Hint Unfold sub_spec: lia_unfold.

Definition sub
  (ds_d4lW : Nats)
  (ds_d4lX : {ds_d4lX: Nats_u | Nats_wf ds_d4lX
                                ∧ ∃ (geqN_res : bool), geqN_rel ⌊ ds_d4lW ⌋ ds_d4lX geqN_res ∧ is_true geqN_res}):
  sub_spec ds_d4lW ds_d4lX.
Proof.
  destruct ds_d4lW as [ds_d4lW ds_d4lW_p].
  destruct ds_d4lX as [ds_d4lX ds_d4lX_p].
  try revert ds_d4lX_p; generalize dependent ds_d4lX; induction ds_d4lW as [m IH_m|]; intros.
  - destruct ds_d4lX as [n|].
    + refine (subsumptionCast
              Nats_u
              (λ (o : Nats_u), Nats_wf o ∧ (o ≠ Zero_u ↔ Suc_u m ≠ Suc_u n))
              (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver))
              ltac:(solver)).
    + refine (subsumptionCast
              Nats_u
              (λ (o : Nats_u), Nats_wf o ∧ (o ≠ Zero_u ↔ Suc_u m ≠ Zero_u))
              (Suc (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver)))
              ltac:(solver)).
  - destruct ds_d4lX as [lq_anf7205759403792810480|].
    + intros; exfalso; solver.
    + refine (subsumptionCast
              Nats_u
              (λ (o : Nats_u), Nats_wf o ∧ (o ≠ Zero_u ↔ Zero_u ≠ Zero_u))
              Zero
              ltac:(solver)).
Defined.

Inductive sub_rel: Nats_u → Nats_u → Nats_u → Prop :=
  | sub_Suc_Suc: ∀ m n (sub_res : Nats_u), sub_rel m n sub_res → sub_rel (Suc_u m) (Suc_u n) sub_res
  | sub_Suc_Zero: ∀ m, sub_rel (Suc_u m) Zero_u (Suc_u m)
  | sub_Zero_Zero: sub_rel Zero_u Zero_u Zero_u.

#[global] Hint Constructors sub_rel: core_hint_db.

#[global] Instance sub_lookup_rel: dictionary rel sub := { lookup' := sub_rel }.

#[global] Instance sub_getF: getFunc sub_rel := { getF' := sub }.

Theorem sub_rel_funct [ds_d4lW ds_d4lX : Nats_u]:
  ∀ (o o' : Nats_u), sub_rel ds_d4lW ds_d4lX o → (sub_rel ds_d4lW ds_d4lX o' → o = o').
Proof.
  try revert ds_d4lX_p; generalize dependent ds_d4lX; induction ds_d4lW as [m IH_m|]; intros;
  [destruct ds_d4lX as [n|] | destruct ds_d4lX as [lq_anf7205759403792810480|]];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve sub_rel_funct: f_rel_funct_db.

Theorem sub_Suc_Suc_lem m n sub_Suc_Suc_lem_res:
  sub_rel (Suc_u m) (Suc_u n) sub_Suc_Suc_lem_res
  ↔ ∃ (sub_res : Nats_u), sub_rel m n sub_res ∧ sub_Suc_Suc_lem_res == sub_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite sub_Suc_Suc_lem: f_rel_back.

Theorem sub_Suc_Zero_lem m sub_Suc_Zero_lem_res:
  sub_rel (Suc_u m) Zero_u sub_Suc_Zero_lem_res ↔ sub_Suc_Zero_lem_res == Suc_u m.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite sub_Suc_Zero_lem: f_rel_back.

Theorem sub_Zero_Zero_lem sub_Zero_Zero_lem_res:
  sub_rel Zero_u Zero_u sub_Zero_Zero_lem_res ↔ sub_Zero_Zero_lem_res == Zero_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite sub_Zero_Zero_lem: f_rel_back.

Theorem sub_rel_ex
  (ds_d4lW : Nats_u)
  (ds_d4lW_p : Nats_wf ds_d4lW ∧ True)
  (ds_d4lX : Nats_u)
  (ds_d4lX_p : Nats_wf ds_d4lX
               ∧ ∃ (geqN_res : bool), geqN_rel ds_d4lW ds_d4lX geqN_res ∧ is_true geqN_res):
  sub_rel ds_d4lW ds_d4lX ⌊ sub (exist _ ds_d4lW ds_d4lW_p) (exist _ ds_d4lX ds_d4lX_p) -⌋.
Proof.
  Opaque sub.
  existence_lemma_pre sub;
  try revert ds_d4lX_p; generalize dependent ds_d4lX; induction ds_d4lW as [m IH_m|]; intros;
  [destruct ds_d4lX as [n|];
   [fix_notations;
    pose proof (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver)) as IH_14792487;
    try clear IH_m |
    fix_notations] |
   destruct ds_d4lX as [lq_anf7205759403792810480|];
   [ | fix_notations]];
  simpl in *.
  Transparent sub.
  all: (existence_lemma_quicksolve sub; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve sub_rel_ex: rel_ax_db.

#[global] Opaque sub.

Theorem sub__sub_rel_rw
  (ds_d4lW : Nats_u)
  (ds_d4lW_p : Nats_wf ds_d4lW ∧ True)
  (ds_d4lX : Nats_u)
  (ds_d4lX_p : Nats_wf ds_d4lX
               ∧ ∃ (geqN_res : bool), geqN_rel ds_d4lW ds_d4lX geqN_res ∧ is_true geqN_res)
  (o : Nats_u):
  ⌊ sub (exist _ ds_d4lW ds_d4lW_p) (exist _ ds_d4lX ds_d4lX_p) -⌋ = o ↔ sub_rel ds_d4lW ds_d4lX o.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite sub__sub_rel_rw: f_rel_funct_db.

#[global] Hint Resolve sub__sub_rel_rw: rel_ax_db.

#[global] Instance sub_lookup_rw: dictionary rwLem sub := { lookup' := sub__sub_rel_rw }.

Theorem sub__sub_rel
  (ds_d4lW : Nats)
  (ds_d4lX : {ds_d4lX: Nats_u | Nats_wf ds_d4lX
                                ∧ ∃ (geqN_res : bool), geqN_rel ⌊ ds_d4lW ⌋ ds_d4lX geqN_res ∧ is_true geqN_res})
  (o : Nats_u):
  ⌊ sub ds_d4lW ds_d4lX -⌋ = o ↔ sub_rel ⌊ ds_d4lW ⌋ ⌊ ds_d4lX ⌋ o.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite sub__sub_rel: f_rel_funct_db.

Theorem sub__sub_rel'
  (ds_d4lW_u ds_d4lX_u : Nats_u)
  (ds_d4lW : Nats)
  (ds_d4lX : {ds_d4lX: Nats_u | Nats_wf ds_d4lX
                                ∧ ∃ (geqN_res : bool), geqN_rel ⌊ ds_d4lW ⌋ ds_d4lX geqN_res ∧ is_true geqN_res})
  (o : Nats_u):
  ds_d4lW_u = ⌊ ds_d4lW ⌋
  → (ds_d4lX_u = ⌊ ds_d4lX ⌋ → ⌊ sub ds_d4lW ds_d4lX -⌋ = o ↔ sub_rel ds_d4lW_u ds_d4lX_u o).
Proof.
  intros -> ->. refine (sub__sub_rel ds_d4lW ds_d4lX o).
Qed.

#[global] Hint Resolve sub__sub_rel': f_rel_funct_db.

Theorem sub_rel_mk
  (ds_d4lW : Nats_u)
  (ds_d4lW_p : Nats_wf ds_d4lW ∧ True)
  (ds_d4lX : Nats_u)
  (ds_d4lX_p : Nats_wf ds_d4lX
               ∧ ∃ (geqN_res : bool), geqN_rel ds_d4lW ds_d4lX geqN_res ∧ is_true geqN_res):
  {o: _ | sub_rel ds_d4lW ds_d4lX o}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ o, sub_rel ds_d4lW ds_d4lX o)
          (sub (exist _ ds_d4lW ds_d4lW_p) (exist _ ds_d4lX ds_d4lX_p))
          _);
  rewrite <- sub__sub_rel';
  quicksolve.
Qed.

#[global] Hint Resolve sub_rel_mk: f_rel_funct_db.

#[global] Instance sub_pack:
  @Pack
  (Nats
   ::RT λ (ds_d4lW : Nats),
        {ds_d4lX: Nats_u | Nats_wf ds_d4lX
                           ∧ ∃ (geqN_res : bool), geqN_rel ⌊ ds_d4lW ⌋ ds_d4lX geqN_res ∧ is_true geqN_res}
        ::RT λ (ds_d4lX : {ds_d4lX: Nats_u | Nats_wf ds_d4lX
                                             ∧ ∃ (geqN_res : bool),
                                               geqN_rel ⌊ ds_d4lW ⌋ ds_d4lX geqN_res ∧ is_true geqN_res}),
             nilRT)
  (Nats_u ::UT (Nats_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((Nats
  ::RT λ (ds_d4lW : Nats),
       {ds_d4lX: Nats_u | Nats_wf ds_d4lX
                          ∧ ∃ (geqN_res : bool),
                            geqN_rel ⌊ ds_d4lW ⌋ ds_d4lX geqN_res ∧ is_true geqN_res}
       ::RT λ (ds_d4lX : {ds_d4lX: Nats_u | Nats_wf ds_d4lX
                                            ∧ ∃ (geqN_res : bool),
                                              geqN_rel ⌊ ds_d4lW ⌋ ds_d4lX geqN_res
                                              ∧ is_true geqN_res}),
            nilRT)) ((Nats_u ::UT (Nats_u ::UT nilUT))))
  Nats_u
  (λ (x_10146466 : ArgList (Nats
                            ::RT λ (ds_d4lW : Nats),
                                 {ds_d4lX: Nats_u | Nats_wf ds_d4lX
                                                    ∧ ∃ (geqN_res : bool),
                                                      geqN_rel ⌊ ds_d4lW ⌋ ds_d4lX geqN_res ∧ is_true geqN_res}
                                 ::RT λ (ds_d4lX : {ds_d4lX: Nats_u | Nats_wf ds_d4lX
                                                                      ∧ ∃ (geqN_res : bool),
                                                                        geqN_rel ⌊ ds_d4lW ⌋ ds_d4lX geqN_res
                                                                        ∧ is_true geqN_res}),
                                      nilRT))
     (v_x_10146466 : Nats_u),
   ltac:(flattenP (λ (ds_d4lW : Nats)
   (ds_d4lX : {ds_d4lX: Nats_u | Nats_wf ds_d4lX
                                 ∧ ∃ (geqN_res : bool),
                                   geqN_rel ⌊ ds_d4lW ⌋ ds_d4lX geqN_res ∧ is_true geqN_res})
   (o : Nats_u),
 Nats_wf o ∧ (o ≠ Zero_u ↔ ⌊ ds_d4lW ⌋ ≠ ⌊ ds_d4lX ⌋)) x_10146466 v_x_10146466)).
Proof.
  buildPackG sub sub_rel sub__sub_rel sub_rel_funct.
Defined.

#[global] Instance sub_upack: @uPack (Nats_u ::UT (Nats_u ::UT nilUT)) Nats_u.
Proof.
  buildUPackG sub_rel sub_rel_funct.
Defined.

Definition add_sub_spec (ds_d4mq ds_d4mr : Nats): Type :=
  {{∃ (add_res : Nats_u),
    add_rel ⌊ ds_d4mq ⌋ ⌊ ds_d4mr ⌋ add_res
    ∧ ∃ (sub_res : Nats_u), sub_rel add_res ⌊ ds_d4mr ⌋ sub_res ∧ sub_res == ⌊ ds_d4mq ⌋}}.

#[global] Hint Unfold add_sub_spec: lia_unfold.

Theorem add_sub (ds_d4mq ds_d4mr : Nats): add_sub_spec ds_d4mq ds_d4mr.
Proof.
  destruct ds_d4mq as [ds_d4mq ds_d4mq_p].
  destruct ds_d4mr as [ds_d4mr ds_d4mr_p].
  destruct ds_d4mq as [m|].
  - induction ds_d4mr as [lq_anf7205759403792810450 IH_lq_anf7205759403792810450|].
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∃ (add_res : Nats_u),
               add_rel (Suc_u m) (Suc_u lq_anf7205759403792810450) add_res
               ∧ ∃ (sub_res : Nats_u),
                 sub_rel add_res (Suc_u lq_anf7205759403792810450) sub_res ∧ sub_res == Suc_u m)
              (let _: ∃ (add_res : Nats_u),
                      add_rel (Suc_u m) lq_anf7205759403792810450 add_res
                      ∧ ∃ (sub_res : Nats_u), sub_rel add_res lq_anf7205759403792810450 sub_res ∧ sub_res == Suc_u m :=
               ⌈ IH_lq_anf7205759403792810450 ltac:(try clear IH_lq_anf7205759403792810450; solver) ⌉ in
               add_suc_r
               (Suc (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver)))
               (exist (λ (n : Nats_u), Nats_wf n ∧ True) lq_anf7205759403792810450 ltac:(solver)))
              ltac:(solver)).
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∃ (add_res : Nats_u),
               add_rel (Suc_u m) Zero_u add_res
               ∧ ∃ (sub_res : Nats_u), sub_rel add_res Zero_u sub_res ∧ sub_res == Suc_u m)
              (add_zero_r (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver)))
              ltac:(solver)).
  - induction ds_d4mr as [lq_anf7205759403792810442 IH_lq_anf7205759403792810442|].
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∃ (add_res : Nats_u),
               add_rel Zero_u (Suc_u lq_anf7205759403792810442) add_res
               ∧ ∃ (sub_res : Nats_u),
                 sub_rel add_res (Suc_u lq_anf7205759403792810442) sub_res ∧ sub_res == Zero_u)
              (let _: ∃ (add_res : Nats_u),
                      add_rel Zero_u lq_anf7205759403792810442 add_res
                      ∧ ∃ (sub_res : Nats_u), sub_rel add_res lq_anf7205759403792810442 sub_res ∧ sub_res == Zero_u :=
               ⌈ IH_lq_anf7205759403792810442 ltac:(try clear IH_lq_anf7205759403792810442; solver) ⌉ in
               add_suc_r Zero (exist (λ (n : Nats_u), Nats_wf n ∧ True) lq_anf7205759403792810442 ltac:(solver)))
              ltac:(solver)).
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∃ (add_res : Nats_u),
               add_rel Zero_u Zero_u add_res
               ∧ ∃ (sub_res : Nats_u), sub_rel add_res Zero_u sub_res ∧ sub_res == Zero_u)
              (# unit)
              ltac:(solver)).
Qed.

Definition sub_self_spec (ds_d4lQ ds_d4lR : Nats): Type :=
  {{∃ (eqN_res : bool), eqN_rel ⌊ ds_d4lQ ⌋ ⌊ ds_d4lR ⌋ eqN_res ∧ is_true eqN_res
    → ∃ (sub_res : Nats_u), sub_rel ⌊ ds_d4lQ ⌋ ⌊ ds_d4lR ⌋ sub_res ∧ sub_res == Zero_u}}.

#[global] Hint Unfold sub_self_spec: lia_unfold.

Theorem sub_self (ds_d4lQ ds_d4lR : Nats): sub_self_spec ds_d4lQ ds_d4lR.
Proof.
  destruct ds_d4lQ as [ds_d4lQ ds_d4lQ_p].
  destruct ds_d4lR as [ds_d4lR ds_d4lR_p].
  try revert ds_d4lR_p; generalize dependent ds_d4lR; induction ds_d4lQ as [m IH_m|]; intros.
  - destruct ds_d4lR as [n|].
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∃ (eqN_res : bool), eqN_rel (Suc_u m) (Suc_u n) eqN_res ∧ is_true eqN_res
               → ∃ (sub_res : Nats_u), sub_rel (Suc_u m) (Suc_u n) sub_res ∧ sub_res == Zero_u)
              (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver))
              ltac:(solver)).
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∃ (eqN_res : bool), eqN_rel (Suc_u m) Zero_u eqN_res ∧ is_true eqN_res
               → ∃ (sub_res : Nats_u), sub_rel (Suc_u m) Zero_u sub_res ∧ sub_res == Zero_u)
              (# unit)
              ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (eqN_res : bool), eqN_rel Zero_u ds_d4lR eqN_res ∧ is_true eqN_res
             → ∃ (sub_res : Nats_u), sub_rel Zero_u ds_d4lR sub_res ∧ sub_res == Zero_u)
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
