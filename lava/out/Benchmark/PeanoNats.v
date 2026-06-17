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

Definition Suc_lem (n : Nats): Nats_wf (Suc_u ⌊ n -⌋) ∧ True.
Proof.
  repeat first [split | solver].
Defined.

Definition Suc (n : Nats): Nats :=
  exist _ (Suc_u ⌊ n -⌋) (Suc_lem n).

Definition Zero_lem : Nats_wf Zero_u ∧ True.
Proof.
  repeat first [split | solver].
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

Definition add_spec (ds_d4oi n : Nats): Type :=
  Nats.

#[global] Hint Unfold add_spec: lia_unfold.

Definition add (ds_d4oi n : Nats): add_spec ds_d4oi n.
Proof.
  destruct ds_d4oi as [ds_d4oi ds_d4oi_p].
  destruct n as [n n_p].
  try revert n_p; generalize dependent n; induction ds_d4oi as [m IH_m|]; intros.
  - refine (Suc (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver))).
  - refine (exist (λ (n : Nats_u), Nats_wf n ∧ True) n ltac:(solver)).
Defined.

Inductive add_rel: Nats_u → Nats_u → Nats_u → Prop :=
  | add_Suc_x: ∀ m n (add_res : Nats_u), add_rel m n add_res → add_rel (Suc_u m) n (Suc_u add_res)
  | add_Zero_x: ∀ n, add_rel Zero_u n n.

#[global] Hint Constructors add_rel: core_hint_db.

#[global] Instance add_lookup_rel: dictionary rel add := { lookup' := add_rel }.

#[global] Instance add_getF: getFunc add_rel := { getF' := add }.

Theorem add_rel_funct [ds_d4oi n : Nats_u]:
  ∀ (VV VV' : Nats_u), add_rel ds_d4oi n VV → (add_rel ds_d4oi n VV' → VV = VV').
Proof.
  try revert n_p; generalize dependent n; induction ds_d4oi as [m IH_m|]; intros;
  rel_functionhood_body.
Qed.

#[global] Hint Resolve add_rel_funct: f_rel_funct_db.

#[global] Instance add_lookup_funct: dictionary functionhood add := { lookup' := add_rel_funct }.

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
  (ds_d4oi : Nats_u) (ds_d4oi_p : Nats_wf ds_d4oi ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True):
  add_rel ds_d4oi n ⌊ add (exist _ ds_d4oi ds_d4oi_p) (exist _ n n_p) -⌋.
Proof.
  Opaque add.
  existence_lemma_pre add;
  try revert n_p; generalize dependent n; induction ds_d4oi as [m IH_m|]; intros;
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
  (ds_d4oi : Nats_u)
  (ds_d4oi_p : Nats_wf ds_d4oi ∧ True)
  (n : Nats_u)
  (n_p : Nats_wf n ∧ True)
  (VV : Nats_u):
  ⌊ add (exist _ ds_d4oi ds_d4oi_p) (exist _ n n_p) -⌋ = VV ↔ add_rel ds_d4oi n VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite add__add_rel_rw: f_rel_funct_db.

#[global] Hint Resolve add__add_rel_rw: rel_ax_db.

#[global] Instance add_lookup_rw: dictionary rwLem add := { lookup' := add__add_rel_rw }.

Theorem add__add_rel (ds_d4oi n : Nats) (VV : Nats_u):
  ⌊ add ds_d4oi n -⌋ = VV ↔ add_rel ⌊ ds_d4oi ⌋ ⌊ n ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite add__add_rel: f_rel_funct_db.

Theorem add__add_rel' (ds_d4oi_u n_u : Nats_u) (ds_d4oi n : Nats) (VV : Nats_u):
  ds_d4oi_u = ⌊ ds_d4oi ⌋ → (n_u = ⌊ n ⌋ → ⌊ add ds_d4oi n -⌋ = VV ↔ add_rel ds_d4oi_u n_u VV).
Proof.
  intros -> ->. refine (add__add_rel ds_d4oi n VV).
Qed.

#[global] Hint Resolve add__add_rel': f_rel_funct_db.

Theorem add_rel_mk
  (ds_d4oi : Nats_u) (ds_d4oi_p : Nats_wf ds_d4oi ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True):
  {VV: _ | add_rel ds_d4oi n VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, add_rel ds_d4oi n VV)
          (add (exist _ ds_d4oi ds_d4oi_p) (exist _ n n_p))
          _);
  rewrite <- add__add_rel';
  quicksolve.
Qed.

#[global] Hint Resolve add_rel_mk: f_rel_funct_db.

#[global] Instance add_pack:
  @Pack
  (Nats ::RT λ (ds_d4oi : Nats), Nats ::RT λ (n : Nats), nilRT)
  (Nats_u ::UT (Nats_u ::UT nilUT))
  ltac:(mkProjectsArgListTG (Nats ::RT λ (ds_d4oi : Nats), Nats ::RT λ (n : Nats), nilRT) ((Nats_u ::UT (Nats_u ::UT nilUT))))
  Nats_u
  (λ (x_65232642 : ArgList (Nats ::RT λ (ds_d4oi : Nats), Nats ::RT λ (n : Nats), nilRT))
     (v_x_65232642 : Nats_u),
   ltac:(flattenP (λ (ds_d4oi n : Nats) (VV : Nats_u), Nats_wf VV ∧ True) x_65232642 v_x_65232642)).
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
                 add_rel ⌊ m -⌋ ⌊ n -⌋ add_res
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
  {v: Nats_u | Nats_wf v ∧ ∃ (add_res : Nats_u), add_rel ⌊ m -⌋ ⌊ n -⌋ add_res ∧ add_res == v}.

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

Definition add_assoc_spec (ds_d4oc ds_d4od ds_d4oe : Nats): Type :=
  {{∃ (add_res : Nats_u),
    add_rel ⌊ ds_d4od -⌋ ⌊ ds_d4oe -⌋ add_res
    ∧ ∃ (add_res_2 : Nats_u),
      add_rel ⌊ ds_d4oc -⌋ add_res add_res_2
      ∧ ∃ (add_res_3 : Nats_u),
        add_rel ⌊ ds_d4oc -⌋ ⌊ ds_d4od -⌋ add_res_3
        ∧ ∃ (add_res_4 : Nats_u), add_rel add_res_3 ⌊ ds_d4oe -⌋ add_res_4 ∧ add_res_2 == add_res_4}}.

#[global] Hint Unfold add_assoc_spec: lia_unfold.

Theorem add_assoc (ds_d4oc ds_d4od ds_d4oe : Nats): add_assoc_spec ds_d4oc ds_d4od ds_d4oe.
Proof.
  destruct ds_d4oc as [ds_d4oc ds_d4oc_p].
  destruct ds_d4od as [ds_d4od ds_d4od_p].
  destruct ds_d4oe as [ds_d4oe ds_d4oe_p].
  try revert ds_d4oe_p; generalize dependent ds_d4oe;
  try revert ds_d4od_p; generalize dependent ds_d4od;
  induction ds_d4oc as [m IH_m|];
  intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (add_res : Nats_u),
             add_rel ds_d4od ds_d4oe add_res
             ∧ ∃ (add_res_2 : Nats_u),
               add_rel (Suc_u m) add_res add_res_2
               ∧ ∃ (add_res_3 : Nats_u),
                 add_rel (Suc_u m) ds_d4od add_res_3
                 ∧ ∃ (add_res_4 : Nats_u), add_rel add_res_3 ds_d4oe add_res_4 ∧ add_res_2 == add_res_4)
            (IH_m
             ltac:(try clear IH_m; solver)
             ds_d4od
             ltac:(try clear IH_m; solver)
             ds_d4oe
             ltac:(try clear IH_m; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (add_res : Nats_u),
             add_rel ds_d4od ds_d4oe add_res
             ∧ ∃ (add_res_2 : Nats_u),
               add_rel Zero_u add_res add_res_2
               ∧ ∃ (add_res_3 : Nats_u),
                 add_rel Zero_u ds_d4od add_res_3
                 ∧ ∃ (add_res_4 : Nats_u), add_rel add_res_3 ds_d4oe add_res_4 ∧ add_res_2 == add_res_4)
            (# unit)
            ltac:(solver)).
Qed.

Definition add_suc_r_spec (ds_d4o1 ds_d4o2 : Nats): Type :=
  {{∃ (add_res : Nats_u),
    add_rel ⌊ ds_d4o1 -⌋ ⌊ ds_d4o2 -⌋ add_res
    ∧ ∃ (add_res_2 : Nats_u),
      add_rel ⌊ ds_d4o1 -⌋ (Suc_u ⌊ ds_d4o2 -⌋) add_res_2 ∧ Suc_u add_res == add_res_2}}.

#[global] Hint Unfold add_suc_r_spec: lia_unfold.

Theorem add_suc_r (ds_d4o1 ds_d4o2 : Nats): add_suc_r_spec ds_d4o1 ds_d4o2.
Proof.
  destruct ds_d4o1 as [ds_d4o1 ds_d4o1_p].
  destruct ds_d4o2 as [ds_d4o2 ds_d4o2_p].
  try revert ds_d4o2_p; generalize dependent ds_d4o2; induction ds_d4o1 as [m IH_m|]; intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (add_res : Nats_u),
             add_rel (Suc_u m) ds_d4o2 add_res
             ∧ ∃ (add_res_2 : Nats_u), add_rel (Suc_u m) (Suc_u ds_d4o2) add_res_2 ∧ Suc_u add_res == add_res_2)
            (IH_m ltac:(try clear IH_m; solver) ds_d4o2 ltac:(try clear IH_m; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (add_res : Nats_u),
             add_rel Zero_u ds_d4o2 add_res
             ∧ ∃ (add_res_2 : Nats_u), add_rel Zero_u (Suc_u ds_d4o2) add_res_2 ∧ Suc_u add_res == add_res_2)
            (# unit)
            ltac:(solver)).
Qed.

Definition add_zero_l_spec (ds_d4of : Nats): Type :=
  {{∃ (add_res : Nats_u), add_rel Zero_u ⌊ ds_d4of -⌋ add_res ∧ add_res == ⌊ ds_d4of -⌋}}.

#[global] Hint Unfold add_zero_l_spec: lia_unfold.

Theorem add_zero_l (ds_d4of : Nats): add_zero_l_spec ds_d4of.
Proof.
  destruct ds_d4of as [ds_d4of ds_d4of_p].
  induction ds_d4of as [n IH_n|].
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

Definition add_zero_r_spec (ds_d4o3 : Nats): Type :=
  {{∃ (add_res : Nats_u), add_rel ⌊ ds_d4o3 -⌋ Zero_u add_res ∧ add_res == ⌊ ds_d4o3 -⌋}}.

#[global] Hint Unfold add_zero_r_spec: lia_unfold.

Theorem add_zero_r (ds_d4o3 : Nats): add_zero_r_spec ds_d4o3.
Proof.
  destruct ds_d4o3 as [ds_d4o3 ds_d4o3_p].
  induction ds_d4o3 as [n IH_n|].
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

Definition eqN_spec (ds_d4nF ds_d4nG : Nats): Type :=
  Bool.

#[global] Hint Unfold eqN_spec: lia_unfold.

Definition eqN (ds_d4nF ds_d4nG : Nats): eqN_spec ds_d4nF ds_d4nG.
Proof.
  destruct ds_d4nF as [ds_d4nF ds_d4nF_p].
  destruct ds_d4nG as [ds_d4nG ds_d4nG_p].
  try revert ds_d4nG_p; generalize dependent ds_d4nG; induction ds_d4nF as [m IH_m|]; intros.
  - destruct ds_d4nG as [n|].
    + refine (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver)).
    + refine (# false).
  - destruct ds_d4nG as [lq_anf7205759403792810566|].
    + refine (# false).
    + refine (# true).
Defined.

Inductive eqN_rel: Nats_u → Nats_u → bool → Prop :=
  | eqN_Suc_Suc: ∀ m n (eqN_res : bool), eqN_rel m n eqN_res → eqN_rel (Suc_u m) (Suc_u n) eqN_res
  | eqN_Suc_Zero: ∀ m, eqN_rel (Suc_u m) Zero_u false
  | eqN_Zero_Suc: ∀ lq_anf7205759403792810566, eqN_rel Zero_u (Suc_u lq_anf7205759403792810566) false
  | eqN_Zero_Zero: eqN_rel Zero_u Zero_u true.

#[global] Hint Constructors eqN_rel: core_hint_db.

#[global] Instance eqN_lookup_rel: dictionary rel eqN := { lookup' := eqN_rel }.

#[global] Instance eqN_getF: getFunc eqN_rel := { getF' := eqN }.

Theorem eqN_rel_funct [ds_d4nF ds_d4nG : Nats_u]:
  ∀ (VV VV' : bool), eqN_rel ds_d4nF ds_d4nG VV → (eqN_rel ds_d4nF ds_d4nG VV' → VV = VV').
Proof.
  try revert ds_d4nG_p; generalize dependent ds_d4nG; induction ds_d4nF as [m IH_m|]; intros;
  [destruct ds_d4nG as [n|] | destruct ds_d4nG as [lq_anf7205759403792810566|]];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve eqN_rel_funct: f_rel_funct_db.

#[global] Instance eqN_lookup_funct: dictionary functionhood eqN := { lookup' := eqN_rel_funct }.

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

Theorem eqN_Zero_Suc_lem lq_anf7205759403792810566 eqN_Zero_Suc_lem_res:
  eqN_rel Zero_u (Suc_u lq_anf7205759403792810566) eqN_Zero_Suc_lem_res
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
  (ds_d4nF : Nats_u)
  (ds_d4nF_p : Nats_wf ds_d4nF ∧ True)
  (ds_d4nG : Nats_u)
  (ds_d4nG_p : Nats_wf ds_d4nG ∧ True):
  eqN_rel ds_d4nF ds_d4nG ⌊ eqN (exist _ ds_d4nF ds_d4nF_p) (exist _ ds_d4nG ds_d4nG_p) -⌋.
Proof.
  Opaque eqN.
  existence_lemma_pre eqN;
  try revert ds_d4nG_p; generalize dependent ds_d4nG; induction ds_d4nF as [m IH_m|]; intros;
  [destruct ds_d4nG as [n|];
   [fix_notations;
    pose proof (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver)) as IH_14792487;
    try clear IH_m |
    fix_notations] |
   destruct ds_d4nG as [lq_anf7205759403792810566|];
   [fix_notations | fix_notations]];
  simpl in *.
  Transparent eqN.
  all: (existence_lemma_quicksolve eqN; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve eqN_rel_ex: rel_ax_db.

#[global] Opaque eqN.

Theorem eqN__eqN_rel_rw
  (ds_d4nF : Nats_u)
  (ds_d4nF_p : Nats_wf ds_d4nF ∧ True)
  (ds_d4nG : Nats_u)
  (ds_d4nG_p : Nats_wf ds_d4nG ∧ True)
  (VV : bool):
  ⌊ eqN (exist _ ds_d4nF ds_d4nF_p) (exist _ ds_d4nG ds_d4nG_p) -⌋ = VV ↔ eqN_rel ds_d4nF ds_d4nG VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite eqN__eqN_rel_rw: f_rel_funct_db.

#[global] Hint Resolve eqN__eqN_rel_rw: rel_ax_db.

#[global] Instance eqN_lookup_rw: dictionary rwLem eqN := { lookup' := eqN__eqN_rel_rw }.

Theorem eqN__eqN_rel (ds_d4nF ds_d4nG : Nats) (VV : bool):
  ⌊ eqN ds_d4nF ds_d4nG -⌋ = VV ↔ eqN_rel ⌊ ds_d4nF ⌋ ⌊ ds_d4nG ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite eqN__eqN_rel: f_rel_funct_db.

Theorem eqN__eqN_rel' (ds_d4nF_u ds_d4nG_u : Nats_u) (ds_d4nF ds_d4nG : Nats) (VV : bool):
  ds_d4nF_u = ⌊ ds_d4nF ⌋
  → (ds_d4nG_u = ⌊ ds_d4nG ⌋ → ⌊ eqN ds_d4nF ds_d4nG -⌋ = VV ↔ eqN_rel ds_d4nF_u ds_d4nG_u VV).
Proof.
  intros -> ->. refine (eqN__eqN_rel ds_d4nF ds_d4nG VV).
Qed.

#[global] Hint Resolve eqN__eqN_rel': f_rel_funct_db.

Theorem eqN_rel_mk
  (ds_d4nF : Nats_u)
  (ds_d4nF_p : Nats_wf ds_d4nF ∧ True)
  (ds_d4nG : Nats_u)
  (ds_d4nG_p : Nats_wf ds_d4nG ∧ True):
  {VV: _ | eqN_rel ds_d4nF ds_d4nG VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, eqN_rel ds_d4nF ds_d4nG VV)
          (eqN (exist _ ds_d4nF ds_d4nF_p) (exist _ ds_d4nG ds_d4nG_p))
          _);
  rewrite <- eqN__eqN_rel';
  quicksolve.
Qed.

#[global] Hint Resolve eqN_rel_mk: f_rel_funct_db.

#[global] Instance eqN_pack:
  @Pack
  (Nats ::RT λ (ds_d4nF : Nats), Nats ::RT λ (ds_d4nG : Nats), nilRT)
  (Nats_u ::UT (Nats_u ::UT nilUT))
  ltac:(mkProjectsArgListTG (Nats ::RT λ (ds_d4nF : Nats), Nats ::RT λ (ds_d4nG : Nats), nilRT) ((Nats_u ::UT (Nats_u ::UT nilUT))))
  bool
  (λ (x_28156604 : ArgList (Nats ::RT λ (ds_d4nF : Nats), Nats ::RT λ (ds_d4nG : Nats), nilRT))
     (v_x_28156604 : bool),
   ltac:(flattenP (λ (ds_d4nF ds_d4nG : Nats) (VV : bool), True) x_28156604 v_x_28156604)).
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

Definition geqN_spec (ds_d4nU ds_d4nV : Nats): Type :=
  Bool.

#[global] Hint Unfold geqN_spec: lia_unfold.

Definition geqN (ds_d4nU ds_d4nV : Nats): geqN_spec ds_d4nU ds_d4nV.
Proof.
  destruct ds_d4nU as [ds_d4nU ds_d4nU_p].
  destruct ds_d4nV as [ds_d4nV ds_d4nV_p].
  try revert ds_d4nU_p; generalize dependent ds_d4nU;
  induction ds_d4nV as [lq_anf7205759403792810563 IH_lq_anf7205759403792810563|];
  intros.
  - destruct ds_d4nU as [m|].
    + refine (IH_lq_anf7205759403792810563
              ltac:(try clear IH_lq_anf7205759403792810563; solver)
              m
              ltac:(try clear IH_lq_anf7205759403792810563; solver)).
    + refine (# false).
  - refine (# true).
Defined.

Inductive geqN_rel: Nats_u → Nats_u → bool → Prop :=
  | geqN_Suc_Suc: ∀ m lq_anf7205759403792810563 (geqN_res : bool),
                  geqN_rel m lq_anf7205759403792810563 geqN_res
                  → geqN_rel (Suc_u m) (Suc_u lq_anf7205759403792810563) geqN_res
  | geqN_Zero_Suc: ∀ lq_anf7205759403792810563,
                   geqN_rel Zero_u (Suc_u lq_anf7205759403792810563) false
  | geqN_x_Zero: ∀ ds_d4nU, geqN_rel ds_d4nU Zero_u true.

#[global] Hint Constructors geqN_rel: core_hint_db.

#[global] Instance geqN_lookup_rel: dictionary rel geqN := { lookup' := geqN_rel }.

#[global] Instance geqN_getF: getFunc geqN_rel := { getF' := geqN }.

Theorem geqN_rel_funct [ds_d4nU ds_d4nV : Nats_u]:
  ∀ (VV VV' : bool), geqN_rel ds_d4nU ds_d4nV VV → (geqN_rel ds_d4nU ds_d4nV VV' → VV = VV').
Proof.
  try revert ds_d4nU_p; generalize dependent ds_d4nU;
  induction ds_d4nV as [lq_anf7205759403792810563 IH_lq_anf7205759403792810563|];
  intros;
  [destruct ds_d4nU as [m|] |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve geqN_rel_funct: f_rel_funct_db.

#[global] Instance geqN_lookup_funct: dictionary functionhood geqN := {
    lookup' := geqN_rel_funct }.

Theorem geqN_Suc_Suc_lem lq_anf7205759403792810563 m geqN_Suc_Suc_lem_res:
  geqN_rel (Suc_u m) (Suc_u lq_anf7205759403792810563) geqN_Suc_Suc_lem_res
  ↔ ∃ (geqN_res : bool),
    geqN_rel m lq_anf7205759403792810563 geqN_res ∧ geqN_Suc_Suc_lem_res == geqN_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite geqN_Suc_Suc_lem: f_rel_back.

Theorem geqN_Zero_Suc_lem lq_anf7205759403792810563 geqN_Zero_Suc_lem_res:
  geqN_rel Zero_u (Suc_u lq_anf7205759403792810563) geqN_Zero_Suc_lem_res
  ↔ geqN_Zero_Suc_lem_res == false.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite geqN_Zero_Suc_lem: f_rel_back.

Theorem geqN_x_Zero_lem ds_d4nU geqN_x_Zero_lem_res:
  geqN_rel ds_d4nU Zero_u geqN_x_Zero_lem_res ↔ geqN_x_Zero_lem_res == true.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite geqN_x_Zero_lem: f_rel_back.

Theorem geqN_rel_ex
  (ds_d4nU : Nats_u)
  (ds_d4nU_p : Nats_wf ds_d4nU ∧ True)
  (ds_d4nV : Nats_u)
  (ds_d4nV_p : Nats_wf ds_d4nV ∧ True):
  geqN_rel ds_d4nU ds_d4nV ⌊ geqN (exist _ ds_d4nU ds_d4nU_p) (exist _ ds_d4nV ds_d4nV_p) -⌋.
Proof.
  Opaque geqN.
  existence_lemma_pre geqN;
  try revert ds_d4nU_p; generalize dependent ds_d4nU;
  induction ds_d4nV as [lq_anf7205759403792810563 IH_lq_anf7205759403792810563|];
  intros;
  [destruct ds_d4nU as [m|];
   [fix_notations;
    pose proof (IH_lq_anf7205759403792810563
                ltac:(try clear IH_lq_anf7205759403792810563; solver)
                m
                ltac:(try clear IH_lq_anf7205759403792810563; solver)) as IH_55853897;
    try clear IH_lq_anf7205759403792810563 |
    fix_notations] |
   fix_notations];
  simpl in *.
  Transparent geqN.
  all: (existence_lemma_quicksolve geqN; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve geqN_rel_ex: rel_ax_db.

#[global] Opaque geqN.

Theorem geqN__geqN_rel_rw
  (ds_d4nU : Nats_u)
  (ds_d4nU_p : Nats_wf ds_d4nU ∧ True)
  (ds_d4nV : Nats_u)
  (ds_d4nV_p : Nats_wf ds_d4nV ∧ True)
  (VV : bool):
  ⌊ geqN (exist _ ds_d4nU ds_d4nU_p) (exist _ ds_d4nV ds_d4nV_p) -⌋ = VV
  ↔ geqN_rel ds_d4nU ds_d4nV VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite geqN__geqN_rel_rw: f_rel_funct_db.

#[global] Hint Resolve geqN__geqN_rel_rw: rel_ax_db.

#[global] Instance geqN_lookup_rw: dictionary rwLem geqN := { lookup' := geqN__geqN_rel_rw }.

Theorem geqN__geqN_rel (ds_d4nU ds_d4nV : Nats) (VV : bool):
  ⌊ geqN ds_d4nU ds_d4nV -⌋ = VV ↔ geqN_rel ⌊ ds_d4nU ⌋ ⌊ ds_d4nV ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite geqN__geqN_rel: f_rel_funct_db.

Theorem geqN__geqN_rel' (ds_d4nU_u ds_d4nV_u : Nats_u) (ds_d4nU ds_d4nV : Nats) (VV : bool):
  ds_d4nU_u = ⌊ ds_d4nU ⌋
  → (ds_d4nV_u = ⌊ ds_d4nV ⌋ → ⌊ geqN ds_d4nU ds_d4nV -⌋ = VV ↔ geqN_rel ds_d4nU_u ds_d4nV_u VV).
Proof.
  intros -> ->. refine (geqN__geqN_rel ds_d4nU ds_d4nV VV).
Qed.

#[global] Hint Resolve geqN__geqN_rel': f_rel_funct_db.

Theorem geqN_rel_mk
  (ds_d4nU : Nats_u)
  (ds_d4nU_p : Nats_wf ds_d4nU ∧ True)
  (ds_d4nV : Nats_u)
  (ds_d4nV_p : Nats_wf ds_d4nV ∧ True):
  {VV: _ | geqN_rel ds_d4nU ds_d4nV VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, geqN_rel ds_d4nU ds_d4nV VV)
          (geqN (exist _ ds_d4nU ds_d4nU_p) (exist _ ds_d4nV ds_d4nV_p))
          _);
  rewrite <- geqN__geqN_rel';
  quicksolve.
Qed.

#[global] Hint Resolve geqN_rel_mk: f_rel_funct_db.

#[global] Instance geqN_pack:
  @Pack
  (Nats ::RT λ (ds_d4nU : Nats), Nats ::RT λ (ds_d4nV : Nats), nilRT)
  (Nats_u ::UT (Nats_u ::UT nilUT))
  ltac:(mkProjectsArgListTG (Nats ::RT λ (ds_d4nU : Nats), Nats ::RT λ (ds_d4nV : Nats), nilRT) ((Nats_u ::UT (Nats_u ::UT nilUT))))
  bool
  (λ (x_13635317 : ArgList (Nats ::RT λ (ds_d4nU : Nats), Nats ::RT λ (ds_d4nV : Nats), nilRT))
     (v_x_13635317 : bool),
   ltac:(flattenP (λ (ds_d4nU ds_d4nV : Nats) (VV : bool), True) x_13635317 v_x_13635317)).
Proof.
  buildPackG geqN geqN_rel geqN__geqN_rel geqN_rel_funct.
Defined.

#[global] Instance geqN_upack: @uPack (Nats_u ::UT (Nats_u ::UT nilUT)) bool.
Proof.
  buildUPackG geqN_rel geqN_rel_funct.
Defined.

Definition mult_spec (ds_d4ok ds_d4ol : Nats): Type :=
  Nats.

#[global] Hint Unfold mult_spec: lia_unfold.

Definition mult (ds_d4ok ds_d4ol : Nats): mult_spec ds_d4ok ds_d4ol.
Proof.
  destruct ds_d4ok as [ds_d4ok ds_d4ok_p].
  destruct ds_d4ol as [ds_d4ol ds_d4ol_p].
  try revert ds_d4ol_p; generalize dependent ds_d4ol; induction ds_d4ok as [m IH_m|]; intros.
  - refine (add
            (exist (λ (ds_d4ol : Nats_u), Nats_wf ds_d4ol ∧ True) ds_d4ol ltac:(solver))
            (IH_m ltac:(try clear IH_m; solver) ds_d4ol ltac:(try clear IH_m; solver))).
  - refine Zero.
Defined.

Inductive mult_rel: Nats_u → Nats_u → Nats_u → Prop :=
  | mult_Suc_x: ∀ m ds_d4ol (mult_res : Nats_u),
                mult_rel m ds_d4ol mult_res
                → ∀ (add_res : Nats_u), add_rel ds_d4ol mult_res add_res → mult_rel (Suc_u m) ds_d4ol add_res
  | mult_Zero_x: ∀ ds_d4ol, mult_rel Zero_u ds_d4ol Zero_u.

#[global] Hint Constructors mult_rel: core_hint_db.

#[global] Instance mult_lookup_rel: dictionary rel mult := { lookup' := mult_rel }.

#[global] Instance mult_getF: getFunc mult_rel := { getF' := mult }.

Theorem mult_rel_funct [ds_d4ok ds_d4ol : Nats_u]:
  ∀ (VV VV' : Nats_u), mult_rel ds_d4ok ds_d4ol VV → (mult_rel ds_d4ok ds_d4ol VV' → VV = VV').
Proof.
  try revert ds_d4ol_p; generalize dependent ds_d4ol; induction ds_d4ok as [m IH_m|]; intros;
  rel_functionhood_body.
Qed.

#[global] Hint Resolve mult_rel_funct: f_rel_funct_db.

#[global] Instance mult_lookup_funct: dictionary functionhood mult := {
    lookup' := mult_rel_funct }.

Theorem mult_Suc_x_lem ds_d4ol m mult_Suc_x_lem_res:
  mult_rel (Suc_u m) ds_d4ol mult_Suc_x_lem_res
  ↔ ∃ (mult_res : Nats_u),
    mult_rel m ds_d4ol mult_res
    ∧ ∃ (add_res : Nats_u), add_rel ds_d4ol mult_res add_res ∧ mult_Suc_x_lem_res == add_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite mult_Suc_x_lem: f_rel_back.

Theorem mult_Zero_x_lem ds_d4ol mult_Zero_x_lem_res:
  mult_rel Zero_u ds_d4ol mult_Zero_x_lem_res ↔ mult_Zero_x_lem_res == Zero_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite mult_Zero_x_lem: f_rel_back.

Theorem mult_rel_ex
  (ds_d4ok : Nats_u)
  (ds_d4ok_p : Nats_wf ds_d4ok ∧ True)
  (ds_d4ol : Nats_u)
  (ds_d4ol_p : Nats_wf ds_d4ol ∧ True):
  mult_rel ds_d4ok ds_d4ol ⌊ mult (exist _ ds_d4ok ds_d4ok_p) (exist _ ds_d4ol ds_d4ol_p) -⌋.
Proof.
  Opaque mult.
  existence_lemma_pre mult;
  try revert ds_d4ol_p; generalize dependent ds_d4ol; induction ds_d4ok as [m IH_m|]; intros;
  [fix_notations;
   pose proof (IH_m
               ltac:(try clear IH_m; solver)
               ds_d4ol
               ltac:(try clear IH_m; solver)) as IH_89830954;
   try clear IH_m |
   fix_notations];
  simpl in *.
  Transparent mult.
  all: (existence_lemma_quicksolve mult; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve mult_rel_ex: rel_ax_db.

#[global] Opaque mult.

Theorem mult__mult_rel_rw
  (ds_d4ok : Nats_u)
  (ds_d4ok_p : Nats_wf ds_d4ok ∧ True)
  (ds_d4ol : Nats_u)
  (ds_d4ol_p : Nats_wf ds_d4ol ∧ True)
  (VV : Nats_u):
  ⌊ mult (exist _ ds_d4ok ds_d4ok_p) (exist _ ds_d4ol ds_d4ol_p) -⌋ = VV
  ↔ mult_rel ds_d4ok ds_d4ol VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite mult__mult_rel_rw: f_rel_funct_db.

#[global] Hint Resolve mult__mult_rel_rw: rel_ax_db.

#[global] Instance mult_lookup_rw: dictionary rwLem mult := { lookup' := mult__mult_rel_rw }.

Theorem mult__mult_rel (ds_d4ok ds_d4ol : Nats) (VV : Nats_u):
  ⌊ mult ds_d4ok ds_d4ol -⌋ = VV ↔ mult_rel ⌊ ds_d4ok ⌋ ⌊ ds_d4ol ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite mult__mult_rel: f_rel_funct_db.

Theorem mult__mult_rel' (ds_d4ok_u ds_d4ol_u : Nats_u) (ds_d4ok ds_d4ol : Nats) (VV : Nats_u):
  ds_d4ok_u = ⌊ ds_d4ok ⌋
  → (ds_d4ol_u = ⌊ ds_d4ol ⌋ → ⌊ mult ds_d4ok ds_d4ol -⌋ = VV ↔ mult_rel ds_d4ok_u ds_d4ol_u VV).
Proof.
  intros -> ->. refine (mult__mult_rel ds_d4ok ds_d4ol VV).
Qed.

#[global] Hint Resolve mult__mult_rel': f_rel_funct_db.

Theorem mult_rel_mk
  (ds_d4ok : Nats_u)
  (ds_d4ok_p : Nats_wf ds_d4ok ∧ True)
  (ds_d4ol : Nats_u)
  (ds_d4ol_p : Nats_wf ds_d4ol ∧ True):
  {VV: _ | mult_rel ds_d4ok ds_d4ol VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, mult_rel ds_d4ok ds_d4ol VV)
          (mult (exist _ ds_d4ok ds_d4ok_p) (exist _ ds_d4ol ds_d4ol_p))
          _);
  rewrite <- mult__mult_rel';
  quicksolve.
Qed.

#[global] Hint Resolve mult_rel_mk: f_rel_funct_db.

#[global] Instance mult_pack:
  @Pack
  (Nats ::RT λ (ds_d4ok : Nats), Nats ::RT λ (ds_d4ol : Nats), nilRT)
  (Nats_u ::UT (Nats_u ::UT nilUT))
  ltac:(mkProjectsArgListTG (Nats ::RT λ (ds_d4ok : Nats), Nats ::RT λ (ds_d4ol : Nats), nilRT) ((Nats_u ::UT (Nats_u ::UT nilUT))))
  Nats_u
  (λ (x_51015715 : ArgList (Nats ::RT λ (ds_d4ok : Nats), Nats ::RT λ (ds_d4ol : Nats), nilRT))
     (v_x_51015715 : Nats_u),
   ltac:(flattenP (λ (ds_d4ok ds_d4ol : Nats) (VV : Nats_u), Nats_wf VV ∧ True) x_51015715 v_x_51015715)).
Proof.
  buildPackG mult mult_rel mult__mult_rel mult_rel_funct.
Defined.

#[global] Instance mult_upack: @uPack (Nats_u ::UT (Nats_u ::UT nilUT)) Nats_u.
Proof.
  buildUPackG mult_rel mult_rel_funct.
Defined.

Definition add_dist_rmult_spec (ds_d4om ds_d4on ds_d4oo : Nats): Type :=
  {{∃ (add_res : Nats_u),
    add_rel ⌊ ds_d4om -⌋ ⌊ ds_d4on -⌋ add_res
    ∧ ∃ (mult_res : Nats_u),
      mult_rel add_res ⌊ ds_d4oo -⌋ mult_res
      ∧ ∃ (mult_res_2 : Nats_u),
        mult_rel ⌊ ds_d4on -⌋ ⌊ ds_d4oo -⌋ mult_res_2
        ∧ ∃ (mult_res_3 : Nats_u),
          mult_rel ⌊ ds_d4om -⌋ ⌊ ds_d4oo -⌋ mult_res_3
          ∧ ∃ (add_res_2 : Nats_u), add_rel mult_res_3 mult_res_2 add_res_2 ∧ mult_res == add_res_2}}.

#[global] Hint Unfold add_dist_rmult_spec: lia_unfold.

Theorem add_dist_rmult (ds_d4om ds_d4on ds_d4oo : Nats):
  add_dist_rmult_spec ds_d4om ds_d4on ds_d4oo.
Proof.
  destruct ds_d4om as [ds_d4om ds_d4om_p].
  destruct ds_d4on as [ds_d4on ds_d4on_p].
  destruct ds_d4oo as [ds_d4oo ds_d4oo_p].
  try revert ds_d4oo_p; generalize dependent ds_d4oo;
  try revert ds_d4on_p; generalize dependent ds_d4on;
  induction ds_d4om as [m IH_m|];
  intros.
  - assert (h_78908773 : add
                         ds_d4oo
                         (add
                          ⌊ mult
                            (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver))
                            (exist (λ (ds_d4oo : Nats_u), Nats_wf ds_d4oo ∧ True) ds_d4oo ltac:(solver)) -⌋
                          ⌊ mult
                            (exist (λ (ds_d4on : Nats_u), Nats_wf ds_d4on ∧ True) ds_d4on ltac:(solver))
                            (exist (λ (ds_d4oo : Nats_u), Nats_wf ds_d4oo ∧ True) ds_d4oo ltac:(solver)) -⌋)
                         ==? add
                             (add
                              ds_d4oo
                              ⌊ mult
                                (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver))
                                (exist (λ (ds_d4oo : Nats_u), Nats_wf ds_d4oo ∧ True) ds_d4oo ltac:(solver)) -⌋)
                             ⌊ mult
                               (exist (λ (ds_d4on : Nats_u), Nats_wf ds_d4on ∧ True) ds_d4on ltac:(solver))
                               (exist (λ (ds_d4oo : Nats_u), Nats_wf ds_d4oo ∧ True) ds_d4oo ltac:(solver)) -⌋).
    { refine (add_assoc
              (exist (λ (ds_d4oo : Nats_u), Nats_wf ds_d4oo ∧ True) ds_d4oo ltac:(solver))
              (mult
               (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver))
               (exist (λ (ds_d4oo : Nats_u), Nats_wf ds_d4oo ∧ True) ds_d4oo ltac:(solver)))
              (mult
               (exist (λ (ds_d4on : Nats_u), Nats_wf ds_d4on ∧ True) ds_d4on ltac:(solver))
               (exist (λ (ds_d4oo : Nats_u), Nats_wf ds_d4oo ∧ True) ds_d4oo ltac:(solver)))). }
    refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (add_res : Nats_u),
             add_rel (Suc_u m) ds_d4on add_res
             ∧ ∃ (mult_res : Nats_u),
               mult_rel add_res ds_d4oo mult_res
               ∧ ∃ (mult_res_2 : Nats_u),
                 mult_rel ds_d4on ds_d4oo mult_res_2
                 ∧ ∃ (mult_res_3 : Nats_u),
                   mult_rel (Suc_u m) ds_d4oo mult_res_3
                   ∧ ∃ (add_res_2 : Nats_u), add_rel mult_res_3 mult_res_2 add_res_2 ∧ mult_res == add_res_2)
            (IH_m
             ltac:(try clear IH_m; solver)
             ds_d4on
             ltac:(try clear IH_m; solver)
             ds_d4oo
             ltac:(try clear IH_m; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (add_res : Nats_u),
             add_rel Zero_u ds_d4on add_res
             ∧ ∃ (mult_res : Nats_u),
               mult_rel add_res ds_d4oo mult_res
               ∧ ∃ (mult_res_2 : Nats_u),
                 mult_rel ds_d4on ds_d4oo mult_res_2
                 ∧ ∃ (mult_res_3 : Nats_u),
                   mult_rel Zero_u ds_d4oo mult_res_3
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
  (ds_d4nA : Nats)
  (ds_d4nB : {ds_d4nB: Nats_u | Nats_wf ds_d4nB
                                ∧ ∃ (geqN_res : bool), geqN_rel ⌊ ds_d4nA -⌋ ds_d4nB geqN_res ∧ is_true geqN_res}):
  Type :=
  {o: Nats_u | Nats_wf o ∧ (o ≠ Zero_u ↔ ⌊ ds_d4nA -⌋ ≠ ⌊ ds_d4nB -⌋)}.

#[global] Hint Unfold sub_spec: lia_unfold.

Definition sub
  (ds_d4nA : Nats)
  (ds_d4nB : {ds_d4nB: Nats_u | Nats_wf ds_d4nB
                                ∧ ∃ (geqN_res : bool), geqN_rel ⌊ ds_d4nA -⌋ ds_d4nB geqN_res ∧ is_true geqN_res}):
  sub_spec ds_d4nA ds_d4nB.
Proof.
  destruct ds_d4nA as [ds_d4nA ds_d4nA_p].
  destruct ds_d4nB as [ds_d4nB ds_d4nB_p].
  try revert ds_d4nB_p; generalize dependent ds_d4nB; induction ds_d4nA as [m IH_m|]; intros.
  - destruct ds_d4nB as [n|].
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
  - destruct ds_d4nB as [lq_anf7205759403792810582|].
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

Theorem sub_rel_funct [ds_d4nA ds_d4nB : Nats_u]:
  ∀ (o o' : Nats_u), sub_rel ds_d4nA ds_d4nB o → (sub_rel ds_d4nA ds_d4nB o' → o = o').
Proof.
  try revert ds_d4nB_p; generalize dependent ds_d4nB; induction ds_d4nA as [m IH_m|]; intros;
  [destruct ds_d4nB as [n|] | destruct ds_d4nB as [lq_anf7205759403792810582|]];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve sub_rel_funct: f_rel_funct_db.

#[global] Instance sub_lookup_funct: dictionary functionhood sub := { lookup' := sub_rel_funct }.

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
  (ds_d4nA : Nats_u)
  (ds_d4nA_p : Nats_wf ds_d4nA ∧ True)
  (ds_d4nB : Nats_u)
  (ds_d4nB_p : Nats_wf ds_d4nB
               ∧ ∃ (geqN_res : bool), geqN_rel ds_d4nA ds_d4nB geqN_res ∧ is_true geqN_res):
  sub_rel ds_d4nA ds_d4nB ⌊ sub (exist _ ds_d4nA ds_d4nA_p) (exist _ ds_d4nB ds_d4nB_p) -⌋.
Proof.
  Opaque sub.
  existence_lemma_pre sub;
  try revert ds_d4nB_p; generalize dependent ds_d4nB; induction ds_d4nA as [m IH_m|]; intros;
  [destruct ds_d4nB as [n|];
   [fix_notations;
    pose proof (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver)) as IH_14792487;
    try clear IH_m |
    fix_notations] |
   destruct ds_d4nB as [lq_anf7205759403792810582|];
   [ | fix_notations]];
  simpl in *.
  Transparent sub.
  all: (existence_lemma_quicksolve sub; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve sub_rel_ex: rel_ax_db.

#[global] Opaque sub.

Theorem sub__sub_rel_rw
  (ds_d4nA : Nats_u)
  (ds_d4nA_p : Nats_wf ds_d4nA ∧ True)
  (ds_d4nB : Nats_u)
  (ds_d4nB_p : Nats_wf ds_d4nB
               ∧ ∃ (geqN_res : bool), geqN_rel ds_d4nA ds_d4nB geqN_res ∧ is_true geqN_res)
  (o : Nats_u):
  ⌊ sub (exist _ ds_d4nA ds_d4nA_p) (exist _ ds_d4nB ds_d4nB_p) -⌋ = o ↔ sub_rel ds_d4nA ds_d4nB o.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite sub__sub_rel_rw: f_rel_funct_db.

#[global] Hint Resolve sub__sub_rel_rw: rel_ax_db.

#[global] Instance sub_lookup_rw: dictionary rwLem sub := { lookup' := sub__sub_rel_rw }.

Theorem sub__sub_rel
  (ds_d4nA : Nats)
  (ds_d4nB : {ds_d4nB: Nats_u | Nats_wf ds_d4nB
                                ∧ ∃ (geqN_res : bool), geqN_rel ⌊ ds_d4nA -⌋ ds_d4nB geqN_res ∧ is_true geqN_res})
  (o : Nats_u):
  ⌊ sub ds_d4nA ds_d4nB -⌋ = o ↔ sub_rel ⌊ ds_d4nA ⌋ ⌊ ds_d4nB ⌋ o.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite sub__sub_rel: f_rel_funct_db.

Theorem sub__sub_rel'
  (ds_d4nA_u ds_d4nB_u : Nats_u)
  (ds_d4nA : Nats)
  (ds_d4nB : {ds_d4nB: Nats_u | Nats_wf ds_d4nB
                                ∧ ∃ (geqN_res : bool), geqN_rel ⌊ ds_d4nA -⌋ ds_d4nB geqN_res ∧ is_true geqN_res})
  (o : Nats_u):
  ds_d4nA_u = ⌊ ds_d4nA ⌋
  → (ds_d4nB_u = ⌊ ds_d4nB ⌋ → ⌊ sub ds_d4nA ds_d4nB -⌋ = o ↔ sub_rel ds_d4nA_u ds_d4nB_u o).
Proof.
  intros -> ->. refine (sub__sub_rel ds_d4nA ds_d4nB o).
Qed.

#[global] Hint Resolve sub__sub_rel': f_rel_funct_db.

Theorem sub_rel_mk
  (ds_d4nA : Nats_u)
  (ds_d4nA_p : Nats_wf ds_d4nA ∧ True)
  (ds_d4nB : Nats_u)
  (ds_d4nB_p : Nats_wf ds_d4nB
               ∧ ∃ (geqN_res : bool), geqN_rel ds_d4nA ds_d4nB geqN_res ∧ is_true geqN_res):
  {o: _ | sub_rel ds_d4nA ds_d4nB o}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ o, sub_rel ds_d4nA ds_d4nB o)
          (sub (exist _ ds_d4nA ds_d4nA_p) (exist _ ds_d4nB ds_d4nB_p))
          _);
  rewrite <- sub__sub_rel';
  quicksolve.
Qed.

#[global] Hint Resolve sub_rel_mk: f_rel_funct_db.

#[global] Instance sub_pack:
  @Pack
  (Nats
   ::RT λ (ds_d4nA : Nats),
        {ds_d4nB: Nats_u | Nats_wf ds_d4nB
                           ∧ ∃ (geqN_res : bool), geqN_rel ⌊ ds_d4nA -⌋ ds_d4nB geqN_res ∧ is_true geqN_res}
        ::RT λ (ds_d4nB : {ds_d4nB: Nats_u | Nats_wf ds_d4nB
                                             ∧ ∃ (geqN_res : bool),
                                               geqN_rel ⌊ ds_d4nA -⌋ ds_d4nB geqN_res ∧ is_true geqN_res}),
             nilRT)
  (Nats_u ::UT (Nats_u ::UT nilUT))
  ltac:(mkProjectsArgListTG (Nats
 ::RT λ (ds_d4nA : Nats),
      {ds_d4nB: Nats_u | Nats_wf ds_d4nB
                         ∧ ∃ (geqN_res : bool),
                           geqN_rel ⌊ ds_d4nA -⌋ ds_d4nB geqN_res ∧ is_true geqN_res}
      ::RT λ (ds_d4nB : {ds_d4nB: Nats_u | Nats_wf ds_d4nB
                                           ∧ ∃ (geqN_res : bool),
                                             geqN_rel ⌊ ds_d4nA -⌋ ds_d4nB geqN_res
                                             ∧ is_true geqN_res}),
           nilRT) ((Nats_u ::UT (Nats_u ::UT nilUT))))
  Nats_u
  (λ (x_78071397 : ArgList (Nats
                            ::RT λ (ds_d4nA : Nats),
                                 {ds_d4nB: Nats_u | Nats_wf ds_d4nB
                                                    ∧ ∃ (geqN_res : bool),
                                                      geqN_rel ⌊ ds_d4nA -⌋ ds_d4nB geqN_res ∧ is_true geqN_res}
                                 ::RT λ (ds_d4nB : {ds_d4nB: Nats_u | Nats_wf ds_d4nB
                                                                      ∧ ∃ (geqN_res : bool),
                                                                        geqN_rel ⌊ ds_d4nA -⌋ ds_d4nB geqN_res
                                                                        ∧ is_true geqN_res}),
                                      nilRT))
     (v_x_78071397 : Nats_u),
   ltac:(flattenP (λ (ds_d4nA : Nats)
   (ds_d4nB : {ds_d4nB: Nats_u | Nats_wf ds_d4nB
                                 ∧ ∃ (geqN_res : bool),
                                   geqN_rel ⌊ ds_d4nA -⌋ ds_d4nB geqN_res ∧ is_true geqN_res})
   (o : Nats_u),
 Nats_wf o ∧ (o ≠ Zero_u ↔ ⌊ ds_d4nA -⌋ ≠ ⌊ ds_d4nB -⌋)) x_78071397 v_x_78071397)).
Proof.
  buildPackG sub sub_rel sub__sub_rel sub_rel_funct.
Defined.

#[global] Instance sub_upack: @uPack (Nats_u ::UT (Nats_u ::UT nilUT)) Nats_u.
Proof.
  buildUPackG sub_rel sub_rel_funct.
Defined.

Definition add_sub_spec (ds_d4o4 ds_d4o5 : Nats): Type :=
  {{∃ (add_res : Nats_u),
    add_rel ⌊ ds_d4o4 -⌋ ⌊ ds_d4o5 -⌋ add_res
    ∧ ∃ (sub_res : Nats_u), sub_rel add_res ⌊ ds_d4o5 -⌋ sub_res ∧ sub_res == ⌊ ds_d4o4 -⌋}}.

#[global] Hint Unfold add_sub_spec: lia_unfold.

Theorem add_sub (ds_d4o4 ds_d4o5 : Nats): add_sub_spec ds_d4o4 ds_d4o5.
Proof.
  destruct ds_d4o4 as [ds_d4o4 ds_d4o4_p].
  destruct ds_d4o5 as [ds_d4o5 ds_d4o5_p].
  destruct ds_d4o4 as [m|].
  - induction ds_d4o5 as [lq_anf7205759403792810552 IH_lq_anf7205759403792810552|].
    + assert (h_45011131 : sub
                           (add
                            ⌊ Suc (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver)) -⌋
                            lq_anf7205759403792810552)
                           lq_anf7205759403792810552
                           ==? ⌊ Suc (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver)) -⌋).
      { refine (IH_lq_anf7205759403792810552 ltac:(try clear IH_lq_anf7205759403792810552; solver)). }
      refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∃ (add_res : Nats_u),
               add_rel (Suc_u m) (Suc_u lq_anf7205759403792810552) add_res
               ∧ ∃ (sub_res : Nats_u),
                 sub_rel add_res (Suc_u lq_anf7205759403792810552) sub_res ∧ sub_res == Suc_u m)
              (add_suc_r
               (Suc (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver)))
               (exist (λ (n : Nats_u), Nats_wf n ∧ True) lq_anf7205759403792810552 ltac:(solver)))
              ltac:(solver)).
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∃ (add_res : Nats_u),
               add_rel (Suc_u m) Zero_u add_res
               ∧ ∃ (sub_res : Nats_u), sub_rel add_res Zero_u sub_res ∧ sub_res == Suc_u m)
              (add_zero_r (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver)))
              ltac:(solver)).
  - induction ds_d4o5 as [lq_anf7205759403792810544 IH_lq_anf7205759403792810544|].
    + assert (h_14964841 : sub (add ⌊ Zero -⌋ lq_anf7205759403792810544) lq_anf7205759403792810544
                           ==? ⌊ Zero -⌋).
      { refine (IH_lq_anf7205759403792810544 ltac:(try clear IH_lq_anf7205759403792810544; solver)). }
      refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∃ (add_res : Nats_u),
               add_rel Zero_u (Suc_u lq_anf7205759403792810544) add_res
               ∧ ∃ (sub_res : Nats_u),
                 sub_rel add_res (Suc_u lq_anf7205759403792810544) sub_res ∧ sub_res == Zero_u)
              (add_suc_r Zero (exist (λ (n : Nats_u), Nats_wf n ∧ True) lq_anf7205759403792810544 ltac:(solver)))
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

Definition sub_self_spec (ds_d4nu ds_d4nv : Nats): Type :=
  {{∃ (eqN_res : bool), eqN_rel ⌊ ds_d4nu -⌋ ⌊ ds_d4nv -⌋ eqN_res ∧ is_true eqN_res
    → ∃ (sub_res : Nats_u), sub_rel ⌊ ds_d4nu -⌋ ⌊ ds_d4nv -⌋ sub_res ∧ sub_res == Zero_u}}.

#[global] Hint Unfold sub_self_spec: lia_unfold.

Theorem sub_self (ds_d4nu ds_d4nv : Nats): sub_self_spec ds_d4nu ds_d4nv.
Proof.
  destruct ds_d4nu as [ds_d4nu ds_d4nu_p].
  destruct ds_d4nv as [ds_d4nv ds_d4nv_p].
  try revert ds_d4nv_p; generalize dependent ds_d4nv; induction ds_d4nu as [m IH_m|]; intros.
  - destruct ds_d4nv as [n|].
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
             ∃ (eqN_res : bool), eqN_rel Zero_u ds_d4nv eqN_res ∧ is_true eqN_res
             → ∃ (sub_res : Nats_u), sub_rel Zero_u ds_d4nv sub_res ∧ sub_res == Zero_u)
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
