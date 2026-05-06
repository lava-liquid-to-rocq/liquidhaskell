From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Set Universe Polymorphism.
From Coq Require Import Unicode.Utf8.
Ltac solver := quicksolve.

Inductive Nats_u: Set :=
  | Suc_u: Nats_u → Nats_u | Zero_u: Nats_u.

Fixpoint Nats_eq (x y : Nats_u): bool :=
  match (x, y) with
  | (Suc_u n, Suc_u n') => true && Nats_eq n n'
  | (Zero_u, Zero_u) => true
  | (_, _) => false
  end.

Definition Nats_eq_refl : ∀ (x : Nats_u), is_true (Nats_eq x x).
Proof.
  eq_refl_rec.
Qed.

#[global] Hint Resolve Nats_eq_refl: eq_hint_db.

Definition Nats_eqb_eq : ∀ (s t : Nats_u), is_true (Nats_eq s t) → s = t.
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

Theorem Nats_wf_ref [p : Nats_u → Prop] (tm : {v: Nats_u | Nats_wf v ∧ p v}): Nats_wf ⌊ tm ⌋.
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

Definition add (m n : Nats): Nats.
Proof.
  destruct m as [m m_p].
  destruct n as [n n_p].
  try revert n_p; generalize dependent n; induction m as [m IH_m|]; intros.
  - refine (Suc (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver))).
  - refine (exist (λ (n : Nats_u), Nats_wf n ∧ True) n ltac:(solver)).
Defined.

Inductive add_rel: Nats_u → Nats_u → Nats_u → Prop :=
  | add_Zero_x: ∀ n, add_rel Zero_u n n
  | add_Suc_x: ∀ m n add_res, add_rel m n add_res → add_rel (Suc_u m) n (Suc_u add_res).

#[global] Hint Constructors add_rel: core_hint_db.

#[global] Instance add_lookup_rel: dictionary rel add := { lookup' := add_rel }.

#[global] Instance add_getF: getFunc add_rel := { getF' := add }.

Definition add_rel_funct [m n : Nats_u]:
  ∀ (VV VV' : Nats_u), add_rel m n VV → (add_rel m n VV' → VV = VV').
Proof.
  try revert n_p; generalize dependent n; induction m as [m IH_m|]; intros; rel_functionhood_body.
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
  ↔ ∃ add_res, add_rel m n add_res ∧ add_Suc_x_lem_res == Suc_u add_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite add_Suc_x_lem: f_rel_back.

Theorem add_rel_ex (m : Nats_u) (m_p : Nats_wf m ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True):
  add_rel m n ⌊ add (exist _ m m_p) (exist _ n n_p) ⌋.
Proof.
  existence_lemma_pre add;
  try revert n_p; generalize dependent n; induction m as [m IH_m|]; intros;
  [fix_notations | fix_notations];
  existence_lemma_quicksolve add;
  f__f_rel_ex_body;
  f_rel_finish.
Qed.

#[global] Hint Resolve add_rel_ex: rel_ax_db.

Opaque add.

Theorem add__add_rel_rw
  (m : Nats_u) (m_p : Nats_wf m ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True) (VV : Nats_u):
  ⌊ add (exist _ m m_p) (exist _ n n_p) ⌋ = VV ↔ add_rel m n VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite add__add_rel_rw: f_rel_funct_db.

#[global] Hint Resolve add__add_rel_rw: rel_ax_db.

#[global] Instance add_lookup_rw: dictionary rwLem add := { lookup' := add__add_rel_rw }.

Theorem add__add_rel (m n : Nats) (VV : Nats_u): ⌊ add m n ⌋ = VV ↔ add_rel ⌊ m ⌋ ⌊ n ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite add__add_rel: f_rel_funct_db.

Theorem add__add_rel' (m_u n_u : Nats_u) (m n : Nats) (VV : Nats_u):
  m_u = ⌊ m ⌋ → (n_u = ⌊ n ⌋ → ⌊ add m n ⌋ = VV ↔ add_rel m_u n_u VV).
Proof.
  intros -> ->. refine (add__add_rel m n VV).
Qed.

#[global] Hint Resolve add__add_rel': f_rel_funct_db.

Definition add_rel_mk (m : Nats_u) (m_p : Nats_wf m ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True):
  {VV: _ | add_rel m n VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, add_rel m n VV) (add (exist _ m m_p) (exist _ n n_p)) _);
  rewrite <- add__add_rel';
  quicksolve.
Qed.

#[global] Hint Resolve add_rel_mk: f_rel_funct_db.

#[global] Instance add_pack:
  @Pack
  (Nats ::RT λ (m : Nats), Nats ::RT λ (n : Nats), nilRT)
  (Nats_u ::UT (Nats_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((Nats ::RT λ (m : Nats), Nats ::RT λ (n : Nats), nilRT)) ((Nats_u ::UT (Nats_u ::UT nilUT))))
  Nats_u
  (λ (x_90321534 : ArgList (Nats ::RT λ (m : Nats), Nats ::RT λ (n : Nats), nilRT))
     (v_x_90321534 : Nats_u),
   ltac:(flattenP (λ (m n : Nats) (VV : Nats_u), Nats_wf VV ∧ True) x_90321534 v_x_90321534)).
Proof.
  buildPackG add add_rel add__add_rel add_rel_funct.
Defined.

#[global] Instance add_upack: @uPack (Nats_u ::UT (Nats_u ::UT nilUT)) Nats_u.
Proof.
  buildUPackG add_rel add_rel_funct.
Defined.

Definition add' (m n : Nats):
  {v: Nats_u | Nats_wf v
               ∧ ∀ add_res,
                 add_rel ⌊ m ⌋ ⌊ n ⌋ add_res → ∀ add_res_2, add_rel add_res Zero_u add_res_2 → add_res_2 == v}.
Proof.
  destruct m as [m m_p].
  destruct n as [n n_p].
  refine (subsumptionCast
          Nats_u
          (λ (v : Nats_u),
           Nats_wf v
           ∧ ∀ add_res,
             add_rel ⌊ m ⌋ ⌊ n ⌋ add_res → ∀ add_res_2, add_rel add_res Zero_u add_res_2 → add_res_2 == v)
          (add
           (add
            (exist (λ (m : Nats_u), Nats_wf m ∧ True) m ltac:(solver))
            (exist (λ (n : Nats_u), Nats_wf n ∧ True) n ltac:(solver)))
           Zero)
          ltac:(solver)).
Defined.

Definition add'' (m n : Nats):
  {v: Nats_u | Nats_wf v ∧ ∀ add_res, add_rel ⌊ m ⌋ ⌊ n ⌋ add_res → add_res == v}.
Proof.
  destruct m as [m m_p].
  destruct n as [n n_p].
  refine (subsumptionCast
          Nats_u
          (λ (v : Nats_u), Nats_wf v ∧ ∀ add_res, add_rel ⌊ m ⌋ ⌊ n ⌋ add_res → add_res == v)
          (add
           (exist (λ (m : Nats_u), Nats_wf m ∧ True) m ltac:(solver))
           (exist (λ (n : Nats_u), Nats_wf n ∧ True) n ltac:(solver)))
          ltac:(solver)).
Defined.

Definition add_assoc (m n o : Nats):
  {{∀ add_res,
    add_rel ⌊ n ⌋ ⌊ o ⌋ add_res
    → ∀ add_res_2,
      add_rel ⌊ m ⌋ add_res add_res_2
      → ∀ add_res_3,
        add_rel ⌊ m ⌋ ⌊ n ⌋ add_res_3
        → ∀ add_res_4, add_rel add_res_3 ⌊ o ⌋ add_res_4 → add_res_2 == add_res_4}}.
Proof.
  destruct m as [m m_p].
  destruct n as [n n_p].
  destruct o as [o o_p].
  try revert o_p; generalize dependent o; try revert n_p; generalize dependent n;
  induction m as [m IH_m|];
  intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∀ add_res,
             add_rel ⌊ n ⌋ ⌊ o ⌋ add_res
             → ∀ add_res_2,
               add_rel ⌊ m ⌋ add_res add_res_2
               → ∀ add_res_3,
                 add_rel ⌊ m ⌋ ⌊ n ⌋ add_res_3
                 → ∀ add_res_4, add_rel add_res_3 ⌊ o ⌋ add_res_4 → add_res_2 == add_res_4)
            (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver) o ltac:(try clear IH_m; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∀ add_res,
             add_rel ⌊ n ⌋ ⌊ o ⌋ add_res
             → ∀ add_res_2,
               add_rel ⌊ m ⌋ add_res add_res_2
               → ∀ add_res_3,
                 add_rel ⌊ m ⌋ ⌊ n ⌋ add_res_3
                 → ∀ add_res_4, add_rel add_res_3 ⌊ o ⌋ add_res_4 → add_res_2 == add_res_4)
            (# unit)
            ltac:(solver)).
Defined.

Definition add_suc_r (m n : Nats):
  {{∀ add_res,
    add_rel ⌊ m ⌋ ⌊ n ⌋ add_res
    → ∀ add_res_2, add_rel ⌊ m ⌋ (Suc_u ⌊ n ⌋) add_res_2 → Suc_u add_res == add_res_2}}.
Proof.
  destruct m as [m m_p].
  destruct n as [n n_p].
  try revert n_p; generalize dependent n; induction m as [m IH_m|]; intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∀ add_res,
             add_rel ⌊ m ⌋ ⌊ n ⌋ add_res
             → ∀ add_res_2, add_rel ⌊ m ⌋ (Suc_u ⌊ n ⌋) add_res_2 → Suc_u add_res == add_res_2)
            (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∀ add_res,
             add_rel ⌊ m ⌋ ⌊ n ⌋ add_res
             → ∀ add_res_2, add_rel ⌊ m ⌋ (Suc_u ⌊ n ⌋) add_res_2 → Suc_u add_res == add_res_2)
            (# unit)
            ltac:(solver)).
Defined.

Definition add_zero_l (n : Nats): {{∀ add_res, add_rel Zero_u ⌊ n ⌋ add_res → add_res == ⌊ n ⌋}}.
Proof.
  destruct n as [n n_p].
  induction n as [n IH_n|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∀ add_res, add_rel Zero_u ⌊ n ⌋ add_res → add_res == ⌊ n ⌋)
            (IH_n ltac:(try clear IH_n; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∀ add_res, add_rel Zero_u ⌊ n ⌋ add_res → add_res == ⌊ n ⌋)
            (# unit)
            ltac:(solver)).
Defined.

Definition add_zero_l_test :
  {{∀ add_res, add_rel Zero_u (Suc_u (Suc_u Zero_u)) add_res → add_res == Suc_u (Suc_u Zero_u)}}.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∀ add_res, add_rel Zero_u (Suc_u (Suc_u Zero_u)) add_res → add_res == Suc_u (Suc_u Zero_u))
          (add_zero_l (Suc (Suc Zero)))
          ltac:(solver)).
Defined.

Definition add_zero_r (n : Nats): {{∀ add_res, add_rel ⌊ n ⌋ Zero_u add_res → add_res == ⌊ n ⌋}}.
Proof.
  destruct n as [n n_p].
  induction n as [n IH_n|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∀ add_res, add_rel ⌊ n ⌋ Zero_u add_res → add_res == ⌊ n ⌋)
            (IH_n ltac:(try clear IH_n; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∀ add_res, add_rel ⌊ n ⌋ Zero_u add_res → add_res == ⌊ n ⌋)
            (# unit)
            ltac:(solver)).
Defined.

Definition eqN (m n : Nats): Bool.
Proof.
  destruct m as [m m_p].
  destruct n as [n n_p].
  try revert n_p; generalize dependent n; induction m as [m IH_m|]; intros.
  - destruct n as [n|].
    + refine (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver)).
    + refine (# false).
  - destruct n as [lq_anf7205759403792810464|].
    + refine (# false).
    + refine (# true).
Defined.

Inductive eqN_rel: Nats_u → Nats_u → bool → Prop :=
  | eqN_Zero_Zero: eqN_rel Zero_u Zero_u true
  | eqN_Zero_Suc: ∀ lq_anf7205759403792810464, eqN_rel Zero_u (Suc_u lq_anf7205759403792810464) false
  | eqN_Suc_Zero: ∀ m, eqN_rel (Suc_u m) Zero_u false
  | eqN_Suc_Suc: ∀ m n eqN_res, eqN_rel m n eqN_res → eqN_rel (Suc_u m) (Suc_u n) eqN_res.

#[global] Hint Constructors eqN_rel: core_hint_db.

#[global] Instance eqN_lookup_rel: dictionary rel eqN := { lookup' := eqN_rel }.

#[global] Instance eqN_getF: getFunc eqN_rel := { getF' := eqN }.

Definition eqN_rel_funct [m n : Nats_u]:
  ∀ (VV VV' : bool), eqN_rel m n VV → (eqN_rel m n VV' → VV = VV').
Proof.
  try revert n_p; generalize dependent n; induction m as [m IH_m|]; intros;
  [destruct n as [n|] | destruct n as [lq_anf7205759403792810464|]];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve eqN_rel_funct: f_rel_funct_db.

Theorem eqN_Zero_Zero_lem eqN_Zero_Zero_lem_res:
  eqN_rel Zero_u Zero_u eqN_Zero_Zero_lem_res ↔ eqN_Zero_Zero_lem_res == true.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite eqN_Zero_Zero_lem: f_rel_back.

Theorem eqN_Zero_Suc_lem lq_anf7205759403792810464 eqN_Zero_Suc_lem_res:
  eqN_rel Zero_u (Suc_u lq_anf7205759403792810464) eqN_Zero_Suc_lem_res
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
  ↔ ∃ eqN_res, eqN_rel m n eqN_res ∧ eqN_Suc_Suc_lem_res == eqN_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite eqN_Suc_Suc_lem: f_rel_back.

Theorem eqN_rel_ex (m : Nats_u) (m_p : Nats_wf m ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True):
  eqN_rel m n ⌊ eqN (exist _ m m_p) (exist _ n n_p) ⌋.
Proof.
  existence_lemma_pre eqN;
  try revert n_p; generalize dependent n; induction m as [m IH_m|]; intros;
  [destruct n as [n|];
   [fix_notations;
    pose proof (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver)) as IH_14792487;
    try clear IH_m |
    fix_notations] |
   destruct n as [lq_anf7205759403792810464|];
   [fix_notations | fix_notations]];
  existence_lemma_quicksolve eqN;
  f__f_rel_ex_body;
  f_rel_finish.
Qed.

#[global] Hint Resolve eqN_rel_ex: rel_ax_db.

Opaque eqN.

Theorem eqN__eqN_rel_rw
  (m : Nats_u) (m_p : Nats_wf m ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True) (VV : bool):
  ⌊ eqN (exist _ m m_p) (exist _ n n_p) ⌋ = VV ↔ eqN_rel m n VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite eqN__eqN_rel_rw: f_rel_funct_db.

#[global] Hint Resolve eqN__eqN_rel_rw: rel_ax_db.

#[global] Instance eqN_lookup_rw: dictionary rwLem eqN := { lookup' := eqN__eqN_rel_rw }.

Theorem eqN__eqN_rel (m n : Nats) (VV : bool): ⌊ eqN m n ⌋ = VV ↔ eqN_rel ⌊ m ⌋ ⌊ n ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite eqN__eqN_rel: f_rel_funct_db.

Theorem eqN__eqN_rel' (m_u n_u : Nats_u) (m n : Nats) (VV : bool):
  m_u = ⌊ m ⌋ → (n_u = ⌊ n ⌋ → ⌊ eqN m n ⌋ = VV ↔ eqN_rel m_u n_u VV).
Proof.
  intros -> ->. refine (eqN__eqN_rel m n VV).
Qed.

#[global] Hint Resolve eqN__eqN_rel': f_rel_funct_db.

Definition eqN_rel_mk (m : Nats_u) (m_p : Nats_wf m ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True):
  {VV: _ | eqN_rel m n VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, eqN_rel m n VV) (eqN (exist _ m m_p) (exist _ n n_p)) _);
  rewrite <- eqN__eqN_rel';
  quicksolve.
Qed.

#[global] Hint Resolve eqN_rel_mk: f_rel_funct_db.

#[global] Instance eqN_pack:
  @Pack
  (Nats ::RT λ (m : Nats), Nats ::RT λ (n : Nats), nilRT)
  (Nats_u ::UT (Nats_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((Nats ::RT λ (m : Nats), Nats ::RT λ (n : Nats), nilRT)) ((Nats_u ::UT (Nats_u ::UT nilUT))))
  bool
  (λ (x_90321534 : ArgList (Nats ::RT λ (m : Nats), Nats ::RT λ (n : Nats), nilRT))
     (v_x_90321534 : bool),
   ltac:(flattenP (λ (m n : Nats) (VV : bool), True) x_90321534 v_x_90321534)).
Proof.
  buildPackG eqN eqN_rel eqN__eqN_rel eqN_rel_funct.
Defined.

#[global] Instance eqN_upack: @uPack (Nats_u ::UT (Nats_u ::UT nilUT)) bool.
Proof.
  buildUPackG eqN_rel eqN_rel_funct.
Defined.

Definition test_eqN : {r : bool | is_true r}.
Proof.
  refine (subsumptionCast
          bool
          (λ (r : bool), is_true r)
          (eqN (Suc (Suc (Suc Zero))) (Suc (Suc (Suc Zero))))
          ltac:(solver)).
Defined.

Definition test_eqN' : {r : bool | ¬ is_true r}.
Proof.
  refine (subsumptionCast
          bool
          (λ (r : bool), ¬ is_true r)
          (eqN (Suc (Suc Zero)) (Suc Zero))
          ltac:(solver)).
Defined.

Definition geqN (m n : Nats): Bool.
Proof.
  destruct m as [m m_p].
  destruct n as [n n_p].
  try revert m_p; generalize dependent m;
  induction n as [lq_anf7205759403792810461 IH_lq_anf7205759403792810461|];
  intros.
  - destruct m as [m|].
    + refine (IH_lq_anf7205759403792810461
              ltac:(try clear IH_lq_anf7205759403792810461; solver)
              m
              ltac:(try clear IH_lq_anf7205759403792810461; solver)).
    + refine (# false).
  - refine (# true).
Defined.

Inductive geqN_rel: Nats_u → Nats_u → bool → Prop :=
  | geqN_x_Zero: ∀ m, geqN_rel m Zero_u true
  | geqN_Zero_Suc: ∀ lq_anf7205759403792810461,
                   geqN_rel Zero_u (Suc_u lq_anf7205759403792810461) false
  | geqN_Suc_Suc: ∀ m lq_anf7205759403792810461 geqN_res,
                  geqN_rel m lq_anf7205759403792810461 geqN_res
                  → geqN_rel (Suc_u m) (Suc_u lq_anf7205759403792810461) geqN_res.

#[global] Hint Constructors geqN_rel: core_hint_db.

#[global] Instance geqN_lookup_rel: dictionary rel geqN := { lookup' := geqN_rel }.

#[global] Instance geqN_getF: getFunc geqN_rel := { getF' := geqN }.

Definition geqN_rel_funct [m n : Nats_u]:
  ∀ (VV VV' : bool), geqN_rel m n VV → (geqN_rel m n VV' → VV = VV').
Proof.
  try revert m_p; generalize dependent m;
  induction n as [lq_anf7205759403792810461 IH_lq_anf7205759403792810461|];
  intros;
  [destruct m as [m|] |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve geqN_rel_funct: f_rel_funct_db.

Theorem geqN_x_Zero_lem m geqN_x_Zero_lem_res:
  geqN_rel m Zero_u geqN_x_Zero_lem_res ↔ geqN_x_Zero_lem_res == true.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite geqN_x_Zero_lem: f_rel_back.

Theorem geqN_Zero_Suc_lem lq_anf7205759403792810461 geqN_Zero_Suc_lem_res:
  geqN_rel Zero_u (Suc_u lq_anf7205759403792810461) geqN_Zero_Suc_lem_res
  ↔ geqN_Zero_Suc_lem_res == false.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite geqN_Zero_Suc_lem: f_rel_back.

Theorem geqN_Suc_Suc_lem lq_anf7205759403792810461 m geqN_Suc_Suc_lem_res:
  geqN_rel (Suc_u m) (Suc_u lq_anf7205759403792810461) geqN_Suc_Suc_lem_res
  ↔ ∃ geqN_res, geqN_rel m lq_anf7205759403792810461 geqN_res ∧ geqN_Suc_Suc_lem_res == geqN_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite geqN_Suc_Suc_lem: f_rel_back.

Theorem geqN_rel_ex (m : Nats_u) (m_p : Nats_wf m ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True):
  geqN_rel m n ⌊ geqN (exist _ m m_p) (exist _ n n_p) ⌋.
Proof.
  existence_lemma_pre geqN;
  try revert m_p; generalize dependent m;
  induction n as [lq_anf7205759403792810461 IH_lq_anf7205759403792810461|];
  intros;
  [destruct m as [m|];
   [fix_notations;
    pose proof (IH_lq_anf7205759403792810461
                ltac:(try clear IH_lq_anf7205759403792810461; solver)
                m
                ltac:(try clear IH_lq_anf7205759403792810461; solver)) as IH_28387485;
    try clear IH_lq_anf7205759403792810461 |
    fix_notations] |
   fix_notations];
  existence_lemma_quicksolve geqN;
  f__f_rel_ex_body;
  f_rel_finish.
Qed.

#[global] Hint Resolve geqN_rel_ex: rel_ax_db.

Opaque geqN.

Theorem geqN__geqN_rel_rw
  (m : Nats_u) (m_p : Nats_wf m ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True) (VV : bool):
  ⌊ geqN (exist _ m m_p) (exist _ n n_p) ⌋ = VV ↔ geqN_rel m n VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite geqN__geqN_rel_rw: f_rel_funct_db.

#[global] Hint Resolve geqN__geqN_rel_rw: rel_ax_db.

#[global] Instance geqN_lookup_rw: dictionary rwLem geqN := { lookup' := geqN__geqN_rel_rw }.

Theorem geqN__geqN_rel (m n : Nats) (VV : bool): ⌊ geqN m n ⌋ = VV ↔ geqN_rel ⌊ m ⌋ ⌊ n ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite geqN__geqN_rel: f_rel_funct_db.

Theorem geqN__geqN_rel' (m_u n_u : Nats_u) (m n : Nats) (VV : bool):
  m_u = ⌊ m ⌋ → (n_u = ⌊ n ⌋ → ⌊ geqN m n ⌋ = VV ↔ geqN_rel m_u n_u VV).
Proof.
  intros -> ->. refine (geqN__geqN_rel m n VV).
Qed.

#[global] Hint Resolve geqN__geqN_rel': f_rel_funct_db.

Definition geqN_rel_mk (m : Nats_u) (m_p : Nats_wf m ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True):
  {VV: _ | geqN_rel m n VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, geqN_rel m n VV) (geqN (exist _ m m_p) (exist _ n n_p)) _);
  rewrite <- geqN__geqN_rel';
  quicksolve.
Qed.

#[global] Hint Resolve geqN_rel_mk: f_rel_funct_db.

#[global] Instance geqN_pack:
  @Pack
  (Nats ::RT λ (m : Nats), Nats ::RT λ (n : Nats), nilRT)
  (Nats_u ::UT (Nats_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((Nats ::RT λ (m : Nats), Nats ::RT λ (n : Nats), nilRT)) ((Nats_u ::UT (Nats_u ::UT nilUT))))
  bool
  (λ (x_90321534 : ArgList (Nats ::RT λ (m : Nats), Nats ::RT λ (n : Nats), nilRT))
     (v_x_90321534 : bool),
   ltac:(flattenP (λ (m n : Nats) (VV : bool), True) x_90321534 v_x_90321534)).
Proof.
  buildPackG geqN geqN_rel geqN__geqN_rel geqN_rel_funct.
Defined.

#[global] Instance geqN_upack: @uPack (Nats_u ::UT (Nats_u ::UT nilUT)) bool.
Proof.
  buildUPackG geqN_rel geqN_rel_funct.
Defined.

Definition mult (m n : Nats): Nats.
Proof.
  destruct m as [m m_p].
  destruct n as [n n_p].
  try revert n_p; generalize dependent n; induction m as [m IH_m|]; intros.
  - refine (add
            (exist (λ (n : Nats_u), Nats_wf n ∧ True) n ltac:(solver))
            (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver))).
  - refine Zero.
Defined.

Inductive mult_rel: Nats_u → Nats_u → Nats_u → Prop :=
  | mult_Zero_x: ∀ n, mult_rel Zero_u n Zero_u
  | mult_Suc_x: ∀ m n mult_res,
                mult_rel m n mult_res → ∀ add_res, add_rel n mult_res add_res → mult_rel (Suc_u m) n add_res.

#[global] Hint Constructors mult_rel: core_hint_db.

#[global] Instance mult_lookup_rel: dictionary rel mult := { lookup' := mult_rel }.

#[global] Instance mult_getF: getFunc mult_rel := { getF' := mult }.

Definition mult_rel_funct [m n : Nats_u]:
  ∀ (VV VV' : Nats_u), mult_rel m n VV → (mult_rel m n VV' → VV = VV').
Proof.
  try revert n_p; generalize dependent n; induction m as [m IH_m|]; intros; rel_functionhood_body.
Qed.

#[global] Hint Resolve mult_rel_funct: f_rel_funct_db.

Theorem mult_Zero_x_lem n mult_Zero_x_lem_res:
  mult_rel Zero_u n mult_Zero_x_lem_res ↔ mult_Zero_x_lem_res == Zero_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite mult_Zero_x_lem: f_rel_back.

Theorem mult_Suc_x_lem m n mult_Suc_x_lem_res:
  mult_rel (Suc_u m) n mult_Suc_x_lem_res
  ↔ ∃ mult_res,
    mult_rel m n mult_res ∧ ∃ add_res, add_rel n mult_res add_res ∧ mult_Suc_x_lem_res == add_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite mult_Suc_x_lem: f_rel_back.

Theorem mult_rel_ex (m : Nats_u) (m_p : Nats_wf m ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True):
  mult_rel m n ⌊ mult (exist _ m m_p) (exist _ n n_p) ⌋.
Proof.
  existence_lemma_pre mult;
  try revert n_p; generalize dependent n; induction m as [m IH_m|]; intros;
  [fix_notations | fix_notations];
  existence_lemma_quicksolve mult;
  f__f_rel_ex_body;
  f_rel_finish.
Qed.

#[global] Hint Resolve mult_rel_ex: rel_ax_db.

Opaque mult.

Theorem mult__mult_rel_rw
  (m : Nats_u) (m_p : Nats_wf m ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True) (VV : Nats_u):
  ⌊ mult (exist _ m m_p) (exist _ n n_p) ⌋ = VV ↔ mult_rel m n VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite mult__mult_rel_rw: f_rel_funct_db.

#[global] Hint Resolve mult__mult_rel_rw: rel_ax_db.

#[global] Instance mult_lookup_rw: dictionary rwLem mult := { lookup' := mult__mult_rel_rw }.

Theorem mult__mult_rel (m n : Nats) (VV : Nats_u): ⌊ mult m n ⌋ = VV ↔ mult_rel ⌊ m ⌋ ⌊ n ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite mult__mult_rel: f_rel_funct_db.

Theorem mult__mult_rel' (m_u n_u : Nats_u) (m n : Nats) (VV : Nats_u):
  m_u = ⌊ m ⌋ → (n_u = ⌊ n ⌋ → ⌊ mult m n ⌋ = VV ↔ mult_rel m_u n_u VV).
Proof.
  intros -> ->. refine (mult__mult_rel m n VV).
Qed.

#[global] Hint Resolve mult__mult_rel': f_rel_funct_db.

Definition mult_rel_mk (m : Nats_u) (m_p : Nats_wf m ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True):
  {VV: _ | mult_rel m n VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, mult_rel m n VV) (mult (exist _ m m_p) (exist _ n n_p)) _);
  rewrite <- mult__mult_rel';
  quicksolve.
Qed.

#[global] Hint Resolve mult_rel_mk: f_rel_funct_db.

#[global] Instance mult_pack:
  @Pack
  (Nats ::RT λ (m : Nats), Nats ::RT λ (n : Nats), nilRT)
  (Nats_u ::UT (Nats_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((Nats ::RT λ (m : Nats), Nats ::RT λ (n : Nats), nilRT)) ((Nats_u ::UT (Nats_u ::UT nilUT))))
  Nats_u
  (λ (x_90321534 : ArgList (Nats ::RT λ (m : Nats), Nats ::RT λ (n : Nats), nilRT))
     (v_x_90321534 : Nats_u),
   ltac:(flattenP (λ (m n : Nats) (VV : Nats_u), Nats_wf VV ∧ True) x_90321534 v_x_90321534)).
Proof.
  buildPackG mult mult_rel mult__mult_rel mult_rel_funct.
Defined.

#[global] Instance mult_upack: @uPack (Nats_u ::UT (Nats_u ::UT nilUT)) Nats_u.
Proof.
  buildUPackG mult_rel mult_rel_funct.
Defined.

Definition add_dist_rmult (m n o : Nats):
  {{∀ add_res,
    add_rel ⌊ m ⌋ ⌊ n ⌋ add_res
    → ∀ mult_res,
      mult_rel add_res ⌊ o ⌋ mult_res
      → ∀ mult_res_2,
        mult_rel ⌊ n ⌋ ⌊ o ⌋ mult_res_2
        → ∀ mult_res_3,
          mult_rel ⌊ m ⌋ ⌊ o ⌋ mult_res_3
          → ∀ add_res_2, add_rel mult_res_3 mult_res_2 add_res_2 → mult_res == add_res_2}}.
Proof.
  destruct m as [m m_p].
  destruct n as [n n_p].
  destruct o as [o o_p].
  try revert o_p; generalize dependent o; try revert n_p; generalize dependent n;
  induction m as [m IH_m|];
  intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∀ add_res,
             add_rel ⌊ m ⌋ ⌊ n ⌋ add_res
             → ∀ mult_res,
               mult_rel add_res ⌊ o ⌋ mult_res
               → ∀ mult_res_2,
                 mult_rel ⌊ n ⌋ ⌊ o ⌋ mult_res_2
                 → ∀ mult_res_3,
                   mult_rel ⌊ m ⌋ ⌊ o ⌋ mult_res_3
                   → ∀ add_res_2, add_rel mult_res_3 mult_res_2 add_res_2 → mult_res == add_res_2)
            (let _: ∀ add_res,
                    add_rel
                    ⌊ mult
                      (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver))
                      (exist (λ (o : Nats_u), Nats_wf o ∧ True) o ltac:(solver)) ⌋
                    ⌊ mult
                      (exist (λ (n : Nats_u), Nats_wf n ∧ True) n ltac:(solver))
                      (exist (λ (o : Nats_u), Nats_wf o ∧ True) o ltac:(solver)) ⌋
                    add_res
                    → ∀ add_res_2,
                      add_rel o add_res add_res_2
                      → ∀ add_res_3,
                        add_rel
                        o
                        ⌊ mult
                          (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver))
                          (exist (λ (o : Nats_u), Nats_wf o ∧ True) o ltac:(solver)) ⌋
                        add_res_3
                        → ∀ add_res_4,
                          add_rel
                          add_res_3
                          ⌊ mult
                            (exist (λ (n : Nats_u), Nats_wf n ∧ True) n ltac:(solver))
                            (exist (λ (o : Nats_u), Nats_wf o ∧ True) o ltac:(solver)) ⌋
                          add_res_4
                          → add_res_2 == add_res_4 :=
             ⌈ add_assoc
               (exist (λ (o : Nats_u), Nats_wf o ∧ True) o ltac:(solver))
               (mult
                (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver))
                (exist (λ (o : Nats_u), Nats_wf o ∧ True) o ltac:(solver)))
               (mult
                (exist (λ (n : Nats_u), Nats_wf n ∧ True) n ltac:(solver))
                (exist (λ (o : Nats_u), Nats_wf o ∧ True) o ltac:(solver))) ⌉ in
             IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver) o ltac:(try clear IH_m; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∀ add_res,
             add_rel ⌊ m ⌋ ⌊ n ⌋ add_res
             → ∀ mult_res,
               mult_rel add_res ⌊ o ⌋ mult_res
               → ∀ mult_res_2,
                 mult_rel ⌊ n ⌋ ⌊ o ⌋ mult_res_2
                 → ∀ mult_res_3,
                   mult_rel ⌊ m ⌋ ⌊ o ⌋ mult_res_3
                   → ∀ add_res_2, add_rel mult_res_3 mult_res_2 add_res_2 → mult_res == add_res_2)
            (# unit)
            ltac:(solver)).
Defined.

Definition one : Nats.
Proof.
  refine (Suc Zero).
Defined.

Inductive one_rel: Nats_u → Prop :=
  | one_Constr: one_rel (Suc_u Zero_u).

#[global] Hint Constructors one_rel: core_hint_db.

#[global] Instance one_lookup_rel: dictionary rel one := { lookup' := one_rel }.

#[global] Instance one_getF: getFunc one_rel := { getF' := one }.

Definition one_rel_funct : ∀ (VV VV' : Nats_u), one_rel VV → (one_rel VV' → VV = VV').
Proof.
  rel_functionhood_body.
Qed.

#[global] Hint Resolve one_rel_funct: f_rel_funct_db.

Theorem one_inv_lem one_inv_lem_res: one_rel one_inv_lem_res ↔ one_inv_lem_res == Suc_u Zero_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite one_inv_lem: f_rel_back.

Theorem one_rel_ex : one_rel ⌊ one ⌋.
Proof.
  existence_lemma_pre one;
  fix_notations;
  existence_lemma_quicksolve one;
  f__f_rel_ex_body;
  f_rel_finish.
Qed.

#[global] Hint Resolve one_rel_ex: rel_ax_db.

Opaque one.

Theorem one__one_rel_rw (VV : Nats_u): ⌊ one ⌋ = VV ↔ one_rel VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite one__one_rel_rw: f_rel_funct_db.

#[global] Hint Resolve one__one_rel_rw: rel_ax_db.

#[global] Instance one_lookup_rw: dictionary rwLem one := { lookup' := one__one_rel_rw }.

Theorem one__one_rel (VV : Nats_u): ⌊ one ⌋ = VV ↔ one_rel VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite one__one_rel: f_rel_funct_db.

Theorem one__one_rel' (VV : Nats_u): ⌊ one ⌋ = VV ↔ one_rel VV.
Proof.
  intros. refine (one__one_rel VV).
Qed.

#[global] Hint Resolve one__one_rel': f_rel_funct_db.

Definition one_rel_mk : {VV: _ | one_rel VV}.
Proof.
  intros; refine (subsumptionCast _ (λ VV, one_rel VV) one _); rewrite <- one__one_rel'; quicksolve.
Qed.

#[global] Hint Resolve one_rel_mk: f_rel_funct_db.

Definition sub
  (m : Nats) (n : {n: Nats_u | Nats_wf n ∧ ∀ geqN_res, geqN_rel ⌊ m ⌋ n geqN_res → is_true geqN_res}):
  {o: Nats_u | Nats_wf o ∧ (o ≠ Zero_u ↔ ⌊ m ⌋ ≠ ⌊ n ⌋)}.
Proof.
  destruct m as [m m_p].
  destruct n as [n n_p].
  try revert n_p; generalize dependent n; induction m as [m IH_m|]; intros.
  - destruct n as [n|].
    + refine (subsumptionCast
              Nats_u
              (λ (o : Nats_u), Nats_wf o ∧ (o ≠ Zero_u ↔ ⌊ m ⌋ ≠ ⌊ n ⌋))
              (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver))
              ltac:(solver)).
    + refine (subsumptionCast
              Nats_u
              (λ (o : Nats_u), Nats_wf o ∧ (o ≠ Zero_u ↔ ⌊ m ⌋ ≠ ⌊ n ⌋))
              (Suc (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver)))
              ltac:(solver)).
  - destruct n as [lq_anf7205759403792810480|].
    + intros; exfalso; solver.
    + refine (subsumptionCast
              Nats_u
              (λ (o : Nats_u), Nats_wf o ∧ (o ≠ Zero_u ↔ ⌊ m ⌋ ≠ ⌊ n ⌋))
              Zero
              ltac:(solver)).
Defined.

Inductive sub_rel: Nats_u → Nats_u → Nats_u → Prop :=
  | sub_Zero_Zero: sub_rel Zero_u Zero_u Zero_u
  | sub_Suc_Zero: ∀ m, sub_rel (Suc_u m) Zero_u (Suc_u m)
  | sub_Suc_Suc: ∀ m n sub_res, sub_rel m n sub_res → sub_rel (Suc_u m) (Suc_u n) sub_res.

#[global] Hint Constructors sub_rel: core_hint_db.

#[global] Instance sub_lookup_rel: dictionary rel sub := { lookup' := sub_rel }.

#[global] Instance sub_getF: getFunc sub_rel := { getF' := sub }.

Definition sub_rel_funct [m n : Nats_u]:
  ∀ (o o' : Nats_u), sub_rel m n o → (sub_rel m n o' → o = o').
Proof.
  try revert n_p; generalize dependent n; induction m as [m IH_m|]; intros;
  [destruct n as [n|] | destruct n as [lq_anf7205759403792810480|]];
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
  ↔ ∃ sub_res, sub_rel m n sub_res ∧ sub_Suc_Suc_lem_res == sub_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite sub_Suc_Suc_lem: f_rel_back.

Theorem sub_rel_ex
  (m : Nats_u)
  (m_p : Nats_wf m ∧ True)
  (n : Nats_u)
  (n_p : Nats_wf n ∧ ∀ geqN_res, geqN_rel m n geqN_res → is_true geqN_res):
  sub_rel m n ⌊ sub (exist _ m m_p) (exist _ n n_p) ⌋.
Proof.
  existence_lemma_pre sub;
  try revert n_p; generalize dependent n; induction m as [m IH_m|]; intros;
  [destruct n as [n|];
   [fix_notations;
    pose proof (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver)) as IH_14792487;
    try clear IH_m |
    fix_notations] |
   destruct n as [lq_anf7205759403792810480|];
   [ | fix_notations]];
  existence_lemma_quicksolve sub;
  f__f_rel_ex_body;
  f_rel_finish.
Qed.

#[global] Hint Resolve sub_rel_ex: rel_ax_db.

Opaque sub.

Theorem sub__sub_rel_rw
  (m : Nats_u)
  (m_p : Nats_wf m ∧ True)
  (n : Nats_u)
  (n_p : Nats_wf n ∧ ∀ geqN_res, geqN_rel m n geqN_res → is_true geqN_res)
  (o : Nats_u):
  ⌊ sub (exist _ m m_p) (exist _ n n_p) ⌋ = o ↔ sub_rel m n o.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite sub__sub_rel_rw: f_rel_funct_db.

#[global] Hint Resolve sub__sub_rel_rw: rel_ax_db.

#[global] Instance sub_lookup_rw: dictionary rwLem sub := { lookup' := sub__sub_rel_rw }.

Theorem sub__sub_rel
  (m : Nats)
  (n : {n: Nats_u | Nats_wf n ∧ ∀ geqN_res, geqN_rel ⌊ m ⌋ n geqN_res → is_true geqN_res})
  (o : Nats_u):
  ⌊ sub m n ⌋ = o ↔ sub_rel ⌊ m ⌋ ⌊ n ⌋ o.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite sub__sub_rel: f_rel_funct_db.

Theorem sub__sub_rel'
  (m_u n_u : Nats_u)
  (m : Nats)
  (n : {n: Nats_u | Nats_wf n ∧ ∀ geqN_res, geqN_rel ⌊ m ⌋ n geqN_res → is_true geqN_res})
  (o : Nats_u):
  m_u = ⌊ m ⌋ → (n_u = ⌊ n ⌋ → ⌊ sub m n ⌋ = o ↔ sub_rel m_u n_u o).
Proof.
  intros -> ->. refine (sub__sub_rel m n o).
Qed.

#[global] Hint Resolve sub__sub_rel': f_rel_funct_db.

Definition sub_rel_mk
  (m : Nats_u)
  (m_p : Nats_wf m ∧ True)
  (n : Nats_u)
  (n_p : Nats_wf n ∧ ∀ geqN_res, geqN_rel m n geqN_res → is_true geqN_res):
  {o: _ | sub_rel m n o}.
Proof.
  intros;
  refine (subsumptionCast _ (λ o, sub_rel m n o) (sub (exist _ m m_p) (exist _ n n_p)) _);
  rewrite <- sub__sub_rel';
  quicksolve.
Qed.

#[global] Hint Resolve sub_rel_mk: f_rel_funct_db.

#[global] Instance sub_pack:
  @Pack
  (Nats
   ::RT λ (m : Nats),
        {n: Nats_u | Nats_wf n ∧ ∀ geqN_res, geqN_rel ⌊ m ⌋ n geqN_res → is_true geqN_res}
        ::RT λ (n : {n: Nats_u | Nats_wf n ∧ ∀ geqN_res, geqN_rel ⌊ m ⌋ n geqN_res → is_true geqN_res}),
             nilRT)
  (Nats_u ::UT (Nats_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((Nats
  ::RT λ (m : Nats),
       {n: Nats_u | Nats_wf n
                    ∧ ∀ geqN_res, geqN_rel ⌊ m ⌋ n geqN_res → is_true geqN_res}
       ::RT λ (n : {n: Nats_u | Nats_wf n
                                ∧ ∀ geqN_res, geqN_rel ⌊ m ⌋ n geqN_res → is_true geqN_res}),
            nilRT)) ((Nats_u ::UT (Nats_u ::UT nilUT))))
  Nats_u
  (λ (x_19226769 : ArgList (Nats
                            ::RT λ (m : Nats),
                                 {n: Nats_u | Nats_wf n ∧ ∀ geqN_res, geqN_rel ⌊ m ⌋ n geqN_res → is_true geqN_res}
                                 ::RT λ (n : {n: Nats_u | Nats_wf n
                                                          ∧ ∀ geqN_res, geqN_rel ⌊ m ⌋ n geqN_res → is_true geqN_res}),
                                      nilRT))
     (v_x_19226769 : Nats_u),
   ltac:(flattenP (λ (m : Nats)
   (n : {n: Nats_u | Nats_wf n
                     ∧ ∀ geqN_res, geqN_rel ⌊ m ⌋ n geqN_res → is_true geqN_res})
   (o : Nats_u),
 Nats_wf o ∧ (o ≠ Zero_u ↔ ⌊ m ⌋ ≠ ⌊ n ⌋)) x_19226769 v_x_19226769)).
Proof.
  buildPackG sub sub_rel sub__sub_rel sub_rel_funct.
Defined.

#[global] Instance sub_upack: @uPack (Nats_u ::UT (Nats_u ::UT nilUT)) Nats_u.
Proof.
  buildUPackG sub_rel sub_rel_funct.
Defined.

Definition add_sub (m n : Nats):
  {{∀ add_res,
    add_rel ⌊ m ⌋ ⌊ n ⌋ add_res → ∀ sub_res, sub_rel add_res ⌊ n ⌋ sub_res → sub_res == ⌊ m ⌋}}.
Proof.
  destruct m as [m m_p].
  destruct n as [n n_p].
  destruct m as [m|].
  - induction n as [lq_anf7205759403792810450 IH_lq_anf7205759403792810450|].
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∀ add_res,
               add_rel ⌊ m ⌋ ⌊ n ⌋ add_res → ∀ sub_res, sub_rel add_res ⌊ n ⌋ sub_res → sub_res == ⌊ m ⌋)
              (let _: ∀ add_res,
                      add_rel (Suc_u m) lq_anf7205759403792810450 add_res
                      → ∀ sub_res, sub_rel add_res lq_anf7205759403792810450 sub_res → sub_res == Suc_u m :=
               ⌈ IH_lq_anf7205759403792810450 ltac:(try clear IH_lq_anf7205759403792810450; solver) ⌉ in
               add_suc_r
               (Suc (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver)))
               (exist (λ (n : Nats_u), Nats_wf n ∧ True) lq_anf7205759403792810450 ltac:(solver)))
              ltac:(solver)).
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∀ add_res,
               add_rel ⌊ m ⌋ ⌊ n ⌋ add_res → ∀ sub_res, sub_rel add_res ⌊ n ⌋ sub_res → sub_res == ⌊ m ⌋)
              (add_zero_r (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver)))
              ltac:(solver)).
  - induction n as [lq_anf7205759403792810442 IH_lq_anf7205759403792810442|].
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∀ add_res,
               add_rel ⌊ m ⌋ ⌊ n ⌋ add_res → ∀ sub_res, sub_rel add_res ⌊ n ⌋ sub_res → sub_res == ⌊ m ⌋)
              (let _: ∀ add_res,
                      add_rel Zero_u lq_anf7205759403792810442 add_res
                      → ∀ sub_res, sub_rel add_res lq_anf7205759403792810442 sub_res → sub_res == Zero_u :=
               ⌈ IH_lq_anf7205759403792810442 ltac:(try clear IH_lq_anf7205759403792810442; solver) ⌉ in
               add_suc_r Zero (exist (λ (n : Nats_u), Nats_wf n ∧ True) lq_anf7205759403792810442 ltac:(solver)))
              ltac:(solver)).
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∀ add_res,
               add_rel ⌊ m ⌋ ⌊ n ⌋ add_res → ∀ sub_res, sub_rel add_res ⌊ n ⌋ sub_res → sub_res == ⌊ m ⌋)
              (# unit)
              ltac:(solver)).
Defined.

Definition sub_self (m n : Nats):
  {{∀ eqN_res,
    eqN_rel ⌊ m ⌋ ⌊ n ⌋ eqN_res
    → ∀ sub_res, sub_rel ⌊ m ⌋ ⌊ n ⌋ sub_res → (is_true eqN_res → sub_res == Zero_u)}}.
Proof.
  destruct m as [m m_p].
  destruct n as [n n_p].
  try revert n_p; generalize dependent n; induction m as [m IH_m|]; intros.
  - destruct n as [n|].
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∀ eqN_res,
               eqN_rel ⌊ m ⌋ ⌊ n ⌋ eqN_res
               → ∀ sub_res, sub_rel ⌊ m ⌋ ⌊ n ⌋ sub_res → (is_true eqN_res → sub_res == Zero_u))
              (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver))
              ltac:(solver)).
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∀ eqN_res,
               eqN_rel ⌊ m ⌋ ⌊ n ⌋ eqN_res
               → ∀ sub_res, sub_rel ⌊ m ⌋ ⌊ n ⌋ sub_res → (is_true eqN_res → sub_res == Zero_u))
              (# unit)
              ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∀ eqN_res,
             eqN_rel ⌊ m ⌋ ⌊ n ⌋ eqN_res
             → ∀ sub_res, sub_rel ⌊ m ⌋ ⌊ n ⌋ sub_res → (is_true eqN_res → sub_res == Zero_u))
            (# unit)
            ltac:(solver)).
Defined.

Definition two : Nats.
Proof.
  refine (Suc one).
Defined.

Inductive two_rel: Nats_u → Prop :=
  | two_Constr: ∀ one_res, one_rel one_res → two_rel (Suc_u one_res).

#[global] Hint Constructors two_rel: core_hint_db.

#[global] Instance two_lookup_rel: dictionary rel two := { lookup' := two_rel }.

#[global] Instance two_getF: getFunc two_rel := { getF' := two }.

Definition two_rel_funct : ∀ (VV VV' : Nats_u), two_rel VV → (two_rel VV' → VV = VV').
Proof.
  rel_functionhood_body.
Qed.

#[global] Hint Resolve two_rel_funct: f_rel_funct_db.

Theorem two_inv_lem two_inv_lem_res:
  two_rel two_inv_lem_res ↔ ∃ one_res, one_rel one_res ∧ two_inv_lem_res == Suc_u one_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite two_inv_lem: f_rel_back.

Theorem two_rel_ex : two_rel ⌊ two ⌋.
Proof.
  existence_lemma_pre two;
  fix_notations;
  existence_lemma_quicksolve two;
  f__f_rel_ex_body;
  f_rel_finish.
Qed.

#[global] Hint Resolve two_rel_ex: rel_ax_db.

Opaque two.

Theorem two__two_rel_rw (VV : Nats_u): ⌊ two ⌋ = VV ↔ two_rel VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite two__two_rel_rw: f_rel_funct_db.

#[global] Hint Resolve two__two_rel_rw: rel_ax_db.

#[global] Instance two_lookup_rw: dictionary rwLem two := { lookup' := two__two_rel_rw }.

Theorem two__two_rel (VV : Nats_u): ⌊ two ⌋ = VV ↔ two_rel VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite two__two_rel: f_rel_funct_db.

Theorem two__two_rel' (VV : Nats_u): ⌊ two ⌋ = VV ↔ two_rel VV.
Proof.
  intros. refine (two__two_rel VV).
Qed.

#[global] Hint Resolve two__two_rel': f_rel_funct_db.

Definition two_rel_mk : {VV: _ | two_rel VV}.
Proof.
  intros; refine (subsumptionCast _ (λ VV, two_rel VV) two _); rewrite <- two__two_rel'; quicksolve.
Qed.

#[global] Hint Resolve two_rel_mk: f_rel_funct_db.
