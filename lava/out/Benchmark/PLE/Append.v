From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Set Universe Polymorphism. 
From Coq Require Import Unicode.Utf8.

Definition flip_spec
  (f : @Pack
       ({VV: Z | True}
        ::RT λ (lq_tmp0 : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({VV: Z | True}
  ::RT λ (lq_tmp0 : {VV: Z | True}),
       {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_41814097 : ArgList ({VV: Z | True}
                                 ::RT λ (lq_tmp0 : {VV: Z | True}),
                                      {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_41814097 : Z),
        ltac:(flattenP (λ (lq_tmp0 lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_41814097 v_x_41814097)))
  (x : {x: Z | True})
  (y : {y: Z | True}):
  Type :=
  {VV: Z | True}.

#[global] Hint Unfold flip_spec: lia_unfold.

Definition flip
  (f : @Pack
       ({VV: Z | True}
        ::RT λ (lq_tmp0 : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({VV: Z | True}
  ::RT λ (lq_tmp0 : {VV: Z | True}),
       {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_41814097 : ArgList ({VV: Z | True}
                                 ::RT λ (lq_tmp0 : {VV: Z | True}),
                                      {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_41814097 : Z),
        ltac:(flattenP (λ (lq_tmp0 lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_41814097 v_x_41814097)))
  (x : {x: Z | True})
  (y : {y: Z | True}):
  flip_spec f x y.
Proof.
  destruct x as [x x_p]. destruct y as [y y_p]. refine (getPackF f (# y) (# x)).
Defined.

Inductive flip_rel: @uPack (Z ::UT (Z ::UT nilUT)) Z → Z → Z → Z → Prop :=
  | flip_Constr: ∀ (f : @uPack (Z ::UT (Z ::UT nilUT)) Z) x y (f_res : Z),
                 getUPackRel f y x f_res → flip_rel f x y f_res.

#[global] Hint Constructors flip_rel: core_hint_db.

#[global] Instance flip_lookup_rel: dictionary rel flip := { lookup' := flip_rel }.

#[global] Instance flip_getF: getFunc flip_rel := { getF' := flip }.

Theorem flip_rel_funct [f : @uPack (Z ::UT (Z ::UT nilUT)) Z] [x y : Z]:
  ∀ (VV VV' : Z), flip_rel f x y VV → (flip_rel f x y VV' → VV = VV').
Proof.
  rel_functionhood_body.
Qed.

#[global] Hint Resolve flip_rel_funct: f_rel_funct_db.

Theorem flip_inv_lem f x y flip_inv_lem_res:
  flip_rel f x y flip_inv_lem_res
  ↔ ∃ (f_res : Z), getUPackRel f y x f_res ∧ flip_inv_lem_res == f_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite flip_inv_lem: f_rel_back.

Theorem flip_rel_ex
  (f : @Pack
       ({lq_tmp0: Z | True}
        ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}),
             {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({lq_tmp0: Z | True}
  ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}),
       {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_15576161 : ArgList ({lq_tmp0: Z | True}
                                 ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}),
                                      {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_15576161 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {lq_tmp0: Z | True})
   (lq_tmp1 : {lq_tmp1: Z | True})
   (VV : Z),
 True) x_15576161 v_x_15576161)))
  (x : Z)
  (x_p : True)
  (y : Z)
  (y_p : True):
  flip_rel ⌊ f ⌋ x y ⌊ flip f (exist _ x x_p) (exist _ y y_p) -⌋.
Proof.
  Opaque flip.
  existence_lemma_pre flip; fix_notations; simpl in *.
  Transparent flip.
  all: (existence_lemma_quicksolve flip; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve flip_rel_ex: rel_ax_db.

#[global] Opaque flip.

Theorem flip__flip_rel_rw
  (f : @Pack
       ({lq_tmp0: Z | True}
        ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}),
             {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({lq_tmp0: Z | True}
  ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}),
       {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_15576161 : ArgList ({lq_tmp0: Z | True}
                                 ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}),
                                      {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_15576161 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {lq_tmp0: Z | True})
   (lq_tmp1 : {lq_tmp1: Z | True})
   (VV : Z),
 True) x_15576161 v_x_15576161)))
  (x : Z)
  (x_p : True)
  (y : Z)
  (y_p : True)
  (VV : Z):
  ⌊ flip f (exist _ x x_p) (exist _ y y_p) -⌋ = VV ↔ flip_rel ⌊ f ⌋ x y VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite flip__flip_rel_rw: f_rel_funct_db.

#[global] Hint Resolve flip__flip_rel_rw: rel_ax_db.

#[global] Instance flip_lookup_rw: dictionary rwLem flip := { lookup' := flip__flip_rel_rw }.

Theorem flip__flip_rel
  (f : @Pack
       ({VV: Z | True}
        ::RT λ (lq_tmp0 : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({VV: Z | True}
  ::RT λ (lq_tmp0 : {VV: Z | True}),
       {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_41814097 : ArgList ({VV: Z | True}
                                 ::RT λ (lq_tmp0 : {VV: Z | True}),
                                      {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_41814097 : Z),
        ltac:(flattenP (λ (lq_tmp0 lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_41814097 v_x_41814097)))
  (x : {x: Z | True})
  (y : {y: Z | True})
  (VV : Z):
  ⌊ flip f x y -⌋ = VV ↔ flip_rel ⌊ f ⌋ ⌊ x ⌋ ⌊ y ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite flip__flip_rel: f_rel_funct_db.

Theorem flip__flip_rel'
  (f_u : @uPack (Z ::UT (Z ::UT nilUT)) Z)
  (x_u y_u : Z)
  (f : @Pack
       ({VV: Z | True}
        ::RT λ (lq_tmp0 : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({VV: Z | True}
  ::RT λ (lq_tmp0 : {VV: Z | True}),
       {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_41814097 : ArgList ({VV: Z | True}
                                 ::RT λ (lq_tmp0 : {VV: Z | True}),
                                      {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_41814097 : Z),
        ltac:(flattenP (λ (lq_tmp0 lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_41814097 v_x_41814097)))
  (x : {x: Z | True})
  (y : {y: Z | True})
  (VV : Z):
  f_u = ⌊ f ⌋ → (x_u = ⌊ x ⌋ → (y_u = ⌊ y ⌋ → ⌊ flip f x y -⌋ = VV ↔ flip_rel f_u x_u y_u VV)).
Proof.
  intros -> -> ->. refine (flip__flip_rel f x y VV).
Qed.

#[global] Hint Resolve flip__flip_rel': f_rel_funct_db.

Theorem flip_rel_mk
  (f : @Pack
       ({lq_tmp0: Z | True}
        ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}),
             {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({lq_tmp0: Z | True}
  ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}),
       {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_15576161 : ArgList ({lq_tmp0: Z | True}
                                 ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}),
                                      {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_15576161 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {lq_tmp0: Z | True})
   (lq_tmp1 : {lq_tmp1: Z | True})
   (VV : Z),
 True) x_15576161 v_x_15576161)))
  (x : Z)
  (x_p : True)
  (y : Z)
  (y_p : True):
  {VV: _ | flip_rel (packProj f) x y VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, flip_rel (packProj f) x y VV)
          (flip f (exist _ x x_p) (exist _ y y_p))
          _);
  rewrite <- flip__flip_rel';
  quicksolve.
Qed.

#[global] Hint Resolve flip_rel_mk: f_rel_funct_db.

Inductive Pair_u: Type :=
  | MkPair_u: Z → Z → Pair_u.

Fixpoint Pair_eq (x y : Pair_u): bool :=
  match (x, y) with
  | (MkPair_u VV VV_, MkPair_u VV' VV_') => (true && (VV ==? VV')) && (VV_ ==? VV_')
  end.

Theorem Pair_eq_refl : ∀ (x : Pair_u), is_true (Pair_eq x x).
Proof.
  eq_refl_rec.
Qed.

#[global] Hint Resolve Pair_eq_refl: eq_hint_db.

Theorem Pair_eqb_eq : ∀ (s t : Pair_u), is_true (Pair_eq s t) → s = t.
Proof.
  eqb_eq_lem.
Qed.

#[global] Hint Resolve Pair_eqb_eq: eq_hint_db.

#[global] Instance leibnitz_eq_Pair: LeibnitzEqB := {
    equalB' := Pair_eq;
    refl' := Pair_eq_refl;
    eqb_eq' := Pair_eqb_eq }.

Fixpoint Pair_wf (x : Pair_u): Prop :=
  match x with | MkPair_u VV VV_ => True end.

Theorem Pair_wf_ref [p : Pair_u → Prop] (tm : {v: Pair_u | Pair_wf v ∧ p v}): Pair_wf ⌊ tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation Pair := {x: Pair_u | Pair_wf x ∧ True}.

Definition MkPair_lem (VV VV_ : {VV: Z | True}): Pair_wf (MkPair_u ⌊ VV ⌋ ⌊ VV_ ⌋) ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition MkPair (VV VV_ : {VV: Z | True}): Pair :=
  exist _ (MkPair_u ⌊ VV ⌋ ⌊ VV_ ⌋) (MkPair_lem VV VV_).

#[global] Hint Resolve Pair_wf_ref: wf_constr_db.

#[global] Hint Unfold Pair_wf: wf_constr_db.

#[global] Hint Resolve Pair_eq: ref_constr_db.

#[global] Hint Unfold MkPair: ref_constr_db.

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

Definition geqN_spec (ds_d1e7 ds_d1e8 : Nats): Type :=
  Bool.

#[global] Hint Unfold geqN_spec: lia_unfold.

Definition geqN (ds_d1e7 ds_d1e8 : Nats): geqN_spec ds_d1e7 ds_d1e8.
Proof.
  destruct ds_d1e7 as [ds_d1e7 ds_d1e7_p].
  destruct ds_d1e8 as [ds_d1e8 ds_d1e8_p].
  try revert ds_d1e7_p; generalize dependent ds_d1e7;
  induction ds_d1e8 as [lq_anf7205759403792798740 IH_lq_anf7205759403792798740|];
  intros.
  - destruct ds_d1e7 as [m|].
    + refine (IH_lq_anf7205759403792798740
              ltac:(try clear IH_lq_anf7205759403792798740; solver)
              m
              ltac:(try clear IH_lq_anf7205759403792798740; solver)).
    + refine (# false).
  - refine (# true).
Defined.

Inductive geqN_rel: Nats_u → Nats_u → bool → Prop :=
  | geqN_Suc_Suc: ∀ m lq_anf7205759403792798740 (geqN_res : bool),
                  geqN_rel m lq_anf7205759403792798740 geqN_res
                  → geqN_rel (Suc_u m) (Suc_u lq_anf7205759403792798740) geqN_res
  | geqN_Zero_Suc: ∀ lq_anf7205759403792798740,
                   geqN_rel Zero_u (Suc_u lq_anf7205759403792798740) false
  | geqN_x_Zero: ∀ ds_d1e7, geqN_rel ds_d1e7 Zero_u true.

#[global] Hint Constructors geqN_rel: core_hint_db.

#[global] Instance geqN_lookup_rel: dictionary rel geqN := { lookup' := geqN_rel }.

#[global] Instance geqN_getF: getFunc geqN_rel := { getF' := geqN }.

Theorem geqN_rel_funct [ds_d1e7 ds_d1e8 : Nats_u]:
  ∀ (VV VV' : bool), geqN_rel ds_d1e7 ds_d1e8 VV → (geqN_rel ds_d1e7 ds_d1e8 VV' → VV = VV').
Proof.
  try revert ds_d1e7_p; generalize dependent ds_d1e7;
  induction ds_d1e8 as [lq_anf7205759403792798740 IH_lq_anf7205759403792798740|];
  intros;
  [destruct ds_d1e7 as [m|] |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve geqN_rel_funct: f_rel_funct_db.

Theorem geqN_Suc_Suc_lem lq_anf7205759403792798740 m geqN_Suc_Suc_lem_res:
  geqN_rel (Suc_u m) (Suc_u lq_anf7205759403792798740) geqN_Suc_Suc_lem_res
  ↔ ∃ (geqN_res : bool),
    geqN_rel m lq_anf7205759403792798740 geqN_res ∧ geqN_Suc_Suc_lem_res == geqN_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite geqN_Suc_Suc_lem: f_rel_back.

Theorem geqN_Zero_Suc_lem lq_anf7205759403792798740 geqN_Zero_Suc_lem_res:
  geqN_rel Zero_u (Suc_u lq_anf7205759403792798740) geqN_Zero_Suc_lem_res
  ↔ geqN_Zero_Suc_lem_res == false.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite geqN_Zero_Suc_lem: f_rel_back.

Theorem geqN_x_Zero_lem ds_d1e7 geqN_x_Zero_lem_res:
  geqN_rel ds_d1e7 Zero_u geqN_x_Zero_lem_res ↔ geqN_x_Zero_lem_res == true.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite geqN_x_Zero_lem: f_rel_back.

Theorem geqN_rel_ex
  (ds_d1e7 : Nats_u)
  (ds_d1e7_p : Nats_wf ds_d1e7 ∧ True)
  (ds_d1e8 : Nats_u)
  (ds_d1e8_p : Nats_wf ds_d1e8 ∧ True):
  geqN_rel ds_d1e7 ds_d1e8 ⌊ geqN (exist _ ds_d1e7 ds_d1e7_p) (exist _ ds_d1e8 ds_d1e8_p) -⌋.
Proof.
  Opaque geqN.
  existence_lemma_pre geqN;
  try revert ds_d1e7_p; generalize dependent ds_d1e7;
  induction ds_d1e8 as [lq_anf7205759403792798740 IH_lq_anf7205759403792798740|];
  intros;
  [destruct ds_d1e7 as [m|];
   [fix_notations;
    pose proof (IH_lq_anf7205759403792798740
                ltac:(try clear IH_lq_anf7205759403792798740; solver)
                m
                ltac:(try clear IH_lq_anf7205759403792798740; solver)) as IH_16154647;
    try clear IH_lq_anf7205759403792798740 |
    fix_notations] |
   fix_notations];
  simpl in *.
  Transparent geqN.
  all: (existence_lemma_quicksolve geqN; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve geqN_rel_ex: rel_ax_db.

#[global] Opaque geqN.

Theorem geqN__geqN_rel_rw
  (ds_d1e7 : Nats_u)
  (ds_d1e7_p : Nats_wf ds_d1e7 ∧ True)
  (ds_d1e8 : Nats_u)
  (ds_d1e8_p : Nats_wf ds_d1e8 ∧ True)
  (VV : bool):
  ⌊ geqN (exist _ ds_d1e7 ds_d1e7_p) (exist _ ds_d1e8 ds_d1e8_p) -⌋ = VV
  ↔ geqN_rel ds_d1e7 ds_d1e8 VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite geqN__geqN_rel_rw: f_rel_funct_db.

#[global] Hint Resolve geqN__geqN_rel_rw: rel_ax_db.

#[global] Instance geqN_lookup_rw: dictionary rwLem geqN := { lookup' := geqN__geqN_rel_rw }.

Theorem geqN__geqN_rel (ds_d1e7 ds_d1e8 : Nats) (VV : bool):
  ⌊ geqN ds_d1e7 ds_d1e8 -⌋ = VV ↔ geqN_rel ⌊ ds_d1e7 ⌋ ⌊ ds_d1e8 ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite geqN__geqN_rel: f_rel_funct_db.

Theorem geqN__geqN_rel' (ds_d1e7_u ds_d1e8_u : Nats_u) (ds_d1e7 ds_d1e8 : Nats) (VV : bool):
  ds_d1e7_u = ⌊ ds_d1e7 ⌋
  → (ds_d1e8_u = ⌊ ds_d1e8 ⌋ → ⌊ geqN ds_d1e7 ds_d1e8 -⌋ = VV ↔ geqN_rel ds_d1e7_u ds_d1e8_u VV).
Proof.
  intros -> ->. refine (geqN__geqN_rel ds_d1e7 ds_d1e8 VV).
Qed.

#[global] Hint Resolve geqN__geqN_rel': f_rel_funct_db.

Theorem geqN_rel_mk
  (ds_d1e7 : Nats_u)
  (ds_d1e7_p : Nats_wf ds_d1e7 ∧ True)
  (ds_d1e8 : Nats_u)
  (ds_d1e8_p : Nats_wf ds_d1e8 ∧ True):
  {VV: _ | geqN_rel ds_d1e7 ds_d1e8 VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, geqN_rel ds_d1e7 ds_d1e8 VV)
          (geqN (exist _ ds_d1e7 ds_d1e7_p) (exist _ ds_d1e8 ds_d1e8_p))
          _);
  rewrite <- geqN__geqN_rel';
  quicksolve.
Qed.

#[global] Hint Resolve geqN_rel_mk: f_rel_funct_db.

#[global] Instance geqN_pack:
  @Pack
  (Nats ::RT λ (ds_d1e7 : Nats), Nats ::RT λ (ds_d1e8 : Nats), nilRT)
  (Nats_u ::UT (Nats_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((Nats
  ::RT λ (ds_d1e7 : Nats), Nats ::RT λ (ds_d1e8 : Nats), nilRT)) ((Nats_u ::UT (Nats_u ::UT nilUT))))
  bool
  (λ (x_78844109 : ArgList (Nats ::RT λ (ds_d1e7 : Nats), Nats ::RT λ (ds_d1e8 : Nats), nilRT))
     (v_x_78844109 : bool),
   ltac:(flattenP (λ (ds_d1e7 ds_d1e8 : Nats) (VV : bool), True) x_78844109 v_x_78844109)).
Proof.
  buildPackG geqN geqN_rel geqN__geqN_rel geqN_rel_funct.
Defined.

#[global] Instance geqN_upack: @uPack (Nats_u ::UT (Nats_u ::UT nilUT)) bool.
Proof.
  buildUPackG geqN_rel geqN_rel_funct.
Defined.

Inductive L2_u: Type :=
  | App2_u: Pair_u → L2_u → L2_u | Emp2_u: L2_u.

Fixpoint L2_eq (x y : L2_u): bool :=
  match (x, y) with
  | (App2_u VV VV_, App2_u VV' VV_') => (true && (VV ==? VV')) && L2_eq VV_ VV_'
  | (Emp2_u, Emp2_u) => true
  | (_, _) => false
  end.

Theorem L2_eq_refl : ∀ (x : L2_u), is_true (L2_eq x x).
Proof.
  eq_refl_rec.
Qed.

#[global] Hint Resolve L2_eq_refl: eq_hint_db.

Theorem L2_eqb_eq : ∀ (s t : L2_u), is_true (L2_eq s t) → s = t.
Proof.
  eqb_eq_lem.
Qed.

#[global] Hint Resolve L2_eqb_eq: eq_hint_db.

#[global] Instance leibnitz_eq_L2: LeibnitzEqB := {
    equalB' := L2_eq;
    refl' := L2_eq_refl;
    eqb_eq' := L2_eqb_eq }.

Fixpoint L2_wf (x : L2_u): Prop :=
  match x with | App2_u VV VV_ => (Pair_wf VV ∧ True) ∧ (L2_wf VV_ ∧ True) | Emp2_u => True end.

Theorem L2_wf_ref [p : L2_u → Prop] (tm : {v: L2_u | L2_wf v ∧ p v}): L2_wf ⌊ tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation L2 := {x: L2_u | L2_wf x ∧ True}.

Definition App2_lem (VV : Pair) (VV_ : L2): L2_wf (App2_u ⌊ VV ⌋ ⌊ VV_ ⌋) ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition App2 (VV : Pair) (VV_ : L2): L2 :=
  exist _ (App2_u ⌊ VV ⌋ ⌊ VV_ ⌋) (App2_lem VV VV_).

Definition Emp2_lem : L2_wf Emp2_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Emp2 : L2 :=
  exist _ Emp2_u Emp2_lem.

Definition wf_App2_VV [VV : Pair_u] [VV_ : L2_u] (p : L2_wf (App2_u VV VV_)): Pair_wf VV.
Proof.
  quicksolve.
Defined.

#[global] Hint Resolve wf_App2_VV: ref_constr_db.

Definition wf_App2_VV_ [VV : Pair_u] [VV_ : L2_u] (p : L2_wf (App2_u VV VV_)): L2_wf VV_.
Proof.
  quicksolve.
Defined.

#[global] Hint Resolve wf_App2_VV_: ref_constr_db.

#[global] Hint Resolve L2_wf_ref: wf_constr_db.

#[global] Hint Unfold L2_wf: wf_constr_db.

#[global] Hint Resolve L2_eq: ref_constr_db.

#[global] Hint Unfold App2: ref_constr_db.

#[global] Hint Unfold Emp2: ref_constr_db.

Definition length2_spec (ds_d1eN : L2): Type :=
  Nats.

#[global] Hint Unfold length2_spec: lia_unfold.

Definition length2 (ds_d1eN : L2): length2_spec ds_d1eN.
Proof.
  destruct ds_d1eN as [ds_d1eN ds_d1eN_p].
  induction ds_d1eN as [ds_d1eP xs IH_xs|].
  - refine (Suc (IH_xs ltac:(try clear IH_xs; solver))).
  - refine Zero.
Defined.

Inductive length2_rel: L2_u → Nats_u → Prop :=
  | length2_App2: ∀ ds_d1eP xs (length2_res : Nats_u),
                  length2_rel xs length2_res → length2_rel (App2_u ds_d1eP xs) (Suc_u length2_res)
  | length2_Emp2: length2_rel Emp2_u Zero_u.

#[global] Hint Constructors length2_rel: core_hint_db.

#[global] Instance length2_lookup_rel: dictionary rel length2 := { lookup' := length2_rel }.

#[global] Instance length2_getF: getFunc length2_rel := { getF' := length2 }.

Theorem length2_rel_funct [ds_d1eN : L2_u]:
  ∀ (VV VV' : Nats_u), length2_rel ds_d1eN VV → (length2_rel ds_d1eN VV' → VV = VV').
Proof.
  induction ds_d1eN as [ds_d1eP xs IH_xs|]; rel_functionhood_body.
Qed.

#[global] Hint Resolve length2_rel_funct: f_rel_funct_db.

Theorem length2_App2_lem ds_d1eP xs length2_App2_lem_res:
  length2_rel (App2_u ds_d1eP xs) length2_App2_lem_res
  ↔ ∃ (length2_res : Nats_u), length2_rel xs length2_res ∧ length2_App2_lem_res == Suc_u length2_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite length2_App2_lem: f_rel_back.

Theorem length2_Emp2_lem length2_Emp2_lem_res:
  length2_rel Emp2_u length2_Emp2_lem_res ↔ length2_Emp2_lem_res == Zero_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite length2_Emp2_lem: f_rel_back.

Theorem length2_rel_ex (ds_d1eN : L2_u) (ds_d1eN_p : L2_wf ds_d1eN ∧ True):
  length2_rel ds_d1eN ⌊ length2 (exist _ ds_d1eN ds_d1eN_p) -⌋.
Proof.
  Opaque length2.
  existence_lemma_pre length2;
  induction ds_d1eN as [ds_d1eP xs IH_xs|];
  [fix_notations; pose proof (IH_xs ltac:(try clear IH_xs; solver)) as IH_67415571; try clear IH_xs |
   fix_notations];
  simpl in *.
  Transparent length2.
  all: (existence_lemma_quicksolve length2; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve length2_rel_ex: rel_ax_db.

#[global] Opaque length2.

Theorem length2__length2_rel_rw (ds_d1eN : L2_u) (ds_d1eN_p : L2_wf ds_d1eN ∧ True) (VV : Nats_u):
  ⌊ length2 (exist _ ds_d1eN ds_d1eN_p) -⌋ = VV ↔ length2_rel ds_d1eN VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite length2__length2_rel_rw: f_rel_funct_db.

#[global] Hint Resolve length2__length2_rel_rw: rel_ax_db.

#[global] Instance length2_lookup_rw: dictionary rwLem length2 := {
    lookup' := length2__length2_rel_rw }.

Theorem length2__length2_rel (ds_d1eN : L2) (VV : Nats_u):
  ⌊ length2 ds_d1eN -⌋ = VV ↔ length2_rel ⌊ ds_d1eN ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite length2__length2_rel: f_rel_funct_db.

Theorem length2__length2_rel' (ds_d1eN_u : L2_u) (ds_d1eN : L2) (VV : Nats_u):
  ds_d1eN_u = ⌊ ds_d1eN ⌋ → ⌊ length2 ds_d1eN -⌋ = VV ↔ length2_rel ds_d1eN_u VV.
Proof.
  intros ->. refine (length2__length2_rel ds_d1eN VV).
Qed.

#[global] Hint Resolve length2__length2_rel': f_rel_funct_db.

Theorem length2_rel_mk (ds_d1eN : L2_u) (ds_d1eN_p : L2_wf ds_d1eN ∧ True):
  {VV: _ | length2_rel ds_d1eN VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, length2_rel ds_d1eN VV) (length2 (exist _ ds_d1eN ds_d1eN_p)) _);
  rewrite <- length2__length2_rel';
  quicksolve.
Qed.

#[global] Hint Resolve length2_rel_mk: f_rel_funct_db.

#[global] Instance length2_pack:
  @Pack
  (L2 ::RT λ (ds_d1eN : L2), nilRT)
  (L2_u ::UT nilUT)
  ltac:(mkProjectsArgListTG ((L2 ::RT λ (ds_d1eN : L2), nilRT)) ((L2_u ::UT nilUT)))
  Nats_u
  (λ (x_84990795 : ArgList (L2 ::RT λ (ds_d1eN : L2), nilRT)) (v_x_84990795 : Nats_u),
   ltac:(flattenP (λ (ds_d1eN : L2) (VV : Nats_u), Nats_wf VV ∧ True) x_84990795 v_x_84990795)).
Proof.
  buildPackG length2 length2_rel length2__length2_rel length2_rel_funct.
Defined.

#[global] Instance length2_upack: @uPack (L2_u ::UT nilUT) Nats_u.
Proof.
  buildUPackG length2_rel length2_rel_funct.
Defined.

Inductive L_u: Type :=
  | App_u: Z → L_u → L_u | Emp_u: L_u.

Fixpoint L_eq (x y : L_u): bool :=
  match (x, y) with
  | (App_u VV VV_, App_u VV' VV_') => (true && (VV ==? VV')) && L_eq VV_ VV_'
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
  match x with | App_u VV VV_ => L_wf VV_ ∧ True | Emp_u => True end.

Theorem L_wf_ref [p : L_u → Prop] (tm : {v: L_u | L_wf v ∧ p v}): L_wf ⌊ tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation L := {x: L_u | L_wf x ∧ True}.

Definition App_lem (VV : {VV: Z | True}) (VV_ : L): L_wf (App_u ⌊ VV ⌋ ⌊ VV_ ⌋) ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition App (VV : {VV: Z | True}) (VV_ : L): L :=
  exist _ (App_u ⌊ VV ⌋ ⌊ VV_ ⌋) (App_lem VV VV_).

Definition Emp_lem : L_wf Emp_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Emp : L :=
  exist _ Emp_u Emp_lem.

Definition wf_App_VV_ [VV : Z] [VV_ : L_u] (p : L_wf (App_u VV VV_)): L_wf VV_.
Proof.
  quicksolve.
Defined.

#[global] Hint Resolve wf_App_VV_: ref_constr_db.

#[global] Hint Resolve L_wf_ref: wf_constr_db.

#[global] Hint Unfold L_wf: wf_constr_db.

#[global] Hint Resolve L_eq: ref_constr_db.

#[global] Hint Unfold App: ref_constr_db.

#[global] Hint Unfold Emp: ref_constr_db.

Inductive PairL_u: Type :=
  | MkPairL_u: L_u → L_u → PairL_u.

Fixpoint PairL_eq (x y : PairL_u): bool :=
  match (x, y) with
  | (MkPairL_u VV VV_, MkPairL_u VV' VV_') => (true && (VV ==? VV')) && (VV_ ==? VV_')
  end.

Theorem PairL_eq_refl : ∀ (x : PairL_u), is_true (PairL_eq x x).
Proof.
  eq_refl_rec.
Qed.

#[global] Hint Resolve PairL_eq_refl: eq_hint_db.

Theorem PairL_eqb_eq : ∀ (s t : PairL_u), is_true (PairL_eq s t) → s = t.
Proof.
  eqb_eq_lem.
Qed.

#[global] Hint Resolve PairL_eqb_eq: eq_hint_db.

#[global] Instance leibnitz_eq_PairL: LeibnitzEqB := {
    equalB' := PairL_eq;
    refl' := PairL_eq_refl;
    eqb_eq' := PairL_eqb_eq }.

Fixpoint PairL_wf (x : PairL_u): Prop :=
  match x with | MkPairL_u VV VV_ => (L_wf VV ∧ True) ∧ (L_wf VV_ ∧ True) end.

Theorem PairL_wf_ref [p : PairL_u → Prop] (tm : {v: PairL_u | PairL_wf v ∧ p v}): PairL_wf ⌊ tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation PairL := {x: PairL_u | PairL_wf x ∧ True}.

Definition MkPairL_lem (VV VV_ : L): PairL_wf (MkPairL_u ⌊ VV ⌋ ⌊ VV_ ⌋) ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition MkPairL (VV VV_ : L): PairL :=
  exist _ (MkPairL_u ⌊ VV ⌋ ⌊ VV_ ⌋) (MkPairL_lem VV VV_).

Definition wf_MkPairL_VV [VV VV_ : L_u] (p : PairL_wf (MkPairL_u VV VV_)): L_wf VV.
Proof.
  quicksolve.
Defined.

#[global] Hint Resolve wf_MkPairL_VV: ref_constr_db.

Definition wf_MkPairL_VV_ [VV VV_ : L_u] (p : PairL_wf (MkPairL_u VV VV_)): L_wf VV_.
Proof.
  quicksolve.
Defined.

#[global] Hint Resolve wf_MkPairL_VV_: ref_constr_db.

#[global] Hint Resolve PairL_wf_ref: wf_constr_db.

#[global] Hint Unfold PairL_wf: wf_constr_db.

#[global] Hint Resolve PairL_eq: ref_constr_db.

#[global] Hint Unfold MkPairL: ref_constr_db.

Definition unzip_spec (ds_d1eT : L2): Type :=
  PairL.

#[global] Hint Unfold unzip_spec: lia_unfold.

Definition unzip (ds_d1eT : L2): unzip_spec ds_d1eT.
Proof.
  destruct ds_d1eT as [ds_d1eT ds_d1eT_p].
  induction ds_d1eT as [ds_d1f3 l IH_l|].
  - destruct ds_d1f3 as [x y].
    + let E := fresh "E" in destruct ⌊ IH_l ltac:(try clear IH_l; solver) -⌋ as [xs ys] eqn:E;
      [refine (MkPairL
               (App (# x) (exist (λ (VV : L_u), L_wf VV ∧ True) xs ltac:(solver)))
               (App (# y) (exist (λ (VV : L_u), L_wf VV ∧ True) ys ltac:(solver))))].
  - refine (MkPairL Emp Emp).
Defined.

Definition app_inj_spec
  (x : {x: Z | True})
  (y : {y: Z | True})
  (xs ys : L)
  (p : {{App_u ⌊ x ⌋ ⌊ xs ⌋ == App_u ⌊ y ⌋ ⌊ ys ⌋}}):
  Type :=
  {{⌊ x ⌋ == ⌊ y ⌋ ∧ ⌊ xs ⌋ == ⌊ ys ⌋}}.

#[global] Hint Unfold app_inj_spec: lia_unfold.

Theorem app_inj
  (x : {x: Z | True})
  (y : {y: Z | True})
  (xs ys : L)
  (p : {{App_u ⌊ x ⌋ ⌊ xs ⌋ == App_u ⌊ y ⌋ ⌊ ys ⌋}}):
  app_inj_spec x y xs ys p.
Proof.
  destruct x as [x x_p].
  destruct y as [y y_p].
  destruct xs as [xs xs_p].
  destruct ys as [ys ys_p].
  destruct p as [p p_p].
  refine (subsumptionCast Unit (λ (VV : Unit), x == y ∧ xs == ys) (# unit) ltac:(solver)).
Qed.

Definition append_spec (ds_d1fO ys : L): Type :=
  L.

#[global] Hint Unfold append_spec: lia_unfold.

Definition append (ds_d1fO ys : L): append_spec ds_d1fO ys.
Proof.
  destruct ds_d1fO as [ds_d1fO ds_d1fO_p].
  destruct ys as [ys ys_p].
  try revert ys_p; generalize dependent ys; induction ds_d1fO as [x xs IH_xs|]; intros.
  - refine (App (# x) (IH_xs ltac:(try clear IH_xs; solver) ys ltac:(try clear IH_xs; solver))).
  - refine (exist (λ (ys : L_u), L_wf ys ∧ True) ys ltac:(solver)).
Defined.

Inductive append_rel: L_u → L_u → L_u → Prop :=
  | append_App_x: ∀ x xs ys (append_res : L_u),
                  append_rel xs ys append_res → append_rel (App_u x xs) ys (App_u x append_res)
  | append_Emp_x: ∀ ys, append_rel Emp_u ys ys.

#[global] Hint Constructors append_rel: core_hint_db.

#[global] Instance append_lookup_rel: dictionary rel append := { lookup' := append_rel }.

#[global] Instance append_getF: getFunc append_rel := { getF' := append }.

Theorem append_rel_funct [ds_d1fO ys : L_u]:
  ∀ (VV VV' : L_u), append_rel ds_d1fO ys VV → (append_rel ds_d1fO ys VV' → VV = VV').
Proof.
  try revert ys_p; generalize dependent ys; induction ds_d1fO as [x xs IH_xs|]; intros;
  rel_functionhood_body.
Qed.

#[global] Hint Resolve append_rel_funct: f_rel_funct_db.

Theorem append_App_x_lem x xs ys append_App_x_lem_res:
  append_rel (App_u x xs) ys append_App_x_lem_res
  ↔ ∃ (append_res : L_u), append_rel xs ys append_res ∧ append_App_x_lem_res == App_u x append_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite append_App_x_lem: f_rel_back.

Theorem append_Emp_x_lem ys append_Emp_x_lem_res:
  append_rel Emp_u ys append_Emp_x_lem_res ↔ append_Emp_x_lem_res == ys.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite append_Emp_x_lem: f_rel_back.

Theorem append_rel_ex
  (ds_d1fO : L_u) (ds_d1fO_p : L_wf ds_d1fO ∧ True) (ys : L_u) (ys_p : L_wf ys ∧ True):
  append_rel ds_d1fO ys ⌊ append (exist _ ds_d1fO ds_d1fO_p) (exist _ ys ys_p) -⌋.
Proof.
  Opaque append.
  existence_lemma_pre append;
  try revert ys_p; generalize dependent ys; induction ds_d1fO as [x xs IH_xs|]; intros;
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
  (ds_d1fO : L_u) (ds_d1fO_p : L_wf ds_d1fO ∧ True) (ys : L_u) (ys_p : L_wf ys ∧ True) (VV : L_u):
  ⌊ append (exist _ ds_d1fO ds_d1fO_p) (exist _ ys ys_p) -⌋ = VV ↔ append_rel ds_d1fO ys VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite append__append_rel_rw: f_rel_funct_db.

#[global] Hint Resolve append__append_rel_rw: rel_ax_db.

#[global] Instance append_lookup_rw: dictionary rwLem append := {
    lookup' := append__append_rel_rw }.

Theorem append__append_rel (ds_d1fO ys : L) (VV : L_u):
  ⌊ append ds_d1fO ys -⌋ = VV ↔ append_rel ⌊ ds_d1fO ⌋ ⌊ ys ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite append__append_rel: f_rel_funct_db.

Theorem append__append_rel' (ds_d1fO_u ys_u : L_u) (ds_d1fO ys : L) (VV : L_u):
  ds_d1fO_u = ⌊ ds_d1fO ⌋
  → (ys_u = ⌊ ys ⌋ → ⌊ append ds_d1fO ys -⌋ = VV ↔ append_rel ds_d1fO_u ys_u VV).
Proof.
  intros -> ->. refine (append__append_rel ds_d1fO ys VV).
Qed.

#[global] Hint Resolve append__append_rel': f_rel_funct_db.

Theorem append_rel_mk
  (ds_d1fO : L_u) (ds_d1fO_p : L_wf ds_d1fO ∧ True) (ys : L_u) (ys_p : L_wf ys ∧ True):
  {VV: _ | append_rel ds_d1fO ys VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, append_rel ds_d1fO ys VV)
          (append (exist _ ds_d1fO ds_d1fO_p) (exist _ ys ys_p))
          _);
  rewrite <- append__append_rel';
  quicksolve.
Qed.

#[global] Hint Resolve append_rel_mk: f_rel_funct_db.

#[global] Instance append_pack:
  @Pack
  (L ::RT λ (ds_d1fO : L), L ::RT λ (ys : L), nilRT)
  (L_u ::UT (L_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((L ::RT λ (ds_d1fO : L), L ::RT λ (ys : L), nilRT)) ((L_u ::UT (L_u ::UT nilUT))))
  L_u
  (λ (x_86572260 : ArgList (L ::RT λ (ds_d1fO : L), L ::RT λ (ys : L), nilRT)) (v_x_86572260 : L_u),
   ltac:(flattenP (λ (ds_d1fO ys : L) (VV : L_u), L_wf VV ∧ True) x_86572260 v_x_86572260)).
Proof.
  buildPackG append append_rel append__append_rel append_rel_funct.
Defined.

#[global] Instance append_upack: @uPack (L_u ::UT (L_u ::UT nilUT)) L_u.
Proof.
  buildUPackG append_rel append_rel_funct.
Defined.

Definition append_nonempty_xs_spec
  (ds_d1fx ds_d1fy : L)
  (ds_d1fz : {{∃ (append_res : L_u),
               append_rel ⌊ ds_d1fx ⌋ ⌊ ds_d1fy ⌋ append_res ∧ append_res == Emp_u}}):
  Type :=
  {{⌊ ds_d1fx ⌋ == Emp_u}}.

#[global] Hint Unfold append_nonempty_xs_spec: lia_unfold.

Theorem append_nonempty_xs
  (ds_d1fx ds_d1fy : L)
  (ds_d1fz : {{∃ (append_res : L_u),
               append_rel ⌊ ds_d1fx ⌋ ⌊ ds_d1fy ⌋ append_res ∧ append_res == Emp_u}}):
  append_nonempty_xs_spec ds_d1fx ds_d1fy ds_d1fz.
Proof.
  destruct ds_d1fx as [ds_d1fx ds_d1fx_p].
  destruct ds_d1fy as [ds_d1fy ds_d1fy_p].
  destruct ds_d1fz as [ds_d1fz ds_d1fz_p].
  destruct ds_d1fx as [lq_anf7205759403792798590 lq_anf7205759403792798591|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), App_u lq_anf7205759403792798590 lq_anf7205759403792798591 == Emp_u)
            (exist (λ (ds_d1fz : Unit),
                    ∃ (append_res : L_u),
                    append_rel (App_u lq_anf7205759403792798590 lq_anf7205759403792798591) ds_d1fy append_res
                    ∧ append_res == Emp_u) ds_d1fz ltac:(solver))
            ltac:(solver)).
  - destruct ds_d1fy as [lq_anf7205759403792798588 lq_anf7205759403792798589|].
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit), Emp_u == Emp_u)
              (exist (λ (ds_d1fz : Unit),
                      ∃ (append_res : L_u),
                      append_rel Emp_u (App_u lq_anf7205759403792798588 lq_anf7205759403792798589) append_res
                      ∧ append_res == Emp_u) ds_d1fz ltac:(solver))
              ltac:(solver)).
    + refine (subsumptionCast Unit (λ (VV : Unit), Emp_u == Emp_u) (# unit) ltac:(solver)).
Qed.

Definition append_nonempty_ys_spec
  (ds_d1fE ds_d1fF : L)
  (ds_d1fG : {{∃ (append_res : L_u),
               append_rel ⌊ ds_d1fE ⌋ ⌊ ds_d1fF ⌋ append_res ∧ append_res == Emp_u}}):
  Type :=
  {{⌊ ds_d1fF ⌋ == Emp_u}}.

#[global] Hint Unfold append_nonempty_ys_spec: lia_unfold.

Theorem append_nonempty_ys
  (ds_d1fE ds_d1fF : L)
  (ds_d1fG : {{∃ (append_res : L_u),
               append_rel ⌊ ds_d1fE ⌋ ⌊ ds_d1fF ⌋ append_res ∧ append_res == Emp_u}}):
  append_nonempty_ys_spec ds_d1fE ds_d1fF ds_d1fG.
Proof.
  destruct ds_d1fE as [ds_d1fE ds_d1fE_p].
  destruct ds_d1fF as [ds_d1fF ds_d1fF_p].
  destruct ds_d1fG as [ds_d1fG ds_d1fG_p].
  destruct ds_d1fE as [lq_anf7205759403792798581 lq_anf7205759403792798582|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ds_d1fF == Emp_u)
            (exist (λ (ds_d1fG : Unit),
                    ∃ (append_res : L_u),
                    append_rel (App_u lq_anf7205759403792798581 lq_anf7205759403792798582) ds_d1fF append_res
                    ∧ append_res == Emp_u) ds_d1fG ltac:(solver))
            ltac:(solver)).
  - destruct ds_d1fF as [lq_anf7205759403792798579 lq_anf7205759403792798580|].
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit), App_u lq_anf7205759403792798579 lq_anf7205759403792798580 == Emp_u)
              (exist (λ (ds_d1fG : Unit),
                      ∃ (append_res : L_u),
                      append_rel Emp_u (App_u lq_anf7205759403792798579 lq_anf7205759403792798580) append_res
                      ∧ append_res == Emp_u) ds_d1fG ltac:(solver))
              ltac:(solver)).
    + refine (subsumptionCast Unit (λ (VV : Unit), Emp_u == Emp_u) (# unit) ltac:(solver)).
Qed.

Definition concatMap_spec
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       L_u
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : L_u),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : L_u), L_wf VV ∧ True) x_40877513 v_x_40877513)))
  (ds_d1fR : L):
  Type :=
  L.

#[global] Hint Unfold concatMap_spec: lia_unfold.

Definition concatMap
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       L_u
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : L_u),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : L_u), L_wf VV ∧ True) x_40877513 v_x_40877513)))
  (ds_d1fR : L):
  concatMap_spec f ds_d1fR.
Proof.
  destruct ds_d1fR as [ds_d1fR ds_d1fR_p].
  try revert f_p; generalize dependent f; induction ds_d1fR as [x xs IH_xs|]; intros.
  - refine (append (getPackF f (# x)) (IH_xs ltac:(try clear IH_xs; solver) f)).
  - refine Emp.
Defined.

Inductive concatMap_rel: @uPack (Z ::UT nilUT) L_u → L_u → L_u → Prop :=
  | concatMap_x_App: ∀ (f : @uPack (Z ::UT nilUT) L_u) x xs (concatMap_res : L_u),
                     concatMap_rel f xs concatMap_res
                     → ∀ (f_res : L_u),
                       getUPackRel f x f_res
                       → ∀ (append_res : L_u),
                         append_rel f_res concatMap_res append_res → concatMap_rel f (App_u x xs) append_res
  | concatMap_x_Emp: ∀ (f : @uPack (Z ::UT nilUT) L_u), concatMap_rel f Emp_u Emp_u.

#[global] Hint Constructors concatMap_rel: core_hint_db.

#[global] Instance concatMap_lookup_rel: dictionary rel concatMap := { lookup' := concatMap_rel }.

#[global] Instance concatMap_getF: getFunc concatMap_rel := { getF' := concatMap }.

Theorem concatMap_rel_funct [f : @uPack (Z ::UT nilUT) L_u] [ds_d1fR : L_u]:
  ∀ (VV VV' : L_u), concatMap_rel f ds_d1fR VV → (concatMap_rel f ds_d1fR VV' → VV = VV').
Proof.
  try revert f_p; generalize dependent f; induction ds_d1fR as [x xs IH_xs|]; intros;
  rel_functionhood_body.
Qed.

#[global] Hint Resolve concatMap_rel_funct: f_rel_funct_db.

Theorem concatMap_x_App_lem f x xs concatMap_x_App_lem_res:
  concatMap_rel f (App_u x xs) concatMap_x_App_lem_res
  ↔ ∃ (concatMap_res : L_u),
    concatMap_rel f xs concatMap_res
    ∧ ∃ (f_res : L_u),
      getUPackRel f x f_res
      ∧ ∃ (append_res : L_u),
        append_rel f_res concatMap_res append_res ∧ concatMap_x_App_lem_res == append_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite concatMap_x_App_lem: f_rel_back.

Theorem concatMap_x_Emp_lem f concatMap_x_Emp_lem_res:
  concatMap_rel f Emp_u concatMap_x_Emp_lem_res ↔ concatMap_x_Emp_lem_res == Emp_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite concatMap_x_Emp_lem: f_rel_back.

Theorem concatMap_rel_ex
  (f : @Pack
       ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp1: Z | True}
  ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT nilUT)))
       L_u
       (λ (x_86795196 : ArgList ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_86795196 : L_u),
        ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : L_u), L_wf VV ∧ True) x_86795196 v_x_86795196)))
  (ds_d1fR : L_u)
  (ds_d1fR_p : L_wf ds_d1fR ∧ True):
  concatMap_rel ⌊ f ⌋ ds_d1fR ⌊ concatMap f (exist _ ds_d1fR ds_d1fR_p) -⌋.
Proof.
  Opaque concatMap.
  existence_lemma_pre concatMap;
  try revert f_p; generalize dependent f; induction ds_d1fR as [x xs IH_xs|]; intros;
  [fix_notations;
   pose proof (IH_xs ltac:(try clear IH_xs; solver) f) as IH_29745491;
   try clear IH_xs |
   fix_notations];
  simpl in *.
  Transparent concatMap.
  all: (existence_lemma_quicksolve concatMap; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve concatMap_rel_ex: rel_ax_db.

#[global] Opaque concatMap.

Theorem concatMap__concatMap_rel_rw
  (f : @Pack
       ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp1: Z | True}
  ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT nilUT)))
       L_u
       (λ (x_86795196 : ArgList ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_86795196 : L_u),
        ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : L_u), L_wf VV ∧ True) x_86795196 v_x_86795196)))
  (ds_d1fR : L_u)
  (ds_d1fR_p : L_wf ds_d1fR ∧ True)
  (VV : L_u):
  ⌊ concatMap f (exist _ ds_d1fR ds_d1fR_p) -⌋ = VV ↔ concatMap_rel ⌊ f ⌋ ds_d1fR VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite concatMap__concatMap_rel_rw: f_rel_funct_db.

#[global] Hint Resolve concatMap__concatMap_rel_rw: rel_ax_db.

#[global] Instance concatMap_lookup_rw: dictionary rwLem concatMap := {
    lookup' := concatMap__concatMap_rel_rw }.

Theorem concatMap__concatMap_rel
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       L_u
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : L_u),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : L_u), L_wf VV ∧ True) x_40877513 v_x_40877513)))
  (ds_d1fR : L)
  (VV : L_u):
  ⌊ concatMap f ds_d1fR -⌋ = VV ↔ concatMap_rel ⌊ f ⌋ ⌊ ds_d1fR ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite concatMap__concatMap_rel: f_rel_funct_db.

Theorem concatMap__concatMap_rel'
  (f_u : @uPack (Z ::UT nilUT) L_u)
  (ds_d1fR_u : L_u)
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       L_u
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : L_u),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : L_u), L_wf VV ∧ True) x_40877513 v_x_40877513)))
  (ds_d1fR : L)
  (VV : L_u):
  f_u = ⌊ f ⌋
  → (ds_d1fR_u = ⌊ ds_d1fR ⌋ → ⌊ concatMap f ds_d1fR -⌋ = VV ↔ concatMap_rel f_u ds_d1fR_u VV).
Proof.
  intros -> ->. refine (concatMap__concatMap_rel f ds_d1fR VV).
Qed.

#[global] Hint Resolve concatMap__concatMap_rel': f_rel_funct_db.

Theorem concatMap_rel_mk
  (f : @Pack
       ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp1: Z | True}
  ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT nilUT)))
       L_u
       (λ (x_86795196 : ArgList ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_86795196 : L_u),
        ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : L_u), L_wf VV ∧ True) x_86795196 v_x_86795196)))
  (ds_d1fR : L_u)
  (ds_d1fR_p : L_wf ds_d1fR ∧ True):
  {VV: _ | concatMap_rel (packProj f) ds_d1fR VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, concatMap_rel (packProj f) ds_d1fR VV)
          (concatMap f (exist _ ds_d1fR ds_d1fR_p))
          _);
  rewrite <- concatMap__concatMap_rel';
  quicksolve.
Qed.

#[global] Hint Resolve concatMap_rel_mk: f_rel_funct_db.

Definition l2_pr1_spec (ds_d1ex : L2): Type :=
  L.

#[global] Hint Unfold l2_pr1_spec: lia_unfold.

Definition l2_pr1 (ds_d1ex : L2): l2_pr1_spec ds_d1ex.
Proof.
  destruct ds_d1ex as [ds_d1ex ds_d1ex_p].
  induction ds_d1ex as [ds_d1eA l IH_l|].
  - destruct ds_d1eA as [x ds_d1eB].
    + refine (App (# x) (IH_l ltac:(try clear IH_l; solver))).
  - refine Emp.
Defined.

Inductive l2_pr1_rel: L2_u → L_u → Prop :=
  | l2_pr1__App2_MkPair_x: ∀ ds_d1eB l x (l2_pr1_res : L_u),
                           l2_pr1_rel l l2_pr1_res → l2_pr1_rel (App2_u (MkPair_u x ds_d1eB) l) (App_u x l2_pr1_res)
  | l2_pr1_Emp2: l2_pr1_rel Emp2_u Emp_u.

#[global] Hint Constructors l2_pr1_rel: core_hint_db.

#[global] Instance l2_pr1_lookup_rel: dictionary rel l2_pr1 := { lookup' := l2_pr1_rel }.

#[global] Instance l2_pr1_getF: getFunc l2_pr1_rel := { getF' := l2_pr1 }.

Theorem l2_pr1_rel_funct [ds_d1ex : L2_u]:
  ∀ (VV VV' : L_u), l2_pr1_rel ds_d1ex VV → (l2_pr1_rel ds_d1ex VV' → VV = VV').
Proof.
  induction ds_d1ex as [ds_d1eA l IH_l|];
  [destruct ds_d1eA as [x ds_d1eB] |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve l2_pr1_rel_funct: f_rel_funct_db.

Theorem l2_pr1__App2_MkPair_x_lem ds_d1eB l x l2_pr1__App2_MkPair_x_lem_res:
  l2_pr1_rel (App2_u (MkPair_u x ds_d1eB) l) l2_pr1__App2_MkPair_x_lem_res
  ↔ ∃ (l2_pr1_res : L_u),
    l2_pr1_rel l l2_pr1_res ∧ l2_pr1__App2_MkPair_x_lem_res == App_u x l2_pr1_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite l2_pr1__App2_MkPair_x_lem: f_rel_back.

Theorem l2_pr1_Emp2_lem l2_pr1_Emp2_lem_res:
  l2_pr1_rel Emp2_u l2_pr1_Emp2_lem_res ↔ l2_pr1_Emp2_lem_res == Emp_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite l2_pr1_Emp2_lem: f_rel_back.

Theorem l2_pr1_rel_ex (ds_d1ex : L2_u) (ds_d1ex_p : L2_wf ds_d1ex ∧ True):
  l2_pr1_rel ds_d1ex ⌊ l2_pr1 (exist _ ds_d1ex ds_d1ex_p) -⌋.
Proof.
  Opaque l2_pr1.
  existence_lemma_pre l2_pr1;
  induction ds_d1ex as [ds_d1eA l IH_l|];
  [destruct ds_d1eA as [x ds_d1eB];
   [fix_notations; pose proof (IH_l ltac:(try clear IH_l; solver)) as IH_26190279; try clear IH_l] |
   fix_notations];
  simpl in *.
  Transparent l2_pr1.
  all: (existence_lemma_quicksolve l2_pr1; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve l2_pr1_rel_ex: rel_ax_db.

#[global] Opaque l2_pr1.

Theorem l2_pr1__l2_pr1_rel_rw (ds_d1ex : L2_u) (ds_d1ex_p : L2_wf ds_d1ex ∧ True) (VV : L_u):
  ⌊ l2_pr1 (exist _ ds_d1ex ds_d1ex_p) -⌋ = VV ↔ l2_pr1_rel ds_d1ex VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite l2_pr1__l2_pr1_rel_rw: f_rel_funct_db.

#[global] Hint Resolve l2_pr1__l2_pr1_rel_rw: rel_ax_db.

#[global] Instance l2_pr1_lookup_rw: dictionary rwLem l2_pr1 := {
    lookup' := l2_pr1__l2_pr1_rel_rw }.

Theorem l2_pr1__l2_pr1_rel (ds_d1ex : L2) (VV : L_u):
  ⌊ l2_pr1 ds_d1ex -⌋ = VV ↔ l2_pr1_rel ⌊ ds_d1ex ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite l2_pr1__l2_pr1_rel: f_rel_funct_db.

Theorem l2_pr1__l2_pr1_rel' (ds_d1ex_u : L2_u) (ds_d1ex : L2) (VV : L_u):
  ds_d1ex_u = ⌊ ds_d1ex ⌋ → ⌊ l2_pr1 ds_d1ex -⌋ = VV ↔ l2_pr1_rel ds_d1ex_u VV.
Proof.
  intros ->. refine (l2_pr1__l2_pr1_rel ds_d1ex VV).
Qed.

#[global] Hint Resolve l2_pr1__l2_pr1_rel': f_rel_funct_db.

Theorem l2_pr1_rel_mk (ds_d1ex : L2_u) (ds_d1ex_p : L2_wf ds_d1ex ∧ True):
  {VV: _ | l2_pr1_rel ds_d1ex VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, l2_pr1_rel ds_d1ex VV) (l2_pr1 (exist _ ds_d1ex ds_d1ex_p)) _);
  rewrite <- l2_pr1__l2_pr1_rel';
  quicksolve.
Qed.

#[global] Hint Resolve l2_pr1_rel_mk: f_rel_funct_db.

#[global] Instance l2_pr1_pack:
  @Pack
  (L2 ::RT λ (ds_d1ex : L2), nilRT)
  (L2_u ::UT nilUT)
  ltac:(mkProjectsArgListTG ((L2 ::RT λ (ds_d1ex : L2), nilRT)) ((L2_u ::UT nilUT)))
  L_u
  (λ (x_20289022 : ArgList (L2 ::RT λ (ds_d1ex : L2), nilRT)) (v_x_20289022 : L_u),
   ltac:(flattenP (λ (ds_d1ex : L2) (VV : L_u), L_wf VV ∧ True) x_20289022 v_x_20289022)).
Proof.
  buildPackG l2_pr1 l2_pr1_rel l2_pr1__l2_pr1_rel l2_pr1_rel_funct.
Defined.

#[global] Instance l2_pr1_upack: @uPack (L2_u ::UT nilUT) L_u.
Proof.
  buildUPackG l2_pr1_rel l2_pr1_rel_funct.
Defined.

Definition l2_pr2_spec (ds_d1es : L2): Type :=
  L.

#[global] Hint Unfold l2_pr2_spec: lia_unfold.

Definition l2_pr2 (ds_d1es : L2): l2_pr2_spec ds_d1es.
Proof.
  destruct ds_d1es as [ds_d1es ds_d1es_p].
  induction ds_d1es as [ds_d1ev l IH_l|].
  - destruct ds_d1ev as [ds_d1ew y].
    + refine (App (# y) (IH_l ltac:(try clear IH_l; solver))).
  - refine Emp.
Defined.

Inductive l2_pr2_rel: L2_u → L_u → Prop :=
  | l2_pr2__App2_MkPair_x: ∀ ds_d1ew l y (l2_pr2_res : L_u),
                           l2_pr2_rel l l2_pr2_res → l2_pr2_rel (App2_u (MkPair_u ds_d1ew y) l) (App_u y l2_pr2_res)
  | l2_pr2_Emp2: l2_pr2_rel Emp2_u Emp_u.

#[global] Hint Constructors l2_pr2_rel: core_hint_db.

#[global] Instance l2_pr2_lookup_rel: dictionary rel l2_pr2 := { lookup' := l2_pr2_rel }.

#[global] Instance l2_pr2_getF: getFunc l2_pr2_rel := { getF' := l2_pr2 }.

Theorem l2_pr2_rel_funct [ds_d1es : L2_u]:
  ∀ (VV VV' : L_u), l2_pr2_rel ds_d1es VV → (l2_pr2_rel ds_d1es VV' → VV = VV').
Proof.
  induction ds_d1es as [ds_d1ev l IH_l|];
  [destruct ds_d1ev as [ds_d1ew y] |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve l2_pr2_rel_funct: f_rel_funct_db.

Theorem l2_pr2__App2_MkPair_x_lem ds_d1ew l y l2_pr2__App2_MkPair_x_lem_res:
  l2_pr2_rel (App2_u (MkPair_u ds_d1ew y) l) l2_pr2__App2_MkPair_x_lem_res
  ↔ ∃ (l2_pr2_res : L_u),
    l2_pr2_rel l l2_pr2_res ∧ l2_pr2__App2_MkPair_x_lem_res == App_u y l2_pr2_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite l2_pr2__App2_MkPair_x_lem: f_rel_back.

Theorem l2_pr2_Emp2_lem l2_pr2_Emp2_lem_res:
  l2_pr2_rel Emp2_u l2_pr2_Emp2_lem_res ↔ l2_pr2_Emp2_lem_res == Emp_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite l2_pr2_Emp2_lem: f_rel_back.

Theorem l2_pr2_rel_ex (ds_d1es : L2_u) (ds_d1es_p : L2_wf ds_d1es ∧ True):
  l2_pr2_rel ds_d1es ⌊ l2_pr2 (exist _ ds_d1es ds_d1es_p) -⌋.
Proof.
  Opaque l2_pr2.
  existence_lemma_pre l2_pr2;
  induction ds_d1es as [ds_d1ev l IH_l|];
  [destruct ds_d1ev as [ds_d1ew y];
   [fix_notations; pose proof (IH_l ltac:(try clear IH_l; solver)) as IH_26190279; try clear IH_l] |
   fix_notations];
  simpl in *.
  Transparent l2_pr2.
  all: (existence_lemma_quicksolve l2_pr2; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve l2_pr2_rel_ex: rel_ax_db.

#[global] Opaque l2_pr2.

Theorem l2_pr2__l2_pr2_rel_rw (ds_d1es : L2_u) (ds_d1es_p : L2_wf ds_d1es ∧ True) (VV : L_u):
  ⌊ l2_pr2 (exist _ ds_d1es ds_d1es_p) -⌋ = VV ↔ l2_pr2_rel ds_d1es VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite l2_pr2__l2_pr2_rel_rw: f_rel_funct_db.

#[global] Hint Resolve l2_pr2__l2_pr2_rel_rw: rel_ax_db.

#[global] Instance l2_pr2_lookup_rw: dictionary rwLem l2_pr2 := {
    lookup' := l2_pr2__l2_pr2_rel_rw }.

Theorem l2_pr2__l2_pr2_rel (ds_d1es : L2) (VV : L_u):
  ⌊ l2_pr2 ds_d1es -⌋ = VV ↔ l2_pr2_rel ⌊ ds_d1es ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite l2_pr2__l2_pr2_rel: f_rel_funct_db.

Theorem l2_pr2__l2_pr2_rel' (ds_d1es_u : L2_u) (ds_d1es : L2) (VV : L_u):
  ds_d1es_u = ⌊ ds_d1es ⌋ → ⌊ l2_pr2 ds_d1es -⌋ = VV ↔ l2_pr2_rel ds_d1es_u VV.
Proof.
  intros ->. refine (l2_pr2__l2_pr2_rel ds_d1es VV).
Qed.

#[global] Hint Resolve l2_pr2__l2_pr2_rel': f_rel_funct_db.

Theorem l2_pr2_rel_mk (ds_d1es : L2_u) (ds_d1es_p : L2_wf ds_d1es ∧ True):
  {VV: _ | l2_pr2_rel ds_d1es VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, l2_pr2_rel ds_d1es VV) (l2_pr2 (exist _ ds_d1es ds_d1es_p)) _);
  rewrite <- l2_pr2__l2_pr2_rel';
  quicksolve.
Qed.

#[global] Hint Resolve l2_pr2_rel_mk: f_rel_funct_db.

#[global] Instance l2_pr2_pack:
  @Pack
  (L2 ::RT λ (ds_d1es : L2), nilRT)
  (L2_u ::UT nilUT)
  ltac:(mkProjectsArgListTG ((L2 ::RT λ (ds_d1es : L2), nilRT)) ((L2_u ::UT nilUT)))
  L_u
  (λ (x_14674240 : ArgList (L2 ::RT λ (ds_d1es : L2), nilRT)) (v_x_14674240 : L_u),
   ltac:(flattenP (λ (ds_d1es : L2) (VV : L_u), L_wf VV ∧ True) x_14674240 v_x_14674240)).
Proof.
  buildPackG l2_pr2 l2_pr2_rel l2_pr2__l2_pr2_rel l2_pr2_rel_funct.
Defined.

#[global] Instance l2_pr2_upack: @uPack (L2_u ::UT nilUT) L_u.
Proof.
  buildUPackG l2_pr2_rel l2_pr2_rel_funct.
Defined.

Definition length_spec (ds_d1eQ : L): Type :=
  Nats.

#[global] Hint Unfold length_spec: lia_unfold.

Definition length (ds_d1eQ : L): length_spec ds_d1eQ.
Proof.
  destruct ds_d1eQ as [ds_d1eQ ds_d1eQ_p].
  induction ds_d1eQ as [ds_d1eS xs IH_xs|].
  - refine (Suc (IH_xs ltac:(try clear IH_xs; solver))).
  - refine Zero.
Defined.

Inductive length_rel: L_u → Nats_u → Prop :=
  | length_App: ∀ ds_d1eS xs (length_res : Nats_u),
                length_rel xs length_res → length_rel (App_u ds_d1eS xs) (Suc_u length_res)
  | length_Emp: length_rel Emp_u Zero_u.

#[global] Hint Constructors length_rel: core_hint_db.

#[global] Instance length_lookup_rel: dictionary rel length := { lookup' := length_rel }.

#[global] Instance length_getF: getFunc length_rel := { getF' := length }.

Theorem length_rel_funct [ds_d1eQ : L_u]:
  ∀ (VV VV' : Nats_u), length_rel ds_d1eQ VV → (length_rel ds_d1eQ VV' → VV = VV').
Proof.
  induction ds_d1eQ as [ds_d1eS xs IH_xs|]; rel_functionhood_body.
Qed.

#[global] Hint Resolve length_rel_funct: f_rel_funct_db.

Theorem length_App_lem ds_d1eS xs length_App_lem_res:
  length_rel (App_u ds_d1eS xs) length_App_lem_res
  ↔ ∃ (length_res : Nats_u), length_rel xs length_res ∧ length_App_lem_res == Suc_u length_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite length_App_lem: f_rel_back.

Theorem length_Emp_lem length_Emp_lem_res:
  length_rel Emp_u length_Emp_lem_res ↔ length_Emp_lem_res == Zero_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite length_Emp_lem: f_rel_back.

Theorem length_rel_ex (ds_d1eQ : L_u) (ds_d1eQ_p : L_wf ds_d1eQ ∧ True):
  length_rel ds_d1eQ ⌊ length (exist _ ds_d1eQ ds_d1eQ_p) -⌋.
Proof.
  Opaque length.
  existence_lemma_pre length;
  induction ds_d1eQ as [ds_d1eS xs IH_xs|];
  [fix_notations; pose proof (IH_xs ltac:(try clear IH_xs; solver)) as IH_67415571; try clear IH_xs |
   fix_notations];
  simpl in *.
  Transparent length.
  all: (existence_lemma_quicksolve length; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve length_rel_ex: rel_ax_db.

#[global] Opaque length.

Theorem length__length_rel_rw (ds_d1eQ : L_u) (ds_d1eQ_p : L_wf ds_d1eQ ∧ True) (VV : Nats_u):
  ⌊ length (exist _ ds_d1eQ ds_d1eQ_p) -⌋ = VV ↔ length_rel ds_d1eQ VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite length__length_rel_rw: f_rel_funct_db.

#[global] Hint Resolve length__length_rel_rw: rel_ax_db.

#[global] Instance length_lookup_rw: dictionary rwLem length := {
    lookup' := length__length_rel_rw }.

Theorem length__length_rel (ds_d1eQ : L) (VV : Nats_u):
  ⌊ length ds_d1eQ -⌋ = VV ↔ length_rel ⌊ ds_d1eQ ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite length__length_rel: f_rel_funct_db.

Theorem length__length_rel' (ds_d1eQ_u : L_u) (ds_d1eQ : L) (VV : Nats_u):
  ds_d1eQ_u = ⌊ ds_d1eQ ⌋ → ⌊ length ds_d1eQ -⌋ = VV ↔ length_rel ds_d1eQ_u VV.
Proof.
  intros ->. refine (length__length_rel ds_d1eQ VV).
Qed.

#[global] Hint Resolve length__length_rel': f_rel_funct_db.

Theorem length_rel_mk (ds_d1eQ : L_u) (ds_d1eQ_p : L_wf ds_d1eQ ∧ True):
  {VV: _ | length_rel ds_d1eQ VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, length_rel ds_d1eQ VV) (length (exist _ ds_d1eQ ds_d1eQ_p)) _);
  rewrite <- length__length_rel';
  quicksolve.
Qed.

#[global] Hint Resolve length_rel_mk: f_rel_funct_db.

#[global] Instance length_pack:
  @Pack
  (L ::RT λ (ds_d1eQ : L), nilRT)
  (L_u ::UT nilUT)
  ltac:(mkProjectsArgListTG ((L ::RT λ (ds_d1eQ : L), nilRT)) ((L_u ::UT nilUT)))
  Nats_u
  (λ (x_62200818 : ArgList (L ::RT λ (ds_d1eQ : L), nilRT)) (v_x_62200818 : Nats_u),
   ltac:(flattenP (λ (ds_d1eQ : L) (VV : Nats_u), Nats_wf VV ∧ True) x_62200818 v_x_62200818)).
Proof.
  buildPackG length length_rel length__length_rel length_rel_funct.
Defined.

#[global] Instance length_upack: @uPack (L_u ::UT nilUT) Nats_u.
Proof.
  buildUPackG length_rel length_rel_funct.
Defined.

Definition length_unzip_1_spec (ds_d1eq : L2): Type :=
  {{∃ (length2_res : Nats_u),
    length2_rel ⌊ ds_d1eq ⌋ length2_res
    ∧ ∃ (l2_pr1_res : L_u),
      l2_pr1_rel ⌊ ds_d1eq ⌋ l2_pr1_res
      ∧ ∃ (length_res : Nats_u), length_rel l2_pr1_res length_res ∧ length2_res == length_res}}.

#[global] Hint Unfold length_unzip_1_spec: lia_unfold.

Theorem length_unzip_1 (ds_d1eq : L2): length_unzip_1_spec ds_d1eq.
Proof.
  destruct ds_d1eq as [ds_d1eq ds_d1eq_p].
  induction ds_d1eq as [ds_d1er l IH_l|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (length2_res : Nats_u),
             length2_rel (App2_u ds_d1er l) length2_res
             ∧ ∃ (l2_pr1_res : L_u),
               l2_pr1_rel (App2_u ds_d1er l) l2_pr1_res
               ∧ ∃ (length_res : Nats_u), length_rel l2_pr1_res length_res ∧ length2_res == length_res)
            (IH_l ltac:(try clear IH_l; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (length2_res : Nats_u),
             length2_rel Emp2_u length2_res
             ∧ ∃ (l2_pr1_res : L_u),
               l2_pr1_rel Emp2_u l2_pr1_res
               ∧ ∃ (length_res : Nats_u), length_rel l2_pr1_res length_res ∧ length2_res == length_res)
            (# unit)
            ltac:(solver)).
Qed.

Definition length_unzip_2_spec (ds_d1eo : L2): Type :=
  {{∃ (length2_res : Nats_u),
    length2_rel ⌊ ds_d1eo ⌋ length2_res
    ∧ ∃ (l2_pr2_res : L_u),
      l2_pr2_rel ⌊ ds_d1eo ⌋ l2_pr2_res
      ∧ ∃ (length_res : Nats_u), length_rel l2_pr2_res length_res ∧ length2_res == length_res}}.

#[global] Hint Unfold length_unzip_2_spec: lia_unfold.

Theorem length_unzip_2 (ds_d1eo : L2): length_unzip_2_spec ds_d1eo.
Proof.
  destruct ds_d1eo as [ds_d1eo ds_d1eo_p].
  induction ds_d1eo as [ds_d1ep l IH_l|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (length2_res : Nats_u),
             length2_rel (App2_u ds_d1ep l) length2_res
             ∧ ∃ (l2_pr2_res : L_u),
               l2_pr2_rel (App2_u ds_d1ep l) l2_pr2_res
               ∧ ∃ (length_res : Nats_u), length_rel l2_pr2_res length_res ∧ length2_res == length_res)
            (IH_l ltac:(try clear IH_l; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (length2_res : Nats_u),
             length2_rel Emp2_u length2_res
             ∧ ∃ (l2_pr2_res : L_u),
               l2_pr2_rel Emp2_u l2_pr2_res
               ∧ ∃ (length_res : Nats_u), length_rel l2_pr2_res length_res ∧ length2_res == length_res)
            (# unit)
            ltac:(solver)).
Qed.

Definition map_spec
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513)))
  (ds_d1fL : L):
  Type :=
  L.

#[global] Hint Unfold map_spec: lia_unfold.

Definition map
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513)))
  (ds_d1fL : L):
  map_spec f ds_d1fL.
Proof.
  destruct ds_d1fL as [ds_d1fL ds_d1fL_p].
  try revert f_p; generalize dependent f; induction ds_d1fL as [x xs IH_xs|]; intros.
  - refine (App (getPackF f (# x)) (IH_xs ltac:(try clear IH_xs; solver) f)).
  - refine Emp.
Defined.

Inductive map_rel: @uPack (Z ::UT nilUT) Z → L_u → L_u → Prop :=
  | map_x_App: ∀ (f : @uPack (Z ::UT nilUT) Z) x xs (map_res : L_u),
               map_rel f xs map_res
               → ∀ (f_res : Z), getUPackRel f x f_res → map_rel f (App_u x xs) (App_u f_res map_res)
  | map_x_Emp: ∀ (f : @uPack (Z ::UT nilUT) Z), map_rel f Emp_u Emp_u.

#[global] Hint Constructors map_rel: core_hint_db.

#[global] Instance map_lookup_rel: dictionary rel map := { lookup' := map_rel }.

#[global] Instance map_getF: getFunc map_rel := { getF' := map }.

Theorem map_rel_funct [f : @uPack (Z ::UT nilUT) Z] [ds_d1fL : L_u]:
  ∀ (VV VV' : L_u), map_rel f ds_d1fL VV → (map_rel f ds_d1fL VV' → VV = VV').
Proof.
  try revert f_p; generalize dependent f; induction ds_d1fL as [x xs IH_xs|]; intros;
  rel_functionhood_body.
Qed.

#[global] Hint Resolve map_rel_funct: f_rel_funct_db.

Theorem map_x_App_lem f x xs map_x_App_lem_res:
  map_rel f (App_u x xs) map_x_App_lem_res
  ↔ ∃ (map_res : L_u),
    map_rel f xs map_res
    ∧ ∃ (f_res : Z), getUPackRel f x f_res ∧ map_x_App_lem_res == App_u f_res map_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite map_x_App_lem: f_rel_back.

Theorem map_x_Emp_lem f map_x_Emp_lem_res:
  map_rel f Emp_u map_x_Emp_lem_res ↔ map_x_Emp_lem_res == Emp_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite map_x_Emp_lem: f_rel_back.

Theorem map_rel_ex
  (f : @Pack
       ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp1: Z | True}
  ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_86795196 : ArgList ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_86795196 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z), True) x_86795196 v_x_86795196)))
  (ds_d1fL : L_u)
  (ds_d1fL_p : L_wf ds_d1fL ∧ True):
  map_rel ⌊ f ⌋ ds_d1fL ⌊ map f (exist _ ds_d1fL ds_d1fL_p) -⌋.
Proof.
  Opaque map.
  existence_lemma_pre map;
  try revert f_p; generalize dependent f; induction ds_d1fL as [x xs IH_xs|]; intros;
  [fix_notations;
   pose proof (IH_xs ltac:(try clear IH_xs; solver) f) as IH_29745491;
   try clear IH_xs |
   fix_notations];
  simpl in *.
  Transparent map.
  all: (existence_lemma_quicksolve map; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve map_rel_ex: rel_ax_db.

#[global] Opaque map.

Theorem map__map_rel_rw
  (f : @Pack
       ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp1: Z | True}
  ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_86795196 : ArgList ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_86795196 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z), True) x_86795196 v_x_86795196)))
  (ds_d1fL : L_u)
  (ds_d1fL_p : L_wf ds_d1fL ∧ True)
  (VV : L_u):
  ⌊ map f (exist _ ds_d1fL ds_d1fL_p) -⌋ = VV ↔ map_rel ⌊ f ⌋ ds_d1fL VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite map__map_rel_rw: f_rel_funct_db.

#[global] Hint Resolve map__map_rel_rw: rel_ax_db.

#[global] Instance map_lookup_rw: dictionary rwLem map := { lookup' := map__map_rel_rw }.

Theorem map__map_rel
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513)))
  (ds_d1fL : L)
  (VV : L_u):
  ⌊ map f ds_d1fL -⌋ = VV ↔ map_rel ⌊ f ⌋ ⌊ ds_d1fL ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite map__map_rel: f_rel_funct_db.

Theorem map__map_rel'
  (f_u : @uPack (Z ::UT nilUT) Z)
  (ds_d1fL_u : L_u)
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513)))
  (ds_d1fL : L)
  (VV : L_u):
  f_u = ⌊ f ⌋ → (ds_d1fL_u = ⌊ ds_d1fL ⌋ → ⌊ map f ds_d1fL -⌋ = VV ↔ map_rel f_u ds_d1fL_u VV).
Proof.
  intros -> ->. refine (map__map_rel f ds_d1fL VV).
Qed.

#[global] Hint Resolve map__map_rel': f_rel_funct_db.

Theorem map_rel_mk
  (f : @Pack
       ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp1: Z | True}
  ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_86795196 : ArgList ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_86795196 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z), True) x_86795196 v_x_86795196)))
  (ds_d1fL : L_u)
  (ds_d1fL_p : L_wf ds_d1fL ∧ True):
  {VV: _ | map_rel (packProj f) ds_d1fL VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, map_rel (packProj f) ds_d1fL VV)
          (map f (exist _ ds_d1fL ds_d1fL_p))
          _);
  rewrite <- map__map_rel';
  quicksolve.
Qed.

#[global] Hint Resolve map_rel_mk: f_rel_funct_db.

Definition length_map_spec
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_44453395 : ArgList ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT))
          (v_x_44453395 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {VV: Z | True}) (VV : Z), True) x_44453395 v_x_44453395)))
  (ds_d1eM : L):
  Type :=
  {{∃ (map_res : L_u),
    map_rel ⌊ f ⌋ ⌊ ds_d1eM ⌋ map_res
    ∧ ∃ (length_res : Nats_u),
      length_rel map_res length_res
      ∧ ∃ (length_res_2 : Nats_u), length_rel ⌊ ds_d1eM ⌋ length_res_2 ∧ length_res == length_res_2}}.

#[global] Hint Unfold length_map_spec: lia_unfold.

Theorem length_map
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_44453395 : ArgList ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT))
          (v_x_44453395 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {VV: Z | True}) (VV : Z), True) x_44453395 v_x_44453395)))
  (ds_d1eM : L):
  length_map_spec f ds_d1eM.
Proof.
  destruct ds_d1eM as [ds_d1eM ds_d1eM_p].
  try revert f_p; generalize dependent f; induction ds_d1eM as [x xs IH_xs|]; intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (map_res : L_u),
             map_rel ⌊ f ⌋ (App_u x xs) map_res
             ∧ ∃ (length_res : Nats_u),
               length_rel map_res length_res
               ∧ ∃ (length_res_2 : Nats_u), length_rel (App_u x xs) length_res_2 ∧ length_res == length_res_2)
            (IH_xs ltac:(try clear IH_xs; solver) f)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (map_res : L_u),
             map_rel ⌊ f ⌋ Emp_u map_res
             ∧ ∃ (length_res : Nats_u),
               length_rel map_res length_res
               ∧ ∃ (length_res_2 : Nats_u), length_rel Emp_u length_res_2 ∧ length_res == length_res_2)
            (# unit)
            ltac:(solver)).
Qed.

Definition reverse_spec (ds_d1fS : L): Type :=
  L.

#[global] Hint Unfold reverse_spec: lia_unfold.

Definition reverse (ds_d1fS : L): reverse_spec ds_d1fS.
Proof.
  destruct ds_d1fS as [ds_d1fS ds_d1fS_p].
  induction ds_d1fS as [x xs IH_xs|].
  - refine (append (IH_xs ltac:(try clear IH_xs; solver)) (App (# x) Emp)).
  - refine Emp.
Defined.

Inductive reverse_rel: L_u → L_u → Prop :=
  | reverse_App: ∀ x xs (reverse_res : L_u),
                 reverse_rel xs reverse_res
                 → ∀ (append_res : L_u),
                   append_rel reverse_res (App_u x Emp_u) append_res → reverse_rel (App_u x xs) append_res
  | reverse_Emp: reverse_rel Emp_u Emp_u.

#[global] Hint Constructors reverse_rel: core_hint_db.

#[global] Instance reverse_lookup_rel: dictionary rel reverse := { lookup' := reverse_rel }.

#[global] Instance reverse_getF: getFunc reverse_rel := { getF' := reverse }.

Theorem reverse_rel_funct [ds_d1fS : L_u]:
  ∀ (VV VV' : L_u), reverse_rel ds_d1fS VV → (reverse_rel ds_d1fS VV' → VV = VV').
Proof.
  induction ds_d1fS as [x xs IH_xs|]; rel_functionhood_body.
Qed.

#[global] Hint Resolve reverse_rel_funct: f_rel_funct_db.

Theorem reverse_App_lem x xs reverse_App_lem_res:
  reverse_rel (App_u x xs) reverse_App_lem_res
  ↔ ∃ (reverse_res : L_u),
    reverse_rel xs reverse_res
    ∧ ∃ (append_res : L_u),
      append_rel reverse_res (App_u x Emp_u) append_res ∧ reverse_App_lem_res == append_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite reverse_App_lem: f_rel_back.

Theorem reverse_Emp_lem reverse_Emp_lem_res:
  reverse_rel Emp_u reverse_Emp_lem_res ↔ reverse_Emp_lem_res == Emp_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite reverse_Emp_lem: f_rel_back.

Theorem reverse_rel_ex (ds_d1fS : L_u) (ds_d1fS_p : L_wf ds_d1fS ∧ True):
  reverse_rel ds_d1fS ⌊ reverse (exist _ ds_d1fS ds_d1fS_p) -⌋.
Proof.
  Opaque reverse.
  existence_lemma_pre reverse;
  induction ds_d1fS as [x xs IH_xs|];
  [fix_notations; pose proof (IH_xs ltac:(try clear IH_xs; solver)) as IH_67415571; try clear IH_xs |
   fix_notations];
  simpl in *.
  Transparent reverse.
  all: (existence_lemma_quicksolve reverse; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve reverse_rel_ex: rel_ax_db.

#[global] Opaque reverse.

Theorem reverse__reverse_rel_rw (ds_d1fS : L_u) (ds_d1fS_p : L_wf ds_d1fS ∧ True) (VV : L_u):
  ⌊ reverse (exist _ ds_d1fS ds_d1fS_p) -⌋ = VV ↔ reverse_rel ds_d1fS VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite reverse__reverse_rel_rw: f_rel_funct_db.

#[global] Hint Resolve reverse__reverse_rel_rw: rel_ax_db.

#[global] Instance reverse_lookup_rw: dictionary rwLem reverse := {
    lookup' := reverse__reverse_rel_rw }.

Theorem reverse__reverse_rel (ds_d1fS : L) (VV : L_u):
  ⌊ reverse ds_d1fS -⌋ = VV ↔ reverse_rel ⌊ ds_d1fS ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite reverse__reverse_rel: f_rel_funct_db.

Theorem reverse__reverse_rel' (ds_d1fS_u : L_u) (ds_d1fS : L) (VV : L_u):
  ds_d1fS_u = ⌊ ds_d1fS ⌋ → ⌊ reverse ds_d1fS -⌋ = VV ↔ reverse_rel ds_d1fS_u VV.
Proof.
  intros ->. refine (reverse__reverse_rel ds_d1fS VV).
Qed.

#[global] Hint Resolve reverse__reverse_rel': f_rel_funct_db.

Theorem reverse_rel_mk (ds_d1fS : L_u) (ds_d1fS_p : L_wf ds_d1fS ∧ True):
  {VV: _ | reverse_rel ds_d1fS VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, reverse_rel ds_d1fS VV) (reverse (exist _ ds_d1fS ds_d1fS_p)) _);
  rewrite <- reverse__reverse_rel';
  quicksolve.
Qed.

#[global] Hint Resolve reverse_rel_mk: f_rel_funct_db.

#[global] Instance reverse_pack:
  @Pack
  (L ::RT λ (ds_d1fS : L), nilRT)
  (L_u ::UT nilUT)
  ltac:(mkProjectsArgListTG ((L ::RT λ (ds_d1fS : L), nilRT)) ((L_u ::UT nilUT)))
  L_u
  (λ (x_26216328 : ArgList (L ::RT λ (ds_d1fS : L), nilRT)) (v_x_26216328 : L_u),
   ltac:(flattenP (λ (ds_d1fS : L) (VV : L_u), L_wf VV ∧ True) x_26216328 v_x_26216328)).
Proof.
  buildPackG reverse reverse_rel reverse__reverse_rel reverse_rel_funct.
Defined.

#[global] Instance reverse_upack: @uPack (L_u ::UT nilUT) L_u.
Proof.
  buildUPackG reverse_rel reverse_rel_funct.
Defined.

Definition reverse_nonempty_spec
  (ds_d1fV : L)
  (ds_d1fW : {{∃ (reverse_res : L_u), reverse_rel ⌊ ds_d1fV ⌋ reverse_res ∧ reverse_res == Emp_u}}):
  Type :=
  {{⌊ ds_d1fV ⌋ == Emp_u}}.

#[global] Hint Unfold reverse_nonempty_spec: lia_unfold.

Theorem reverse_nonempty
  (ds_d1fV : L)
  (ds_d1fW : {{∃ (reverse_res : L_u), reverse_rel ⌊ ds_d1fV ⌋ reverse_res ∧ reverse_res == Emp_u}}):
  reverse_nonempty_spec ds_d1fV ds_d1fW.
Proof.
  destruct ds_d1fV as [ds_d1fV ds_d1fV_p].
  destruct ds_d1fW as [ds_d1fW ds_d1fW_p].
  destruct ds_d1fV as [x xs|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), App_u x xs == Emp_u)
            (append_nonempty_ys
             (reverse (exist (λ (VV : L_u), L_wf VV ∧ True) xs ltac:(solver)))
             (App (# x) Emp)
             (subsumptionCast
              Unit
              (λ (ds_d1fG : Unit),
               ∃ (append_res : L_u),
               append_rel
               ⌊ reverse (exist (λ (VV : L_u), L_wf VV ∧ True) xs ltac:(solver)) ⌋
               (App_u x Emp_u)
               append_res
               ∧ append_res == Emp_u)
              (exist (λ (ds_d1fW : Unit),
                      ∃ (reverse_res : L_u),
                      reverse_rel (App_u x xs) reverse_res ∧ reverse_res == Emp_u) ds_d1fW ltac:(solver))
              ltac:(solver)))
            ltac:(solver)).
  - refine (subsumptionCast Unit (λ (VV : Unit), Emp_u == Emp_u) (# unit) ltac:(solver)).
Qed.

Definition take_spec (ds_d1ee : Nats) (ds_d1ef : L): Type :=
  L.

#[global] Hint Unfold take_spec: lia_unfold.

Definition take (ds_d1ee : Nats) (ds_d1ef : L): take_spec ds_d1ee ds_d1ef.
Proof.
  destruct ds_d1ee as [ds_d1ee ds_d1ee_p].
  destruct ds_d1ef as [ds_d1ef ds_d1ef_p].
  try revert ds_d1ef_p; generalize dependent ds_d1ef;
  induction ds_d1ee as [lq_anf7205759403792798697 IH_lq_anf7205759403792798697|];
  intros.
  - destruct ds_d1ef as [lq_anf7205759403792798695 lq_anf7205759403792798696|].
    + refine (App
              (# lq_anf7205759403792798695)
              (IH_lq_anf7205759403792798697
               ltac:(try clear IH_lq_anf7205759403792798697; solver)
               lq_anf7205759403792798696
               ltac:(try clear IH_lq_anf7205759403792798697; solver))).
    + refine Emp.
  - refine Emp.
Defined.

Inductive take_rel: Nats_u → L_u → L_u → Prop :=
  | take_Suc_App: ∀ lq_anf7205759403792798697 lq_anf7205759403792798695 lq_anf7205759403792798696
                    (take_res : L_u),
                  take_rel lq_anf7205759403792798697 lq_anf7205759403792798696 take_res
                  → take_rel
                    (Suc_u lq_anf7205759403792798697)
                    (App_u lq_anf7205759403792798695 lq_anf7205759403792798696)
                    (App_u lq_anf7205759403792798695 take_res)
  | take_Suc_Emp: ∀ lq_anf7205759403792798697, take_rel (Suc_u lq_anf7205759403792798697) Emp_u Emp_u
  | take_Zero_x: ∀ ds_d1ef, take_rel Zero_u ds_d1ef Emp_u.

#[global] Hint Constructors take_rel: core_hint_db.

#[global] Instance take_lookup_rel: dictionary rel take := { lookup' := take_rel }.

#[global] Instance take_getF: getFunc take_rel := { getF' := take }.

Theorem take_rel_funct [ds_d1ee : Nats_u] [ds_d1ef : L_u]:
  ∀ (VV VV' : L_u), take_rel ds_d1ee ds_d1ef VV → (take_rel ds_d1ee ds_d1ef VV' → VV = VV').
Proof.
  try revert ds_d1ef_p; generalize dependent ds_d1ef;
  induction ds_d1ee as [lq_anf7205759403792798697 IH_lq_anf7205759403792798697|];
  intros;
  [destruct ds_d1ef as [lq_anf7205759403792798695 lq_anf7205759403792798696|] |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve take_rel_funct: f_rel_funct_db.

Theorem take_Suc_App_lem
  lq_anf7205759403792798695 lq_anf7205759403792798696 lq_anf7205759403792798697 take_Suc_App_lem_res:
  take_rel
  (Suc_u lq_anf7205759403792798697)
  (App_u lq_anf7205759403792798695 lq_anf7205759403792798696)
  take_Suc_App_lem_res
  ↔ ∃ (take_res : L_u),
    take_rel lq_anf7205759403792798697 lq_anf7205759403792798696 take_res
    ∧ take_Suc_App_lem_res == App_u lq_anf7205759403792798695 take_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite take_Suc_App_lem: f_rel_back.

Theorem take_Suc_Emp_lem lq_anf7205759403792798697 take_Suc_Emp_lem_res:
  take_rel (Suc_u lq_anf7205759403792798697) Emp_u take_Suc_Emp_lem_res
  ↔ take_Suc_Emp_lem_res == Emp_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite take_Suc_Emp_lem: f_rel_back.

Theorem take_Zero_x_lem ds_d1ef take_Zero_x_lem_res:
  take_rel Zero_u ds_d1ef take_Zero_x_lem_res ↔ take_Zero_x_lem_res == Emp_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite take_Zero_x_lem: f_rel_back.

Theorem take_rel_ex
  (ds_d1ee : Nats_u)
  (ds_d1ee_p : Nats_wf ds_d1ee ∧ True)
  (ds_d1ef : L_u)
  (ds_d1ef_p : L_wf ds_d1ef ∧ True):
  take_rel ds_d1ee ds_d1ef ⌊ take (exist _ ds_d1ee ds_d1ee_p) (exist _ ds_d1ef ds_d1ef_p) -⌋.
Proof.
  Opaque take.
  existence_lemma_pre take;
  try revert ds_d1ef_p; generalize dependent ds_d1ef;
  induction ds_d1ee as [lq_anf7205759403792798697 IH_lq_anf7205759403792798697|];
  intros;
  [destruct ds_d1ef as [lq_anf7205759403792798695 lq_anf7205759403792798696|];
   [fix_notations;
    pose proof (IH_lq_anf7205759403792798697
                ltac:(try clear IH_lq_anf7205759403792798697; solver)
                lq_anf7205759403792798696
                ltac:(try clear IH_lq_anf7205759403792798697; solver)) as IH_32670755;
    try clear IH_lq_anf7205759403792798697 |
    fix_notations] |
   fix_notations];
  simpl in *.
  Transparent take.
  all: (existence_lemma_quicksolve take; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve take_rel_ex: rel_ax_db.

#[global] Opaque take.

Theorem take__take_rel_rw
  (ds_d1ee : Nats_u)
  (ds_d1ee_p : Nats_wf ds_d1ee ∧ True)
  (ds_d1ef : L_u)
  (ds_d1ef_p : L_wf ds_d1ef ∧ True)
  (VV : L_u):
  ⌊ take (exist _ ds_d1ee ds_d1ee_p) (exist _ ds_d1ef ds_d1ef_p) -⌋ = VV
  ↔ take_rel ds_d1ee ds_d1ef VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite take__take_rel_rw: f_rel_funct_db.

#[global] Hint Resolve take__take_rel_rw: rel_ax_db.

#[global] Instance take_lookup_rw: dictionary rwLem take := { lookup' := take__take_rel_rw }.

Theorem take__take_rel (ds_d1ee : Nats) (ds_d1ef : L) (VV : L_u):
  ⌊ take ds_d1ee ds_d1ef -⌋ = VV ↔ take_rel ⌊ ds_d1ee ⌋ ⌊ ds_d1ef ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite take__take_rel: f_rel_funct_db.

Theorem take__take_rel'
  (ds_d1ee_u : Nats_u) (ds_d1ef_u : L_u) (ds_d1ee : Nats) (ds_d1ef : L) (VV : L_u):
  ds_d1ee_u = ⌊ ds_d1ee ⌋
  → (ds_d1ef_u = ⌊ ds_d1ef ⌋ → ⌊ take ds_d1ee ds_d1ef -⌋ = VV ↔ take_rel ds_d1ee_u ds_d1ef_u VV).
Proof.
  intros -> ->. refine (take__take_rel ds_d1ee ds_d1ef VV).
Qed.

#[global] Hint Resolve take__take_rel': f_rel_funct_db.

Theorem take_rel_mk
  (ds_d1ee : Nats_u)
  (ds_d1ee_p : Nats_wf ds_d1ee ∧ True)
  (ds_d1ef : L_u)
  (ds_d1ef_p : L_wf ds_d1ef ∧ True):
  {VV: _ | take_rel ds_d1ee ds_d1ef VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, take_rel ds_d1ee ds_d1ef VV)
          (take (exist _ ds_d1ee ds_d1ee_p) (exist _ ds_d1ef ds_d1ef_p))
          _);
  rewrite <- take__take_rel';
  quicksolve.
Qed.

#[global] Hint Resolve take_rel_mk: f_rel_funct_db.

#[global] Instance take_pack:
  @Pack
  (Nats ::RT λ (ds_d1ee : Nats), L ::RT λ (ds_d1ef : L), nilRT)
  (Nats_u ::UT (L_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((Nats ::RT λ (ds_d1ee : Nats), L ::RT λ (ds_d1ef : L), nilRT)) ((Nats_u ::UT (L_u ::UT nilUT))))
  L_u
  (λ (x_24435272 : ArgList (Nats ::RT λ (ds_d1ee : Nats), L ::RT λ (ds_d1ef : L), nilRT))
     (v_x_24435272 : L_u),
   ltac:(flattenP (λ (ds_d1ee : Nats) (ds_d1ef : L) (VV : L_u), L_wf VV ∧ True) x_24435272 v_x_24435272)).
Proof.
  buildPackG take take_rel take__take_rel take_rel_funct.
Defined.

#[global] Instance take_upack: @uPack (Nats_u ::UT (L_u ::UT nilUT)) L_u.
Proof.
  buildUPackG take_rel take_rel_funct.
Defined.

Definition take_all_spec
  (ds_d1e3 : Nats)
  (ds_d1e4 : {ds_d1e4: L_u | L_wf ds_d1e4
                             ∧ ∃ (length_res : Nats_u),
                               length_rel ds_d1e4 length_res
                               ∧ ∃ (geqN_res : bool), geqN_rel ⌊ ds_d1e3 ⌋ length_res geqN_res ∧ is_true geqN_res}):
  Type :=
  {{∃ (take_res : L_u), take_rel ⌊ ds_d1e3 ⌋ ⌊ ds_d1e4 ⌋ take_res ∧ take_res == ⌊ ds_d1e4 ⌋}}.

#[global] Hint Unfold take_all_spec: lia_unfold.

Theorem take_all
  (ds_d1e3 : Nats)
  (ds_d1e4 : {ds_d1e4: L_u | L_wf ds_d1e4
                             ∧ ∃ (length_res : Nats_u),
                               length_rel ds_d1e4 length_res
                               ∧ ∃ (geqN_res : bool), geqN_rel ⌊ ds_d1e3 ⌋ length_res geqN_res ∧ is_true geqN_res}):
  take_all_spec ds_d1e3 ds_d1e4.
Proof.
  destruct ds_d1e3 as [ds_d1e3 ds_d1e3_p].
  destruct ds_d1e4 as [ds_d1e4 ds_d1e4_p].
  try revert ds_d1e4_p; generalize dependent ds_d1e4; induction ds_d1e3 as [n IH_n|]; intros.
  - destruct ds_d1e4 as [x xs|].
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∃ (take_res : L_u), take_rel (Suc_u n) (App_u x xs) take_res ∧ take_res == App_u x xs)
              (IH_n ltac:(try clear IH_n; solver) xs ltac:(try clear IH_n; solver))
              ltac:(solver)).
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit), ∃ (take_res : L_u), take_rel (Suc_u n) Emp_u take_res ∧ take_res == Emp_u)
              (# unit)
              ltac:(solver)).
  - destruct ds_d1e4 as [lq_anf7205759403792798746 lq_anf7205759403792798747|].
    + intros; exfalso; solver.
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit), ∃ (take_res : L_u), take_rel Zero_u Emp_u take_res ∧ take_res == Emp_u)
              (# unit)
              ltac:(solver)).
Qed.

Definition zip_spec (ds_d1fe ds_d1ff : L): Type :=
  L2.

#[global] Hint Unfold zip_spec: lia_unfold.

Definition zip (ds_d1fe ds_d1ff : L): zip_spec ds_d1fe ds_d1ff.
Proof.
  destruct ds_d1fe as [ds_d1fe ds_d1fe_p].
  destruct ds_d1ff as [ds_d1ff ds_d1ff_p].
  try revert ds_d1ff_p; generalize dependent ds_d1ff;
  induction ds_d1fe as [lq_anf7205759403792798606 lq_anf7205759403792798607 IH_lq_anf7205759403792798607|];
  intros.
  - destruct ds_d1ff as [lq_anf7205759403792798604 lq_anf7205759403792798605|].
    + refine (App2
              (MkPair (# lq_anf7205759403792798606) (# lq_anf7205759403792798604))
              (IH_lq_anf7205759403792798607
               ltac:(try clear IH_lq_anf7205759403792798607; solver)
               lq_anf7205759403792798605
               ltac:(try clear IH_lq_anf7205759403792798607; solver))).
    + refine Emp2.
  - refine Emp2.
Defined.

Inductive zip_rel: L_u → L_u → L2_u → Prop :=
  | zip_App_App: ∀ lq_anf7205759403792798606 lq_anf7205759403792798607 lq_anf7205759403792798604 lq_anf7205759403792798605
                   (zip_res : L2_u),
                 zip_rel lq_anf7205759403792798607 lq_anf7205759403792798605 zip_res
                 → zip_rel
                   (App_u lq_anf7205759403792798606 lq_anf7205759403792798607)
                   (App_u lq_anf7205759403792798604 lq_anf7205759403792798605)
                   (App2_u (MkPair_u lq_anf7205759403792798606 lq_anf7205759403792798604) zip_res)
  | zip_App_Emp: ∀ lq_anf7205759403792798606 lq_anf7205759403792798607,
                 zip_rel (App_u lq_anf7205759403792798606 lq_anf7205759403792798607) Emp_u Emp2_u
  | zip_Emp_x: ∀ ds_d1ff, zip_rel Emp_u ds_d1ff Emp2_u.

#[global] Hint Constructors zip_rel: core_hint_db.

#[global] Instance zip_lookup_rel: dictionary rel zip := { lookup' := zip_rel }.

#[global] Instance zip_getF: getFunc zip_rel := { getF' := zip }.

Theorem zip_rel_funct [ds_d1fe ds_d1ff : L_u]:
  ∀ (VV VV' : L2_u), zip_rel ds_d1fe ds_d1ff VV → (zip_rel ds_d1fe ds_d1ff VV' → VV = VV').
Proof.
  try revert ds_d1ff_p; generalize dependent ds_d1ff;
  induction ds_d1fe as [lq_anf7205759403792798606 lq_anf7205759403792798607 IH_lq_anf7205759403792798607|];
  intros;
  [destruct ds_d1ff as [lq_anf7205759403792798604 lq_anf7205759403792798605|] |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve zip_rel_funct: f_rel_funct_db.

Theorem zip_App_App_lem
  lq_anf7205759403792798604 lq_anf7205759403792798605 lq_anf7205759403792798606 lq_anf7205759403792798607 zip_App_App_lem_res:
  zip_rel
  (App_u lq_anf7205759403792798606 lq_anf7205759403792798607)
  (App_u lq_anf7205759403792798604 lq_anf7205759403792798605)
  zip_App_App_lem_res
  ↔ ∃ (zip_res : L2_u),
    zip_rel lq_anf7205759403792798607 lq_anf7205759403792798605 zip_res
    ∧ zip_App_App_lem_res
      == App2_u (MkPair_u lq_anf7205759403792798606 lq_anf7205759403792798604) zip_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite zip_App_App_lem: f_rel_back.

Theorem zip_App_Emp_lem lq_anf7205759403792798606 lq_anf7205759403792798607 zip_App_Emp_lem_res:
  zip_rel (App_u lq_anf7205759403792798606 lq_anf7205759403792798607) Emp_u zip_App_Emp_lem_res
  ↔ zip_App_Emp_lem_res == Emp2_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite zip_App_Emp_lem: f_rel_back.

Theorem zip_Emp_x_lem ds_d1ff zip_Emp_x_lem_res:
  zip_rel Emp_u ds_d1ff zip_Emp_x_lem_res ↔ zip_Emp_x_lem_res == Emp2_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite zip_Emp_x_lem: f_rel_back.

Theorem zip_rel_ex
  (ds_d1fe : L_u) (ds_d1fe_p : L_wf ds_d1fe ∧ True) (ds_d1ff : L_u) (ds_d1ff_p : L_wf ds_d1ff ∧ True):
  zip_rel ds_d1fe ds_d1ff ⌊ zip (exist _ ds_d1fe ds_d1fe_p) (exist _ ds_d1ff ds_d1ff_p) -⌋.
Proof.
  Opaque zip.
  existence_lemma_pre zip;
  try revert ds_d1ff_p; generalize dependent ds_d1ff;
  induction ds_d1fe as [lq_anf7205759403792798606 lq_anf7205759403792798607 IH_lq_anf7205759403792798607|];
  intros;
  [destruct ds_d1ff as [lq_anf7205759403792798604 lq_anf7205759403792798605|];
   [fix_notations;
    pose proof (IH_lq_anf7205759403792798607
                ltac:(try clear IH_lq_anf7205759403792798607; solver)
                lq_anf7205759403792798605
                ltac:(try clear IH_lq_anf7205759403792798607; solver)) as IH_77389074;
    try clear IH_lq_anf7205759403792798607 |
    fix_notations] |
   fix_notations];
  simpl in *.
  Transparent zip.
  all: (existence_lemma_quicksolve zip; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve zip_rel_ex: rel_ax_db.

#[global] Opaque zip.

Theorem zip__zip_rel_rw
  (ds_d1fe : L_u)
  (ds_d1fe_p : L_wf ds_d1fe ∧ True)
  (ds_d1ff : L_u)
  (ds_d1ff_p : L_wf ds_d1ff ∧ True)
  (VV : L2_u):
  ⌊ zip (exist _ ds_d1fe ds_d1fe_p) (exist _ ds_d1ff ds_d1ff_p) -⌋ = VV ↔ zip_rel ds_d1fe ds_d1ff VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite zip__zip_rel_rw: f_rel_funct_db.

#[global] Hint Resolve zip__zip_rel_rw: rel_ax_db.

#[global] Instance zip_lookup_rw: dictionary rwLem zip := { lookup' := zip__zip_rel_rw }.

Theorem zip__zip_rel (ds_d1fe ds_d1ff : L) (VV : L2_u):
  ⌊ zip ds_d1fe ds_d1ff -⌋ = VV ↔ zip_rel ⌊ ds_d1fe ⌋ ⌊ ds_d1ff ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite zip__zip_rel: f_rel_funct_db.

Theorem zip__zip_rel' (ds_d1fe_u ds_d1ff_u : L_u) (ds_d1fe ds_d1ff : L) (VV : L2_u):
  ds_d1fe_u = ⌊ ds_d1fe ⌋
  → (ds_d1ff_u = ⌊ ds_d1ff ⌋ → ⌊ zip ds_d1fe ds_d1ff -⌋ = VV ↔ zip_rel ds_d1fe_u ds_d1ff_u VV).
Proof.
  intros -> ->. refine (zip__zip_rel ds_d1fe ds_d1ff VV).
Qed.

#[global] Hint Resolve zip__zip_rel': f_rel_funct_db.

Theorem zip_rel_mk
  (ds_d1fe : L_u) (ds_d1fe_p : L_wf ds_d1fe ∧ True) (ds_d1ff : L_u) (ds_d1ff_p : L_wf ds_d1ff ∧ True):
  {VV: _ | zip_rel ds_d1fe ds_d1ff VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, zip_rel ds_d1fe ds_d1ff VV)
          (zip (exist _ ds_d1fe ds_d1fe_p) (exist _ ds_d1ff ds_d1ff_p))
          _);
  rewrite <- zip__zip_rel';
  quicksolve.
Qed.

#[global] Hint Resolve zip_rel_mk: f_rel_funct_db.

#[global] Instance zip_pack:
  @Pack
  (L ::RT λ (ds_d1fe : L), L ::RT λ (ds_d1ff : L), nilRT)
  (L_u ::UT (L_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((L ::RT λ (ds_d1fe : L), L ::RT λ (ds_d1ff : L), nilRT)) ((L_u ::UT (L_u ::UT nilUT))))
  L2_u
  (λ (x_44274041 : ArgList (L ::RT λ (ds_d1fe : L), L ::RT λ (ds_d1ff : L), nilRT))
     (v_x_44274041 : L2_u),
   ltac:(flattenP (λ (ds_d1fe ds_d1ff : L) (VV : L2_u), L2_wf VV ∧ True) x_44274041 v_x_44274041)).
Proof.
  buildPackG zip zip_rel zip__zip_rel zip_rel_funct.
Defined.

#[global] Instance zip_upack: @uPack (L_u ::UT (L_u ::UT nilUT)) L2_u.
Proof.
  buildUPackG zip_rel zip_rel_funct.
Defined.

Definition length_zip_spec
  (ds_d1eH : Nats)
  (ds_d1eI : {ds_d1eI: L_u | L_wf ds_d1eI
                             ∧ ∃ (length_res : Nats_u), length_rel ds_d1eI length_res ∧ length_res == ⌊ ds_d1eH ⌋})
  (ds_d1eJ : {ds_d1eJ: L_u | L_wf ds_d1eJ
                             ∧ ∃ (length_res : Nats_u), length_rel ds_d1eJ length_res ∧ length_res == ⌊ ds_d1eH ⌋}):
  Type :=
  {{∃ (zip_res : L2_u),
    zip_rel ⌊ ds_d1eI ⌋ ⌊ ds_d1eJ ⌋ zip_res
    ∧ ∃ (length2_res : Nats_u), length2_rel zip_res length2_res ∧ length2_res == ⌊ ds_d1eH ⌋}}.

#[global] Hint Unfold length_zip_spec: lia_unfold.

Theorem length_zip
  (ds_d1eH : Nats)
  (ds_d1eI : {ds_d1eI: L_u | L_wf ds_d1eI
                             ∧ ∃ (length_res : Nats_u), length_rel ds_d1eI length_res ∧ length_res == ⌊ ds_d1eH ⌋})
  (ds_d1eJ : {ds_d1eJ: L_u | L_wf ds_d1eJ
                             ∧ ∃ (length_res : Nats_u), length_rel ds_d1eJ length_res ∧ length_res == ⌊ ds_d1eH ⌋}):
  length_zip_spec ds_d1eH ds_d1eI ds_d1eJ.
Proof.
  destruct ds_d1eH as [ds_d1eH ds_d1eH_p].
  destruct ds_d1eI as [ds_d1eI ds_d1eI_p].
  destruct ds_d1eJ as [ds_d1eJ ds_d1eJ_p].
  try revert ds_d1eJ_p; generalize dependent ds_d1eJ;
  try revert ds_d1eI_p; generalize dependent ds_d1eI;
  induction ds_d1eH as [n IH_n|];
  intros.
  - destruct ds_d1eI as [x xs|].
    + destruct ds_d1eJ as [y ys|].
      ** refine (subsumptionCast
                 Unit
                 (λ (VV : Unit),
                  ∃ (zip_res : L2_u),
                  zip_rel (App_u x xs) (App_u y ys) zip_res
                  ∧ ∃ (length2_res : Nats_u), length2_rel zip_res length2_res ∧ length2_res == Suc_u n)
                 (IH_n
                  ltac:(try clear IH_n; solver)
                  xs
                  ltac:(try clear IH_n; solver)
                  ys
                  ltac:(try clear IH_n; solver))
                 ltac:(solver)).
      ** intros; exfalso; solver.
    + intros; exfalso; solver.
  - destruct ds_d1eI as [lq_anf7205759403792798645 lq_anf7205759403792798646|].
    + intros; exfalso; solver.
    + destruct ds_d1eJ as [lq_anf7205759403792798643 lq_anf7205759403792798644|].
      ** intros; exfalso; solver.
      ** refine (subsumptionCast
                 Unit
                 (λ (VV : Unit),
                  ∃ (zip_res : L2_u),
                  zip_rel Emp_u Emp_u zip_res
                  ∧ ∃ (length2_res : Nats_u), length2_rel zip_res length2_res ∧ length2_res == Zero_u)
                 (# unit)
                 ltac:(solver)).
Qed.

Definition length_zipWith_spec
  (ds_d1eC : Nats)
  (f : @Pack
       ({VV: Z | True}
        ::RT λ (lq_tmp0 : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({VV: Z | True}
  ::RT λ (lq_tmp0 : {VV: Z | True}),
       {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_41814097 : ArgList ({VV: Z | True}
                                 ::RT λ (lq_tmp0 : {VV: Z | True}),
                                      {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_41814097 : Z),
        ltac:(flattenP (λ (lq_tmp0 lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_41814097 v_x_41814097)))
  (ds_d1eD : {ds_d1eD: L_u | L_wf ds_d1eD
                             ∧ ∃ (length_res : Nats_u), length_rel ds_d1eD length_res ∧ length_res == ⌊ ds_d1eC ⌋})
  (ds_d1eE : {ds_d1eE: L_u | L_wf ds_d1eE
                             ∧ ∃ (length_res : Nats_u), length_rel ds_d1eE length_res ∧ length_res == ⌊ ds_d1eC ⌋}):
  Type :=
  {{∃ (zip_res : L2_u),
    zip_rel ⌊ ds_d1eD ⌋ ⌊ ds_d1eE ⌋ zip_res
    ∧ ∃ (length2_res : Nats_u), length2_rel zip_res length2_res ∧ length2_res == ⌊ ds_d1eC ⌋}}.

#[global] Hint Unfold length_zipWith_spec: lia_unfold.

Theorem length_zipWith
  (ds_d1eC : Nats)
  (f : @Pack
       ({VV: Z | True}
        ::RT λ (lq_tmp0 : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({VV: Z | True}
  ::RT λ (lq_tmp0 : {VV: Z | True}),
       {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_41814097 : ArgList ({VV: Z | True}
                                 ::RT λ (lq_tmp0 : {VV: Z | True}),
                                      {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_41814097 : Z),
        ltac:(flattenP (λ (lq_tmp0 lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_41814097 v_x_41814097)))
  (ds_d1eD : {ds_d1eD: L_u | L_wf ds_d1eD
                             ∧ ∃ (length_res : Nats_u), length_rel ds_d1eD length_res ∧ length_res == ⌊ ds_d1eC ⌋})
  (ds_d1eE : {ds_d1eE: L_u | L_wf ds_d1eE
                             ∧ ∃ (length_res : Nats_u), length_rel ds_d1eE length_res ∧ length_res == ⌊ ds_d1eC ⌋}):
  length_zipWith_spec ds_d1eC f ds_d1eD ds_d1eE.
Proof.
  destruct ds_d1eC as [ds_d1eC ds_d1eC_p].
  destruct ds_d1eD as [ds_d1eD ds_d1eD_p].
  destruct ds_d1eE as [ds_d1eE ds_d1eE_p].
  try revert ds_d1eE_p; generalize dependent ds_d1eE;
  try revert ds_d1eD_p; generalize dependent ds_d1eD;
  try revert f_p; generalize dependent f;
  induction ds_d1eC as [n IH_n|];
  intros.
  - destruct ds_d1eD as [x xs|].
    + destruct ds_d1eE as [y ys|].
      ** refine (subsumptionCast
                 Unit
                 (λ (VV : Unit),
                  ∃ (zip_res : L2_u),
                  zip_rel (App_u x xs) (App_u y ys) zip_res
                  ∧ ∃ (length2_res : Nats_u), length2_rel zip_res length2_res ∧ length2_res == Suc_u n)
                 (IH_n
                  ltac:(try clear IH_n; solver)
                  f
                  xs
                  ltac:(try clear IH_n; solver)
                  ys
                  ltac:(try clear IH_n; solver))
                 ltac:(solver)).
      ** intros; exfalso; solver.
    + intros; exfalso; solver.
  - destruct ds_d1eD as [lq_anf7205759403792798666 lq_anf7205759403792798667|].
    + intros; exfalso; solver.
    + destruct ds_d1eE as [lq_anf7205759403792798664 lq_anf7205759403792798665|].
      ** intros; exfalso; solver.
      ** refine (subsumptionCast
                 Unit
                 (λ (VV : Unit),
                  ∃ (zip_res : L2_u),
                  zip_rel Emp_u Emp_u zip_res
                  ∧ ∃ (length2_res : Nats_u), length2_rel zip_res length2_res ∧ length2_res == Zero_u)
                 (# unit)
                 ltac:(solver)).
Qed.

Definition zipWith_spec
  (f : @Pack
       ({VV: Z | True}
        ::RT λ (lq_tmp0 : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({VV: Z | True}
  ::RT λ (lq_tmp0 : {VV: Z | True}),
       {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_41814097 : ArgList ({VV: Z | True}
                                 ::RT λ (lq_tmp0 : {VV: Z | True}),
                                      {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_41814097 : Z),
        ltac:(flattenP (λ (lq_tmp0 lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_41814097 v_x_41814097)))
  (ds_d1f4 ds_d1f5 : L):
  Type :=
  L.

#[global] Hint Unfold zipWith_spec: lia_unfold.

Definition zipWith
  (f : @Pack
       ({VV: Z | True}
        ::RT λ (lq_tmp0 : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({VV: Z | True}
  ::RT λ (lq_tmp0 : {VV: Z | True}),
       {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_41814097 : ArgList ({VV: Z | True}
                                 ::RT λ (lq_tmp0 : {VV: Z | True}),
                                      {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_41814097 : Z),
        ltac:(flattenP (λ (lq_tmp0 lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_41814097 v_x_41814097)))
  (ds_d1f4 ds_d1f5 : L):
  zipWith_spec f ds_d1f4 ds_d1f5.
Proof.
  destruct ds_d1f4 as [ds_d1f4 ds_d1f4_p].
  destruct ds_d1f5 as [ds_d1f5 ds_d1f5_p].
  try revert ds_d1f5_p; generalize dependent ds_d1f5; try revert f_p; generalize dependent f;
  induction ds_d1f4 as [lq_anf7205759403792798622 lq_anf7205759403792798623 IH_lq_anf7205759403792798623|];
  intros.
  - destruct ds_d1f5 as [lq_anf7205759403792798620 lq_anf7205759403792798621|].
    + refine (App
              (getPackF f (# lq_anf7205759403792798622) (# lq_anf7205759403792798620))
              (IH_lq_anf7205759403792798623
               ltac:(try clear IH_lq_anf7205759403792798623; solver)
               f
               lq_anf7205759403792798621
               ltac:(try clear IH_lq_anf7205759403792798623; solver))).
    + refine Emp.
  - refine Emp.
Defined.

Inductive zipWith_rel: @uPack (Z ::UT (Z ::UT nilUT)) Z → L_u → L_u → L_u → Prop :=
  | zipWith_x_App_App: ∀ (f : @uPack (Z ::UT (Z ::UT nilUT)) Z)
                         lq_anf7205759403792798622 lq_anf7205759403792798623 lq_anf7205759403792798620 lq_anf7205759403792798621
                         (zipWith_res : L_u),
                       zipWith_rel f lq_anf7205759403792798623 lq_anf7205759403792798621 zipWith_res
                       → ∀ (f_res : Z),
                         getUPackRel f lq_anf7205759403792798622 lq_anf7205759403792798620 f_res
                         → zipWith_rel
                           f
                           (App_u lq_anf7205759403792798622 lq_anf7205759403792798623)
                           (App_u lq_anf7205759403792798620 lq_anf7205759403792798621)
                           (App_u f_res zipWith_res)
  | zipWith_x_App_Emp: ∀ (f : @uPack (Z ::UT (Z ::UT nilUT)) Z)
                         lq_anf7205759403792798622 lq_anf7205759403792798623,
                       zipWith_rel f (App_u lq_anf7205759403792798622 lq_anf7205759403792798623) Emp_u Emp_u
  | zipWith_x_Emp_x: ∀ (f : @uPack (Z ::UT (Z ::UT nilUT)) Z) ds_d1f5,
                     zipWith_rel f Emp_u ds_d1f5 Emp_u.

#[global] Hint Constructors zipWith_rel: core_hint_db.

#[global] Instance zipWith_lookup_rel: dictionary rel zipWith := { lookup' := zipWith_rel }.

#[global] Instance zipWith_getF: getFunc zipWith_rel := { getF' := zipWith }.

Theorem zipWith_rel_funct [f : @uPack (Z ::UT (Z ::UT nilUT)) Z] [ds_d1f4 ds_d1f5 : L_u]:
  ∀ (VV VV' : L_u), zipWith_rel f ds_d1f4 ds_d1f5 VV → (zipWith_rel f ds_d1f4 ds_d1f5 VV' → VV = VV').
Proof.
  try revert ds_d1f5_p; generalize dependent ds_d1f5; try revert f_p; generalize dependent f;
  induction ds_d1f4 as [lq_anf7205759403792798622 lq_anf7205759403792798623 IH_lq_anf7205759403792798623|];
  intros;
  [destruct ds_d1f5 as [lq_anf7205759403792798620 lq_anf7205759403792798621|] |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve zipWith_rel_funct: f_rel_funct_db.

Theorem zipWith_x_App_App_lem
  f lq_anf7205759403792798620 lq_anf7205759403792798621 lq_anf7205759403792798622 lq_anf7205759403792798623 zipWith_x_App_App_lem_res:
  zipWith_rel
  f
  (App_u lq_anf7205759403792798622 lq_anf7205759403792798623)
  (App_u lq_anf7205759403792798620 lq_anf7205759403792798621)
  zipWith_x_App_App_lem_res
  ↔ ∃ (zipWith_res : L_u),
    zipWith_rel f lq_anf7205759403792798623 lq_anf7205759403792798621 zipWith_res
    ∧ ∃ (f_res : Z),
      getUPackRel f lq_anf7205759403792798622 lq_anf7205759403792798620 f_res
      ∧ zipWith_x_App_App_lem_res == App_u f_res zipWith_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite zipWith_x_App_App_lem: f_rel_back.

Theorem zipWith_x_App_Emp_lem
  f lq_anf7205759403792798622 lq_anf7205759403792798623 zipWith_x_App_Emp_lem_res:
  zipWith_rel
  f
  (App_u lq_anf7205759403792798622 lq_anf7205759403792798623)
  Emp_u
  zipWith_x_App_Emp_lem_res
  ↔ zipWith_x_App_Emp_lem_res == Emp_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite zipWith_x_App_Emp_lem: f_rel_back.

Theorem zipWith_x_Emp_x_lem ds_d1f5 f zipWith_x_Emp_x_lem_res:
  zipWith_rel f Emp_u ds_d1f5 zipWith_x_Emp_x_lem_res ↔ zipWith_x_Emp_x_lem_res == Emp_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite zipWith_x_Emp_x_lem: f_rel_back.

Theorem zipWith_rel_ex
  (f : @Pack
       ({lq_tmp0: Z | True}
        ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}),
             {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({lq_tmp0: Z | True}
  ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}),
       {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_15576161 : ArgList ({lq_tmp0: Z | True}
                                 ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}),
                                      {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_15576161 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {lq_tmp0: Z | True})
   (lq_tmp1 : {lq_tmp1: Z | True})
   (VV : Z),
 True) x_15576161 v_x_15576161)))
  (ds_d1f4 : L_u)
  (ds_d1f4_p : L_wf ds_d1f4 ∧ True)
  (ds_d1f5 : L_u)
  (ds_d1f5_p : L_wf ds_d1f5 ∧ True):
  zipWith_rel
  ⌊ f ⌋
  ds_d1f4
  ds_d1f5
  ⌊ zipWith f (exist _ ds_d1f4 ds_d1f4_p) (exist _ ds_d1f5 ds_d1f5_p) -⌋.
Proof.
  Opaque zipWith.
  existence_lemma_pre zipWith;
  try revert ds_d1f5_p; generalize dependent ds_d1f5; try revert f_p; generalize dependent f;
  induction ds_d1f4 as [lq_anf7205759403792798622 lq_anf7205759403792798623 IH_lq_anf7205759403792798623|];
  intros;
  [destruct ds_d1f5 as [lq_anf7205759403792798620 lq_anf7205759403792798621|];
   [fix_notations;
    pose proof (IH_lq_anf7205759403792798623
                ltac:(try clear IH_lq_anf7205759403792798623; solver)
                f
                lq_anf7205759403792798621
                ltac:(try clear IH_lq_anf7205759403792798623; solver)) as IH_26952299;
    try clear IH_lq_anf7205759403792798623 |
    fix_notations] |
   fix_notations];
  simpl in *.
  Transparent zipWith.
  all: (existence_lemma_quicksolve zipWith; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve zipWith_rel_ex: rel_ax_db.

#[global] Opaque zipWith.

Theorem zipWith__zipWith_rel_rw
  (f : @Pack
       ({lq_tmp0: Z | True}
        ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}),
             {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({lq_tmp0: Z | True}
  ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}),
       {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_15576161 : ArgList ({lq_tmp0: Z | True}
                                 ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}),
                                      {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_15576161 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {lq_tmp0: Z | True})
   (lq_tmp1 : {lq_tmp1: Z | True})
   (VV : Z),
 True) x_15576161 v_x_15576161)))
  (ds_d1f4 : L_u)
  (ds_d1f4_p : L_wf ds_d1f4 ∧ True)
  (ds_d1f5 : L_u)
  (ds_d1f5_p : L_wf ds_d1f5 ∧ True)
  (VV : L_u):
  ⌊ zipWith f (exist _ ds_d1f4 ds_d1f4_p) (exist _ ds_d1f5 ds_d1f5_p) -⌋ = VV
  ↔ zipWith_rel ⌊ f ⌋ ds_d1f4 ds_d1f5 VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite zipWith__zipWith_rel_rw: f_rel_funct_db.

#[global] Hint Resolve zipWith__zipWith_rel_rw: rel_ax_db.

#[global] Instance zipWith_lookup_rw: dictionary rwLem zipWith := {
    lookup' := zipWith__zipWith_rel_rw }.

Theorem zipWith__zipWith_rel
  (f : @Pack
       ({VV: Z | True}
        ::RT λ (lq_tmp0 : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({VV: Z | True}
  ::RT λ (lq_tmp0 : {VV: Z | True}),
       {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_41814097 : ArgList ({VV: Z | True}
                                 ::RT λ (lq_tmp0 : {VV: Z | True}),
                                      {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_41814097 : Z),
        ltac:(flattenP (λ (lq_tmp0 lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_41814097 v_x_41814097)))
  (ds_d1f4 ds_d1f5 : L)
  (VV : L_u):
  ⌊ zipWith f ds_d1f4 ds_d1f5 -⌋ = VV ↔ zipWith_rel ⌊ f ⌋ ⌊ ds_d1f4 ⌋ ⌊ ds_d1f5 ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite zipWith__zipWith_rel: f_rel_funct_db.

Theorem zipWith__zipWith_rel'
  (f_u : @uPack (Z ::UT (Z ::UT nilUT)) Z)
  (ds_d1f4_u ds_d1f5_u : L_u)
  (f : @Pack
       ({VV: Z | True}
        ::RT λ (lq_tmp0 : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({VV: Z | True}
  ::RT λ (lq_tmp0 : {VV: Z | True}),
       {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_41814097 : ArgList ({VV: Z | True}
                                 ::RT λ (lq_tmp0 : {VV: Z | True}),
                                      {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_41814097 : Z),
        ltac:(flattenP (λ (lq_tmp0 lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_41814097 v_x_41814097)))
  (ds_d1f4 ds_d1f5 : L)
  (VV : L_u):
  f_u = ⌊ f ⌋
  → (ds_d1f4_u = ⌊ ds_d1f4 ⌋
     → (ds_d1f5_u = ⌊ ds_d1f5 ⌋
        → ⌊ zipWith f ds_d1f4 ds_d1f5 -⌋ = VV ↔ zipWith_rel f_u ds_d1f4_u ds_d1f5_u VV)).
Proof.
  intros -> -> ->. refine (zipWith__zipWith_rel f ds_d1f4 ds_d1f5 VV).
Qed.

#[global] Hint Resolve zipWith__zipWith_rel': f_rel_funct_db.

Theorem zipWith_rel_mk
  (f : @Pack
       ({lq_tmp0: Z | True}
        ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}),
             {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({lq_tmp0: Z | True}
  ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}),
       {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_15576161 : ArgList ({lq_tmp0: Z | True}
                                 ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}),
                                      {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_15576161 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {lq_tmp0: Z | True})
   (lq_tmp1 : {lq_tmp1: Z | True})
   (VV : Z),
 True) x_15576161 v_x_15576161)))
  (ds_d1f4 : L_u)
  (ds_d1f4_p : L_wf ds_d1f4 ∧ True)
  (ds_d1f5 : L_u)
  (ds_d1f5_p : L_wf ds_d1f5 ∧ True):
  {VV: _ | zipWith_rel (packProj f) ds_d1f4 ds_d1f5 VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, zipWith_rel (packProj f) ds_d1f4 ds_d1f5 VV)
          (zipWith f (exist _ ds_d1f4 ds_d1f4_p) (exist _ ds_d1f5 ds_d1f5_p))
          _);
  rewrite <- zipWith__zipWith_rel';
  quicksolve.
Qed.

#[global] Hint Resolve zipWith_rel_mk: f_rel_funct_db.

Definition zip_take_spec (ds_d1fq m : L): Type :=
  {{∃ (zip_res : L2_u),
    zip_rel ⌊ ds_d1fq ⌋ ⌊ m ⌋ zip_res
    ∧ ∃ (length_res : Nats_u),
      length_rel ⌊ ds_d1fq ⌋ length_res
      ∧ ∃ (take_res : L_u),
        take_rel length_res ⌊ m ⌋ take_res
        ∧ ∃ (length_res_2 : Nats_u),
          length_rel ⌊ m ⌋ length_res_2
          ∧ ∃ (take_res_2 : L_u),
            take_rel length_res_2 ⌊ ds_d1fq ⌋ take_res_2
            ∧ ∃ (zip_res_2 : L2_u), zip_rel take_res_2 take_res zip_res_2 ∧ zip_res == zip_res_2}}.

#[global] Hint Unfold zip_take_spec: lia_unfold.

Theorem zip_take (ds_d1fq m : L): zip_take_spec ds_d1fq m.
Proof.
  destruct ds_d1fq as [ds_d1fq ds_d1fq_p].
  destruct m as [m m_p].
  try revert m_p; generalize dependent m;
  induction ds_d1fq as [lq_anf7205759403792798728 lq_anf7205759403792798729 IH_lq_anf7205759403792798729|];
  intros.
  - destruct m as [lq_anf7205759403792798708 lq_anf7205759403792798709|].
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∃ (zip_res : L2_u),
               zip_rel
               (App_u lq_anf7205759403792798728 lq_anf7205759403792798729)
               (App_u lq_anf7205759403792798708 lq_anf7205759403792798709)
               zip_res
               ∧ ∃ (length_res : Nats_u),
                 length_rel (App_u lq_anf7205759403792798728 lq_anf7205759403792798729) length_res
                 ∧ ∃ (take_res : L_u),
                   take_rel length_res (App_u lq_anf7205759403792798708 lq_anf7205759403792798709) take_res
                   ∧ ∃ (length_res_2 : Nats_u),
                     length_rel (App_u lq_anf7205759403792798708 lq_anf7205759403792798709) length_res_2
                     ∧ ∃ (take_res_2 : L_u),
                       take_rel length_res_2 (App_u lq_anf7205759403792798728 lq_anf7205759403792798729) take_res_2
                       ∧ ∃ (zip_res_2 : L2_u), zip_rel take_res_2 take_res zip_res_2 ∧ zip_res == zip_res_2)
              (IH_lq_anf7205759403792798729
               ltac:(try clear IH_lq_anf7205759403792798729; solver)
               lq_anf7205759403792798709
               ltac:(try clear IH_lq_anf7205759403792798729; solver))
              ltac:(solver)).
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∃ (zip_res : L2_u),
               zip_rel (App_u lq_anf7205759403792798728 lq_anf7205759403792798729) Emp_u zip_res
               ∧ ∃ (length_res : Nats_u),
                 length_rel (App_u lq_anf7205759403792798728 lq_anf7205759403792798729) length_res
                 ∧ ∃ (take_res : L_u),
                   take_rel length_res Emp_u take_res
                   ∧ ∃ (length_res_2 : Nats_u),
                     length_rel Emp_u length_res_2
                     ∧ ∃ (take_res_2 : L_u),
                       take_rel length_res_2 (App_u lq_anf7205759403792798728 lq_anf7205759403792798729) take_res_2
                       ∧ ∃ (zip_res_2 : L2_u), zip_rel take_res_2 take_res zip_res_2 ∧ zip_res == zip_res_2)
              (# unit)
              ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (zip_res : L2_u),
             zip_rel Emp_u m zip_res
             ∧ ∃ (length_res : Nats_u),
               length_rel Emp_u length_res
               ∧ ∃ (take_res : L_u),
                 take_rel length_res m take_res
                 ∧ ∃ (length_res_2 : Nats_u),
                   length_rel m length_res_2
                   ∧ ∃ (take_res_2 : L_u),
                     take_rel length_res_2 Emp_u take_res_2
                     ∧ ∃ (zip_res_2 : L2_u), zip_rel take_res_2 take_res zip_res_2 ∧ zip_res == zip_res_2)
            (let _: VV
                    == ⌊ zip
                         (take (length (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) Emp)
                         (take Zero (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) ⌋
                    ∧ VV == ⌊ zip Emp Emp ⌋ :=
             ⌈ let _: VV
                      == ⌊ zip
                           (take (length (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) Emp)
                           (take (length Emp) (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) ⌋
                      ∧ VV == ⌊ zip (take (length (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) Emp) Emp ⌋ :=
               ⌈ let _: ⌊ zip (take (length (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) Emp) Emp ⌋
                        == ⌊ zip
                             (take (length (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) Emp)
                             (take (length Emp) (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) ⌋ :=
                 ltac:(solver) in
                 subsumptionCast
                 L2_u
                 (λ (VV : L2_u),
                  L2_wf VV
                  ∧ VV == ⌊ zip (take (length (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) Emp) Emp ⌋)
                 (zip
                  (take (length (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) Emp)
                  (take (length Emp) (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))))
                 ltac:(solver) ⌉ in
               let _: VV == ⌊ zip (take (length (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) Emp) Emp ⌋
                      ∧ VV == ⌊ zip Emp Emp ⌋ :=
               ⌈ let _: ⌊ zip Emp Emp ⌋
                        == ⌊ zip (take (length (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) Emp) Emp ⌋ :=
                 ltac:(solver) in
                 subsumptionCast
                 L2_u
                 (λ (VV : L2_u), L2_wf VV ∧ VV == ⌊ zip Emp Emp ⌋)
                 (zip (take (length (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) Emp) Emp)
                 ltac:(solver) ⌉ in
               let _: VV == ⌊ zip Emp Emp ⌋
                      ∧ VV == ⌊ zip Emp (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver)) ⌋ :=
               ⌈ let _: ⌊ zip Emp (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver)) ⌋ == ⌊ zip Emp Emp ⌋ :=
                 ltac:(solver) in
                 subsumptionCast
                 L2_u
                 (λ (VV : L2_u), L2_wf VV ∧ VV == ⌊ zip Emp (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver)) ⌋)
                 (zip Emp Emp)
                 ltac:(solver) ⌉ in
               let _: ⌊ zip Emp Emp ⌋
                      == ⌊ zip
                           (take (length (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) Emp)
                           (take Zero (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) ⌋ :=
               ltac:(solver) in
               subsumptionCast
               L2_u
               (λ (VV : L2_u), L2_wf VV ∧ VV == ⌊ zip Emp Emp ⌋)
               (zip
                (take (length (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) Emp)
                (take Zero (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))))
               ltac:(solver) ⌉ in
             # unit)
            ltac:(solver)).
Qed.
