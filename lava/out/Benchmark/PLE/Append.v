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
       ltac:(mkProjectsArgListTG ({VV: Z | True}
 ::RT λ (lq_tmp0 : {VV: Z | True}),
      {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT (Z ::UT nilUT))))
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
       ltac:(mkProjectsArgListTG ({VV: Z | True}
 ::RT λ (lq_tmp0 : {VV: Z | True}),
      {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT (Z ::UT nilUT))))
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

#[global] Instance flip_lookup_funct: dictionary functionhood flip := {
    lookup' := flip_rel_funct }.

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
       ltac:(mkProjectsArgListTG ({lq_tmp0: Z | True}
 ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}),
      {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT) ((Z ::UT (Z ::UT nilUT))))
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
       ltac:(mkProjectsArgListTG ({lq_tmp0: Z | True}
 ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}),
      {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT) ((Z ::UT (Z ::UT nilUT))))
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
       ltac:(mkProjectsArgListTG ({VV: Z | True}
 ::RT λ (lq_tmp0 : {VV: Z | True}),
      {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT (Z ::UT nilUT))))
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
       ltac:(mkProjectsArgListTG ({VV: Z | True}
 ::RT λ (lq_tmp0 : {VV: Z | True}),
      {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT (Z ::UT nilUT))))
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
       ltac:(mkProjectsArgListTG ({lq_tmp0: Z | True}
 ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}),
      {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT) ((Z ::UT (Z ::UT nilUT))))
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

Definition Pair_eq (x y : Pair_u): bool :=
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

Definition Pair_wf (x : Pair_u): Prop :=
  match x with | MkPair_u VV VV_ => True end.

Theorem Pair_wf_ref [p : Pair_u → Prop] (tm : {v: Pair_u | Pair_wf v ∧ p v}): Pair_wf ⌊ tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation Pair := {x: Pair_u | Pair_wf x ∧ True}.

Definition MkPair_lem (VV VV_ : {VV: Z | True}): Pair_wf (MkPair_u ⌊ VV -⌋ ⌊ VV_ -⌋) ∧ True.
Proof.
  repeat first [split | solver].
Defined.

Definition MkPair (VV VV_ : {VV: Z | True}): Pair :=
  exist _ (MkPair_u ⌊ VV -⌋ ⌊ VV_ -⌋) (MkPair_lem VV VV_).

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

Definition geqN_spec (ds_d2AJ ds_d2AK : Nats): Type :=
  Bool.

#[global] Hint Unfold geqN_spec: lia_unfold.

Definition geqN (ds_d2AJ ds_d2AK : Nats): geqN_spec ds_d2AJ ds_d2AK.
Proof.
  destruct ds_d2AJ as [ds_d2AJ ds_d2AJ_p].
  destruct ds_d2AK as [ds_d2AK ds_d2AK_p].
  try revert ds_d2AJ_p; generalize dependent ds_d2AJ;
  induction ds_d2AK as [lq_anf7205759403792803968 IH_lq_anf7205759403792803968|];
  intros.
  - destruct ds_d2AJ as [m|].
    + refine (IH_lq_anf7205759403792803968
              ltac:(try clear IH_lq_anf7205759403792803968; solver)
              m
              ltac:(try clear IH_lq_anf7205759403792803968; solver)).
    + refine (# false).
  - refine (# true).
Defined.

Inductive geqN_rel: Nats_u → Nats_u → bool → Prop :=
  | geqN_Suc_Suc: ∀ m lq_anf7205759403792803968 (geqN_res : bool),
                  geqN_rel m lq_anf7205759403792803968 geqN_res
                  → geqN_rel (Suc_u m) (Suc_u lq_anf7205759403792803968) geqN_res
  | geqN_Zero_Suc: ∀ lq_anf7205759403792803968,
                   geqN_rel Zero_u (Suc_u lq_anf7205759403792803968) false
  | geqN_x_Zero: ∀ ds_d2AJ, geqN_rel ds_d2AJ Zero_u true.

#[global] Hint Constructors geqN_rel: core_hint_db.

#[global] Instance geqN_lookup_rel: dictionary rel geqN := { lookup' := geqN_rel }.

#[global] Instance geqN_getF: getFunc geqN_rel := { getF' := geqN }.

Theorem geqN_rel_funct [ds_d2AJ ds_d2AK : Nats_u]:
  ∀ (VV VV' : bool), geqN_rel ds_d2AJ ds_d2AK VV → (geqN_rel ds_d2AJ ds_d2AK VV' → VV = VV').
Proof.
  try revert ds_d2AJ_p; generalize dependent ds_d2AJ;
  induction ds_d2AK as [lq_anf7205759403792803968 IH_lq_anf7205759403792803968|];
  intros;
  [destruct ds_d2AJ as [m|] |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve geqN_rel_funct: f_rel_funct_db.

#[global] Instance geqN_lookup_funct: dictionary functionhood geqN := {
    lookup' := geqN_rel_funct }.

Theorem geqN_Suc_Suc_lem lq_anf7205759403792803968 m geqN_Suc_Suc_lem_res:
  geqN_rel (Suc_u m) (Suc_u lq_anf7205759403792803968) geqN_Suc_Suc_lem_res
  ↔ ∃ (geqN_res : bool),
    geqN_rel m lq_anf7205759403792803968 geqN_res ∧ geqN_Suc_Suc_lem_res == geqN_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite geqN_Suc_Suc_lem: f_rel_back.

Theorem geqN_Zero_Suc_lem lq_anf7205759403792803968 geqN_Zero_Suc_lem_res:
  geqN_rel Zero_u (Suc_u lq_anf7205759403792803968) geqN_Zero_Suc_lem_res
  ↔ geqN_Zero_Suc_lem_res == false.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite geqN_Zero_Suc_lem: f_rel_back.

Theorem geqN_x_Zero_lem ds_d2AJ geqN_x_Zero_lem_res:
  geqN_rel ds_d2AJ Zero_u geqN_x_Zero_lem_res ↔ geqN_x_Zero_lem_res == true.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite geqN_x_Zero_lem: f_rel_back.

Theorem geqN_rel_ex
  (ds_d2AJ : Nats_u)
  (ds_d2AJ_p : Nats_wf ds_d2AJ ∧ True)
  (ds_d2AK : Nats_u)
  (ds_d2AK_p : Nats_wf ds_d2AK ∧ True):
  geqN_rel ds_d2AJ ds_d2AK ⌊ geqN (exist _ ds_d2AJ ds_d2AJ_p) (exist _ ds_d2AK ds_d2AK_p) -⌋.
Proof.
  Opaque geqN.
  existence_lemma_pre geqN;
  try revert ds_d2AJ_p; generalize dependent ds_d2AJ;
  induction ds_d2AK as [lq_anf7205759403792803968 IH_lq_anf7205759403792803968|];
  intros;
  [destruct ds_d2AJ as [m|];
   [fix_notations;
    pose proof (IH_lq_anf7205759403792803968
                ltac:(try clear IH_lq_anf7205759403792803968; solver)
                m
                ltac:(try clear IH_lq_anf7205759403792803968; solver)) as IH_27002835;
    try clear IH_lq_anf7205759403792803968 |
    fix_notations] |
   fix_notations];
  simpl in *.
  Transparent geqN.
  all: (existence_lemma_quicksolve geqN; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve geqN_rel_ex: rel_ax_db.

#[global] Opaque geqN.

Theorem geqN__geqN_rel_rw
  (ds_d2AJ : Nats_u)
  (ds_d2AJ_p : Nats_wf ds_d2AJ ∧ True)
  (ds_d2AK : Nats_u)
  (ds_d2AK_p : Nats_wf ds_d2AK ∧ True)
  (VV : bool):
  ⌊ geqN (exist _ ds_d2AJ ds_d2AJ_p) (exist _ ds_d2AK ds_d2AK_p) -⌋ = VV
  ↔ geqN_rel ds_d2AJ ds_d2AK VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite geqN__geqN_rel_rw: f_rel_funct_db.

#[global] Hint Resolve geqN__geqN_rel_rw: rel_ax_db.

#[global] Instance geqN_lookup_rw: dictionary rwLem geqN := { lookup' := geqN__geqN_rel_rw }.

Theorem geqN__geqN_rel (ds_d2AJ ds_d2AK : Nats) (VV : bool):
  ⌊ geqN ds_d2AJ ds_d2AK -⌋ = VV ↔ geqN_rel ⌊ ds_d2AJ ⌋ ⌊ ds_d2AK ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite geqN__geqN_rel: f_rel_funct_db.

Theorem geqN__geqN_rel' (ds_d2AJ_u ds_d2AK_u : Nats_u) (ds_d2AJ ds_d2AK : Nats) (VV : bool):
  ds_d2AJ_u = ⌊ ds_d2AJ ⌋
  → (ds_d2AK_u = ⌊ ds_d2AK ⌋ → ⌊ geqN ds_d2AJ ds_d2AK -⌋ = VV ↔ geqN_rel ds_d2AJ_u ds_d2AK_u VV).
Proof.
  intros -> ->. refine (geqN__geqN_rel ds_d2AJ ds_d2AK VV).
Qed.

#[global] Hint Resolve geqN__geqN_rel': f_rel_funct_db.

Theorem geqN_rel_mk
  (ds_d2AJ : Nats_u)
  (ds_d2AJ_p : Nats_wf ds_d2AJ ∧ True)
  (ds_d2AK : Nats_u)
  (ds_d2AK_p : Nats_wf ds_d2AK ∧ True):
  {VV: _ | geqN_rel ds_d2AJ ds_d2AK VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, geqN_rel ds_d2AJ ds_d2AK VV)
          (geqN (exist _ ds_d2AJ ds_d2AJ_p) (exist _ ds_d2AK ds_d2AK_p))
          _);
  rewrite <- geqN__geqN_rel';
  quicksolve.
Qed.

#[global] Hint Resolve geqN_rel_mk: f_rel_funct_db.

#[global] Instance geqN_pack:
  @Pack
  (Nats ::RT λ (ds_d2AJ : Nats), Nats ::RT λ (ds_d2AK : Nats), nilRT)
  (Nats_u ::UT (Nats_u ::UT nilUT))
  ltac:(mkProjectsArgListTG (Nats ::RT λ (ds_d2AJ : Nats), Nats ::RT λ (ds_d2AK : Nats), nilRT) ((Nats_u ::UT (Nats_u ::UT nilUT))))
  bool
  (λ (x_83393932 : ArgList (Nats ::RT λ (ds_d2AJ : Nats), Nats ::RT λ (ds_d2AK : Nats), nilRT))
     (v_x_83393932 : bool),
   ltac:(flattenP (λ (ds_d2AJ ds_d2AK : Nats) (VV : bool), True) x_83393932 v_x_83393932)).
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

Definition App2_lem (VV : Pair) (VV_ : L2): L2_wf (App2_u ⌊ VV -⌋ ⌊ VV_ -⌋) ∧ True.
Proof.
  repeat first [split | solver].
Defined.

Definition App2 (VV : Pair) (VV_ : L2): L2 :=
  exist _ (App2_u ⌊ VV -⌋ ⌊ VV_ -⌋) (App2_lem VV VV_).

Definition Emp2_lem : L2_wf Emp2_u ∧ True.
Proof.
  repeat first [split | solver].
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

Definition length2_spec (ds_d2Bp : L2): Type :=
  Nats.

#[global] Hint Unfold length2_spec: lia_unfold.

Definition length2 (ds_d2Bp : L2): length2_spec ds_d2Bp.
Proof.
  destruct ds_d2Bp as [ds_d2Bp ds_d2Bp_p].
  induction ds_d2Bp as [ds_d2Br xs IH_xs|].
  - refine (Suc (IH_xs ltac:(try clear IH_xs; solver))).
  - refine Zero.
Defined.

Inductive length2_rel: L2_u → Nats_u → Prop :=
  | length2_App2: ∀ ds_d2Br xs (length2_res : Nats_u),
                  length2_rel xs length2_res → length2_rel (App2_u ds_d2Br xs) (Suc_u length2_res)
  | length2_Emp2: length2_rel Emp2_u Zero_u.

#[global] Hint Constructors length2_rel: core_hint_db.

#[global] Instance length2_lookup_rel: dictionary rel length2 := { lookup' := length2_rel }.

#[global] Instance length2_getF: getFunc length2_rel := { getF' := length2 }.

Theorem length2_rel_funct [ds_d2Bp : L2_u]:
  ∀ (VV VV' : Nats_u), length2_rel ds_d2Bp VV → (length2_rel ds_d2Bp VV' → VV = VV').
Proof.
  induction ds_d2Bp as [ds_d2Br xs IH_xs|]; rel_functionhood_body.
Qed.

#[global] Hint Resolve length2_rel_funct: f_rel_funct_db.

#[global] Instance length2_lookup_funct: dictionary functionhood length2 := {
    lookup' := length2_rel_funct }.

Theorem length2_App2_lem ds_d2Br xs length2_App2_lem_res:
  length2_rel (App2_u ds_d2Br xs) length2_App2_lem_res
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

Theorem length2_rel_ex (ds_d2Bp : L2_u) (ds_d2Bp_p : L2_wf ds_d2Bp ∧ True):
  length2_rel ds_d2Bp ⌊ length2 (exist _ ds_d2Bp ds_d2Bp_p) -⌋.
Proof.
  Opaque length2.
  existence_lemma_pre length2;
  induction ds_d2Bp as [ds_d2Br xs IH_xs|];
  [fix_notations; pose proof (IH_xs ltac:(try clear IH_xs; solver)) as IH_67415571; try clear IH_xs |
   fix_notations];
  simpl in *.
  Transparent length2.
  all: (existence_lemma_quicksolve length2; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve length2_rel_ex: rel_ax_db.

#[global] Opaque length2.

Theorem length2__length2_rel_rw (ds_d2Bp : L2_u) (ds_d2Bp_p : L2_wf ds_d2Bp ∧ True) (VV : Nats_u):
  ⌊ length2 (exist _ ds_d2Bp ds_d2Bp_p) -⌋ = VV ↔ length2_rel ds_d2Bp VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite length2__length2_rel_rw: f_rel_funct_db.

#[global] Hint Resolve length2__length2_rel_rw: rel_ax_db.

#[global] Instance length2_lookup_rw: dictionary rwLem length2 := {
    lookup' := length2__length2_rel_rw }.

Theorem length2__length2_rel (ds_d2Bp : L2) (VV : Nats_u):
  ⌊ length2 ds_d2Bp -⌋ = VV ↔ length2_rel ⌊ ds_d2Bp ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite length2__length2_rel: f_rel_funct_db.

Theorem length2__length2_rel' (ds_d2Bp_u : L2_u) (ds_d2Bp : L2) (VV : Nats_u):
  ds_d2Bp_u = ⌊ ds_d2Bp ⌋ → ⌊ length2 ds_d2Bp -⌋ = VV ↔ length2_rel ds_d2Bp_u VV.
Proof.
  intros ->. refine (length2__length2_rel ds_d2Bp VV).
Qed.

#[global] Hint Resolve length2__length2_rel': f_rel_funct_db.

Theorem length2_rel_mk (ds_d2Bp : L2_u) (ds_d2Bp_p : L2_wf ds_d2Bp ∧ True):
  {VV: _ | length2_rel ds_d2Bp VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, length2_rel ds_d2Bp VV) (length2 (exist _ ds_d2Bp ds_d2Bp_p)) _);
  rewrite <- length2__length2_rel';
  quicksolve.
Qed.

#[global] Hint Resolve length2_rel_mk: f_rel_funct_db.

#[global] Instance length2_pack:
  @Pack
  (L2 ::RT λ (ds_d2Bp : L2), nilRT)
  (L2_u ::UT nilUT)
  ltac:(mkProjectsArgListTG (L2 ::RT λ (ds_d2Bp : L2), nilRT) ((L2_u ::UT nilUT)))
  Nats_u
  (λ (x_83568817 : ArgList (L2 ::RT λ (ds_d2Bp : L2), nilRT)) (v_x_83568817 : Nats_u),
   ltac:(flattenP (λ (ds_d2Bp : L2) (VV : Nats_u), Nats_wf VV ∧ True) x_83568817 v_x_83568817)).
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

Definition App_lem (VV : {VV: Z | True}) (VV_ : L): L_wf (App_u ⌊ VV -⌋ ⌊ VV_ -⌋) ∧ True.
Proof.
  repeat first [split | solver].
Defined.

Definition App (VV : {VV: Z | True}) (VV_ : L): L :=
  exist _ (App_u ⌊ VV -⌋ ⌊ VV_ -⌋) (App_lem VV VV_).

Definition Emp_lem : L_wf Emp_u ∧ True.
Proof.
  repeat first [split | solver].
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

Definition PairL_eq (x y : PairL_u): bool :=
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

Definition PairL_wf (x : PairL_u): Prop :=
  match x with | MkPairL_u VV VV_ => (L_wf VV ∧ True) ∧ (L_wf VV_ ∧ True) end.

Theorem PairL_wf_ref [p : PairL_u → Prop] (tm : {v: PairL_u | PairL_wf v ∧ p v}): PairL_wf ⌊ tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation PairL := {x: PairL_u | PairL_wf x ∧ True}.

Definition MkPairL_lem (VV VV_ : L): PairL_wf (MkPairL_u ⌊ VV -⌋ ⌊ VV_ -⌋) ∧ True.
Proof.
  repeat first [split | solver].
Defined.

Definition MkPairL (VV VV_ : L): PairL :=
  exist _ (MkPairL_u ⌊ VV -⌋ ⌊ VV_ -⌋) (MkPairL_lem VV VV_).

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

Definition unzip_spec (ds_d2Bv : L2): Type :=
  PairL.

#[global] Hint Unfold unzip_spec: lia_unfold.

Definition unzip (ds_d2Bv : L2): unzip_spec ds_d2Bv.
Proof.
  destruct ds_d2Bv as [ds_d2Bv ds_d2Bv_p].
  induction ds_d2Bv as [ds_d2BF l IH_l|].
  - destruct ds_d2BF as [x y].
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
  (p : {{App_u ⌊ x -⌋ ⌊ xs -⌋ == App_u ⌊ y -⌋ ⌊ ys -⌋}}):
  Type :=
  {{⌊ x -⌋ == ⌊ y -⌋ ∧ ⌊ xs -⌋ == ⌊ ys -⌋}}.

#[global] Hint Unfold app_inj_spec: lia_unfold.

Theorem app_inj
  (x : {x: Z | True})
  (y : {y: Z | True})
  (xs ys : L)
  (p : {{App_u ⌊ x -⌋ ⌊ xs -⌋ == App_u ⌊ y -⌋ ⌊ ys -⌋}}):
  app_inj_spec x y xs ys p.
Proof.
  destruct x as [x x_p].
  destruct y as [y y_p].
  destruct xs as [xs xs_p].
  destruct ys as [ys ys_p].
  destruct p as [p p_p].
  refine (subsumptionCast Unit (λ (VV : Unit), x == y ∧ xs == ys) (# unit) ltac:(solver)).
Qed.

Definition append_spec (ds_d2Cq ys : L): Type :=
  L.

#[global] Hint Unfold append_spec: lia_unfold.

Definition append (ds_d2Cq ys : L): append_spec ds_d2Cq ys.
Proof.
  destruct ds_d2Cq as [ds_d2Cq ds_d2Cq_p].
  destruct ys as [ys ys_p].
  try revert ys_p; generalize dependent ys; induction ds_d2Cq as [x xs IH_xs|]; intros.
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

Theorem append_rel_funct [ds_d2Cq ys : L_u]:
  ∀ (VV VV' : L_u), append_rel ds_d2Cq ys VV → (append_rel ds_d2Cq ys VV' → VV = VV').
Proof.
  try revert ys_p; generalize dependent ys; induction ds_d2Cq as [x xs IH_xs|]; intros;
  rel_functionhood_body.
Qed.

#[global] Hint Resolve append_rel_funct: f_rel_funct_db.

#[global] Instance append_lookup_funct: dictionary functionhood append := {
    lookup' := append_rel_funct }.

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
  (ds_d2Cq : L_u) (ds_d2Cq_p : L_wf ds_d2Cq ∧ True) (ys : L_u) (ys_p : L_wf ys ∧ True):
  append_rel ds_d2Cq ys ⌊ append (exist _ ds_d2Cq ds_d2Cq_p) (exist _ ys ys_p) -⌋.
Proof.
  Opaque append.
  existence_lemma_pre append;
  try revert ys_p; generalize dependent ys; induction ds_d2Cq as [x xs IH_xs|]; intros;
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
  (ds_d2Cq : L_u) (ds_d2Cq_p : L_wf ds_d2Cq ∧ True) (ys : L_u) (ys_p : L_wf ys ∧ True) (VV : L_u):
  ⌊ append (exist _ ds_d2Cq ds_d2Cq_p) (exist _ ys ys_p) -⌋ = VV ↔ append_rel ds_d2Cq ys VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite append__append_rel_rw: f_rel_funct_db.

#[global] Hint Resolve append__append_rel_rw: rel_ax_db.

#[global] Instance append_lookup_rw: dictionary rwLem append := {
    lookup' := append__append_rel_rw }.

Theorem append__append_rel (ds_d2Cq ys : L) (VV : L_u):
  ⌊ append ds_d2Cq ys -⌋ = VV ↔ append_rel ⌊ ds_d2Cq ⌋ ⌊ ys ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite append__append_rel: f_rel_funct_db.

Theorem append__append_rel' (ds_d2Cq_u ys_u : L_u) (ds_d2Cq ys : L) (VV : L_u):
  ds_d2Cq_u = ⌊ ds_d2Cq ⌋
  → (ys_u = ⌊ ys ⌋ → ⌊ append ds_d2Cq ys -⌋ = VV ↔ append_rel ds_d2Cq_u ys_u VV).
Proof.
  intros -> ->. refine (append__append_rel ds_d2Cq ys VV).
Qed.

#[global] Hint Resolve append__append_rel': f_rel_funct_db.

Theorem append_rel_mk
  (ds_d2Cq : L_u) (ds_d2Cq_p : L_wf ds_d2Cq ∧ True) (ys : L_u) (ys_p : L_wf ys ∧ True):
  {VV: _ | append_rel ds_d2Cq ys VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, append_rel ds_d2Cq ys VV)
          (append (exist _ ds_d2Cq ds_d2Cq_p) (exist _ ys ys_p))
          _);
  rewrite <- append__append_rel';
  quicksolve.
Qed.

#[global] Hint Resolve append_rel_mk: f_rel_funct_db.

#[global] Instance append_pack:
  @Pack
  (L ::RT λ (ds_d2Cq : L), L ::RT λ (ys : L), nilRT)
  (L_u ::UT (L_u ::UT nilUT))
  ltac:(mkProjectsArgListTG (L ::RT λ (ds_d2Cq : L), L ::RT λ (ys : L), nilRT) ((L_u ::UT (L_u ::UT nilUT))))
  L_u
  (λ (x_20196586 : ArgList (L ::RT λ (ds_d2Cq : L), L ::RT λ (ys : L), nilRT)) (v_x_20196586 : L_u),
   ltac:(flattenP (λ (ds_d2Cq ys : L) (VV : L_u), L_wf VV ∧ True) x_20196586 v_x_20196586)).
Proof.
  buildPackG append append_rel append__append_rel append_rel_funct.
Defined.

#[global] Instance append_upack: @uPack (L_u ::UT (L_u ::UT nilUT)) L_u.
Proof.
  buildUPackG append_rel append_rel_funct.
Defined.

Definition append_nonempty_xs_spec
  (ds_d2C9 ds_d2Ca : L)
  (ds_d2Cb : {{∃ (append_res : L_u),
               append_rel ⌊ ds_d2C9 -⌋ ⌊ ds_d2Ca -⌋ append_res ∧ append_res == Emp_u}}):
  Type :=
  {{⌊ ds_d2C9 -⌋ == Emp_u}}.

#[global] Hint Unfold append_nonempty_xs_spec: lia_unfold.

Theorem append_nonempty_xs
  (ds_d2C9 ds_d2Ca : L)
  (ds_d2Cb : {{∃ (append_res : L_u),
               append_rel ⌊ ds_d2C9 -⌋ ⌊ ds_d2Ca -⌋ append_res ∧ append_res == Emp_u}}):
  append_nonempty_xs_spec ds_d2C9 ds_d2Ca ds_d2Cb.
Proof.
  destruct ds_d2C9 as [ds_d2C9 ds_d2C9_p].
  destruct ds_d2Ca as [ds_d2Ca ds_d2Ca_p].
  destruct ds_d2Cb as [ds_d2Cb ds_d2Cb_p].
  destruct ds_d2C9 as [lq_anf7205759403792803818 lq_anf7205759403792803819|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), App_u lq_anf7205759403792803818 lq_anf7205759403792803819 == Emp_u)
            (exist (λ (ds_d2Cb : Unit),
                    ∃ (append_res : L_u),
                    append_rel (App_u lq_anf7205759403792803818 lq_anf7205759403792803819) ds_d2Ca append_res
                    ∧ append_res == Emp_u) ds_d2Cb ltac:(solver))
            ltac:(solver)).
  - destruct ds_d2Ca as [lq_anf7205759403792803816 lq_anf7205759403792803817|].
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit), Emp_u == Emp_u)
              (exist (λ (ds_d2Cb : Unit),
                      ∃ (append_res : L_u),
                      append_rel Emp_u (App_u lq_anf7205759403792803816 lq_anf7205759403792803817) append_res
                      ∧ append_res == Emp_u) ds_d2Cb ltac:(solver))
              ltac:(solver)).
    + refine (subsumptionCast Unit (λ (VV : Unit), Emp_u == Emp_u) (# unit) ltac:(solver)).
Qed.

Definition append_nonempty_ys_spec
  (ds_d2Cg ds_d2Ch : L)
  (ds_d2Ci : {{∃ (append_res : L_u),
               append_rel ⌊ ds_d2Cg -⌋ ⌊ ds_d2Ch -⌋ append_res ∧ append_res == Emp_u}}):
  Type :=
  {{⌊ ds_d2Ch -⌋ == Emp_u}}.

#[global] Hint Unfold append_nonempty_ys_spec: lia_unfold.

Theorem append_nonempty_ys
  (ds_d2Cg ds_d2Ch : L)
  (ds_d2Ci : {{∃ (append_res : L_u),
               append_rel ⌊ ds_d2Cg -⌋ ⌊ ds_d2Ch -⌋ append_res ∧ append_res == Emp_u}}):
  append_nonempty_ys_spec ds_d2Cg ds_d2Ch ds_d2Ci.
Proof.
  destruct ds_d2Cg as [ds_d2Cg ds_d2Cg_p].
  destruct ds_d2Ch as [ds_d2Ch ds_d2Ch_p].
  destruct ds_d2Ci as [ds_d2Ci ds_d2Ci_p].
  destruct ds_d2Cg as [lq_anf7205759403792803809 lq_anf7205759403792803810|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ds_d2Ch == Emp_u)
            (exist (λ (ds_d2Ci : Unit),
                    ∃ (append_res : L_u),
                    append_rel (App_u lq_anf7205759403792803809 lq_anf7205759403792803810) ds_d2Ch append_res
                    ∧ append_res == Emp_u) ds_d2Ci ltac:(solver))
            ltac:(solver)).
  - destruct ds_d2Ch as [lq_anf7205759403792803807 lq_anf7205759403792803808|].
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit), App_u lq_anf7205759403792803807 lq_anf7205759403792803808 == Emp_u)
              (exist (λ (ds_d2Ci : Unit),
                      ∃ (append_res : L_u),
                      append_rel Emp_u (App_u lq_anf7205759403792803807 lq_anf7205759403792803808) append_res
                      ∧ append_res == Emp_u) ds_d2Ci ltac:(solver))
              ltac:(solver)).
    + refine (subsumptionCast Unit (λ (VV : Unit), Emp_u == Emp_u) (# unit) ltac:(solver)).
Qed.

Definition concatMap_spec
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT nilUT)))
       L_u
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : L_u),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : L_u), L_wf VV ∧ True) x_40877513 v_x_40877513)))
  (ds_d2Ct : L):
  Type :=
  L.

#[global] Hint Unfold concatMap_spec: lia_unfold.

Definition concatMap
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT nilUT)))
       L_u
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : L_u),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : L_u), L_wf VV ∧ True) x_40877513 v_x_40877513)))
  (ds_d2Ct : L):
  concatMap_spec f ds_d2Ct.
Proof.
  destruct ds_d2Ct as [ds_d2Ct ds_d2Ct_p].
  try revert f_p; generalize dependent f; induction ds_d2Ct as [x xs IH_xs|]; intros.
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

Theorem concatMap_rel_funct [f : @uPack (Z ::UT nilUT) L_u] [ds_d2Ct : L_u]:
  ∀ (VV VV' : L_u), concatMap_rel f ds_d2Ct VV → (concatMap_rel f ds_d2Ct VV' → VV = VV').
Proof.
  try revert f_p; generalize dependent f; induction ds_d2Ct as [x xs IH_xs|]; intros;
  rel_functionhood_body.
Qed.

#[global] Hint Resolve concatMap_rel_funct: f_rel_funct_db.

#[global] Instance concatMap_lookup_funct: dictionary functionhood concatMap := {
    lookup' := concatMap_rel_funct }.

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
       ltac:(mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT) ((Z ::UT nilUT)))
       L_u
       (λ (x_86795196 : ArgList ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_86795196 : L_u),
        ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : L_u), L_wf VV ∧ True) x_86795196 v_x_86795196)))
  (ds_d2Ct : L_u)
  (ds_d2Ct_p : L_wf ds_d2Ct ∧ True):
  concatMap_rel ⌊ f ⌋ ds_d2Ct ⌊ concatMap f (exist _ ds_d2Ct ds_d2Ct_p) -⌋.
Proof.
  Opaque concatMap.
  existence_lemma_pre concatMap;
  try revert f_p; generalize dependent f; induction ds_d2Ct as [x xs IH_xs|]; intros;
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
       ltac:(mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT) ((Z ::UT nilUT)))
       L_u
       (λ (x_86795196 : ArgList ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_86795196 : L_u),
        ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : L_u), L_wf VV ∧ True) x_86795196 v_x_86795196)))
  (ds_d2Ct : L_u)
  (ds_d2Ct_p : L_wf ds_d2Ct ∧ True)
  (VV : L_u):
  ⌊ concatMap f (exist _ ds_d2Ct ds_d2Ct_p) -⌋ = VV ↔ concatMap_rel ⌊ f ⌋ ds_d2Ct VV.
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
       ltac:(mkProjectsArgListTG ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT nilUT)))
       L_u
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : L_u),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : L_u), L_wf VV ∧ True) x_40877513 v_x_40877513)))
  (ds_d2Ct : L)
  (VV : L_u):
  ⌊ concatMap f ds_d2Ct -⌋ = VV ↔ concatMap_rel ⌊ f ⌋ ⌊ ds_d2Ct ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite concatMap__concatMap_rel: f_rel_funct_db.

Theorem concatMap__concatMap_rel'
  (f_u : @uPack (Z ::UT nilUT) L_u)
  (ds_d2Ct_u : L_u)
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT nilUT)))
       L_u
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : L_u),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : L_u), L_wf VV ∧ True) x_40877513 v_x_40877513)))
  (ds_d2Ct : L)
  (VV : L_u):
  f_u = ⌊ f ⌋
  → (ds_d2Ct_u = ⌊ ds_d2Ct ⌋ → ⌊ concatMap f ds_d2Ct -⌋ = VV ↔ concatMap_rel f_u ds_d2Ct_u VV).
Proof.
  intros -> ->. refine (concatMap__concatMap_rel f ds_d2Ct VV).
Qed.

#[global] Hint Resolve concatMap__concatMap_rel': f_rel_funct_db.

Theorem concatMap_rel_mk
  (f : @Pack
       ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT) ((Z ::UT nilUT)))
       L_u
       (λ (x_86795196 : ArgList ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_86795196 : L_u),
        ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : L_u), L_wf VV ∧ True) x_86795196 v_x_86795196)))
  (ds_d2Ct : L_u)
  (ds_d2Ct_p : L_wf ds_d2Ct ∧ True):
  {VV: _ | concatMap_rel (packProj f) ds_d2Ct VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, concatMap_rel (packProj f) ds_d2Ct VV)
          (concatMap f (exist _ ds_d2Ct ds_d2Ct_p))
          _);
  rewrite <- concatMap__concatMap_rel';
  quicksolve.
Qed.

#[global] Hint Resolve concatMap_rel_mk: f_rel_funct_db.

Definition l2_pr1_spec (ds_d2B9 : L2): Type :=
  L.

#[global] Hint Unfold l2_pr1_spec: lia_unfold.

Definition l2_pr1 (ds_d2B9 : L2): l2_pr1_spec ds_d2B9.
Proof.
  destruct ds_d2B9 as [ds_d2B9 ds_d2B9_p].
  induction ds_d2B9 as [ds_d2Bc l IH_l|].
  - destruct ds_d2Bc as [x ds_d2Bd].
    + refine (App (# x) (IH_l ltac:(try clear IH_l; solver))).
  - refine Emp.
Defined.

Inductive l2_pr1_rel: L2_u → L_u → Prop :=
  | l2_pr1__App2_MkPair_x: ∀ ds_d2Bd l x (l2_pr1_res : L_u),
                           l2_pr1_rel l l2_pr1_res → l2_pr1_rel (App2_u (MkPair_u x ds_d2Bd) l) (App_u x l2_pr1_res)
  | l2_pr1_Emp2: l2_pr1_rel Emp2_u Emp_u.

#[global] Hint Constructors l2_pr1_rel: core_hint_db.

#[global] Instance l2_pr1_lookup_rel: dictionary rel l2_pr1 := { lookup' := l2_pr1_rel }.

#[global] Instance l2_pr1_getF: getFunc l2_pr1_rel := { getF' := l2_pr1 }.

Theorem l2_pr1_rel_funct [ds_d2B9 : L2_u]:
  ∀ (VV VV' : L_u), l2_pr1_rel ds_d2B9 VV → (l2_pr1_rel ds_d2B9 VV' → VV = VV').
Proof.
  induction ds_d2B9 as [ds_d2Bc l IH_l|];
  [destruct ds_d2Bc as [x ds_d2Bd] |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve l2_pr1_rel_funct: f_rel_funct_db.

#[global] Instance l2_pr1_lookup_funct: dictionary functionhood l2_pr1 := {
    lookup' := l2_pr1_rel_funct }.

Theorem l2_pr1__App2_MkPair_x_lem ds_d2Bd l x l2_pr1__App2_MkPair_x_lem_res:
  l2_pr1_rel (App2_u (MkPair_u x ds_d2Bd) l) l2_pr1__App2_MkPair_x_lem_res
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

Theorem l2_pr1_rel_ex (ds_d2B9 : L2_u) (ds_d2B9_p : L2_wf ds_d2B9 ∧ True):
  l2_pr1_rel ds_d2B9 ⌊ l2_pr1 (exist _ ds_d2B9 ds_d2B9_p) -⌋.
Proof.
  Opaque l2_pr1.
  existence_lemma_pre l2_pr1;
  induction ds_d2B9 as [ds_d2Bc l IH_l|];
  [destruct ds_d2Bc as [x ds_d2Bd];
   [fix_notations; pose proof (IH_l ltac:(try clear IH_l; solver)) as IH_26190279; try clear IH_l] |
   fix_notations];
  simpl in *.
  Transparent l2_pr1.
  all: (existence_lemma_quicksolve l2_pr1; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve l2_pr1_rel_ex: rel_ax_db.

#[global] Opaque l2_pr1.

Theorem l2_pr1__l2_pr1_rel_rw (ds_d2B9 : L2_u) (ds_d2B9_p : L2_wf ds_d2B9 ∧ True) (VV : L_u):
  ⌊ l2_pr1 (exist _ ds_d2B9 ds_d2B9_p) -⌋ = VV ↔ l2_pr1_rel ds_d2B9 VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite l2_pr1__l2_pr1_rel_rw: f_rel_funct_db.

#[global] Hint Resolve l2_pr1__l2_pr1_rel_rw: rel_ax_db.

#[global] Instance l2_pr1_lookup_rw: dictionary rwLem l2_pr1 := {
    lookup' := l2_pr1__l2_pr1_rel_rw }.

Theorem l2_pr1__l2_pr1_rel (ds_d2B9 : L2) (VV : L_u):
  ⌊ l2_pr1 ds_d2B9 -⌋ = VV ↔ l2_pr1_rel ⌊ ds_d2B9 ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite l2_pr1__l2_pr1_rel: f_rel_funct_db.

Theorem l2_pr1__l2_pr1_rel' (ds_d2B9_u : L2_u) (ds_d2B9 : L2) (VV : L_u):
  ds_d2B9_u = ⌊ ds_d2B9 ⌋ → ⌊ l2_pr1 ds_d2B9 -⌋ = VV ↔ l2_pr1_rel ds_d2B9_u VV.
Proof.
  intros ->. refine (l2_pr1__l2_pr1_rel ds_d2B9 VV).
Qed.

#[global] Hint Resolve l2_pr1__l2_pr1_rel': f_rel_funct_db.

Theorem l2_pr1_rel_mk (ds_d2B9 : L2_u) (ds_d2B9_p : L2_wf ds_d2B9 ∧ True):
  {VV: _ | l2_pr1_rel ds_d2B9 VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, l2_pr1_rel ds_d2B9 VV) (l2_pr1 (exist _ ds_d2B9 ds_d2B9_p)) _);
  rewrite <- l2_pr1__l2_pr1_rel';
  quicksolve.
Qed.

#[global] Hint Resolve l2_pr1_rel_mk: f_rel_funct_db.

#[global] Instance l2_pr1_pack:
  @Pack
  (L2 ::RT λ (ds_d2B9 : L2), nilRT)
  (L2_u ::UT nilUT)
  ltac:(mkProjectsArgListTG (L2 ::RT λ (ds_d2B9 : L2), nilRT) ((L2_u ::UT nilUT)))
  L_u
  (λ (x_90986817 : ArgList (L2 ::RT λ (ds_d2B9 : L2), nilRT)) (v_x_90986817 : L_u),
   ltac:(flattenP (λ (ds_d2B9 : L2) (VV : L_u), L_wf VV ∧ True) x_90986817 v_x_90986817)).
Proof.
  buildPackG l2_pr1 l2_pr1_rel l2_pr1__l2_pr1_rel l2_pr1_rel_funct.
Defined.

#[global] Instance l2_pr1_upack: @uPack (L2_u ::UT nilUT) L_u.
Proof.
  buildUPackG l2_pr1_rel l2_pr1_rel_funct.
Defined.

Definition l2_pr2_spec (ds_d2B4 : L2): Type :=
  L.

#[global] Hint Unfold l2_pr2_spec: lia_unfold.

Definition l2_pr2 (ds_d2B4 : L2): l2_pr2_spec ds_d2B4.
Proof.
  destruct ds_d2B4 as [ds_d2B4 ds_d2B4_p].
  induction ds_d2B4 as [ds_d2B7 l IH_l|].
  - destruct ds_d2B7 as [ds_d2B8 y].
    + refine (App (# y) (IH_l ltac:(try clear IH_l; solver))).
  - refine Emp.
Defined.

Inductive l2_pr2_rel: L2_u → L_u → Prop :=
  | l2_pr2__App2_MkPair_x: ∀ ds_d2B8 l y (l2_pr2_res : L_u),
                           l2_pr2_rel l l2_pr2_res → l2_pr2_rel (App2_u (MkPair_u ds_d2B8 y) l) (App_u y l2_pr2_res)
  | l2_pr2_Emp2: l2_pr2_rel Emp2_u Emp_u.

#[global] Hint Constructors l2_pr2_rel: core_hint_db.

#[global] Instance l2_pr2_lookup_rel: dictionary rel l2_pr2 := { lookup' := l2_pr2_rel }.

#[global] Instance l2_pr2_getF: getFunc l2_pr2_rel := { getF' := l2_pr2 }.

Theorem l2_pr2_rel_funct [ds_d2B4 : L2_u]:
  ∀ (VV VV' : L_u), l2_pr2_rel ds_d2B4 VV → (l2_pr2_rel ds_d2B4 VV' → VV = VV').
Proof.
  induction ds_d2B4 as [ds_d2B7 l IH_l|];
  [destruct ds_d2B7 as [ds_d2B8 y] |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve l2_pr2_rel_funct: f_rel_funct_db.

#[global] Instance l2_pr2_lookup_funct: dictionary functionhood l2_pr2 := {
    lookup' := l2_pr2_rel_funct }.

Theorem l2_pr2__App2_MkPair_x_lem ds_d2B8 l y l2_pr2__App2_MkPair_x_lem_res:
  l2_pr2_rel (App2_u (MkPair_u ds_d2B8 y) l) l2_pr2__App2_MkPair_x_lem_res
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

Theorem l2_pr2_rel_ex (ds_d2B4 : L2_u) (ds_d2B4_p : L2_wf ds_d2B4 ∧ True):
  l2_pr2_rel ds_d2B4 ⌊ l2_pr2 (exist _ ds_d2B4 ds_d2B4_p) -⌋.
Proof.
  Opaque l2_pr2.
  existence_lemma_pre l2_pr2;
  induction ds_d2B4 as [ds_d2B7 l IH_l|];
  [destruct ds_d2B7 as [ds_d2B8 y];
   [fix_notations; pose proof (IH_l ltac:(try clear IH_l; solver)) as IH_26190279; try clear IH_l] |
   fix_notations];
  simpl in *.
  Transparent l2_pr2.
  all: (existence_lemma_quicksolve l2_pr2; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve l2_pr2_rel_ex: rel_ax_db.

#[global] Opaque l2_pr2.

Theorem l2_pr2__l2_pr2_rel_rw (ds_d2B4 : L2_u) (ds_d2B4_p : L2_wf ds_d2B4 ∧ True) (VV : L_u):
  ⌊ l2_pr2 (exist _ ds_d2B4 ds_d2B4_p) -⌋ = VV ↔ l2_pr2_rel ds_d2B4 VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite l2_pr2__l2_pr2_rel_rw: f_rel_funct_db.

#[global] Hint Resolve l2_pr2__l2_pr2_rel_rw: rel_ax_db.

#[global] Instance l2_pr2_lookup_rw: dictionary rwLem l2_pr2 := {
    lookup' := l2_pr2__l2_pr2_rel_rw }.

Theorem l2_pr2__l2_pr2_rel (ds_d2B4 : L2) (VV : L_u):
  ⌊ l2_pr2 ds_d2B4 -⌋ = VV ↔ l2_pr2_rel ⌊ ds_d2B4 ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite l2_pr2__l2_pr2_rel: f_rel_funct_db.

Theorem l2_pr2__l2_pr2_rel' (ds_d2B4_u : L2_u) (ds_d2B4 : L2) (VV : L_u):
  ds_d2B4_u = ⌊ ds_d2B4 ⌋ → ⌊ l2_pr2 ds_d2B4 -⌋ = VV ↔ l2_pr2_rel ds_d2B4_u VV.
Proof.
  intros ->. refine (l2_pr2__l2_pr2_rel ds_d2B4 VV).
Qed.

#[global] Hint Resolve l2_pr2__l2_pr2_rel': f_rel_funct_db.

Theorem l2_pr2_rel_mk (ds_d2B4 : L2_u) (ds_d2B4_p : L2_wf ds_d2B4 ∧ True):
  {VV: _ | l2_pr2_rel ds_d2B4 VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, l2_pr2_rel ds_d2B4 VV) (l2_pr2 (exist _ ds_d2B4 ds_d2B4_p)) _);
  rewrite <- l2_pr2__l2_pr2_rel';
  quicksolve.
Qed.

#[global] Hint Resolve l2_pr2_rel_mk: f_rel_funct_db.

#[global] Instance l2_pr2_pack:
  @Pack
  (L2 ::RT λ (ds_d2B4 : L2), nilRT)
  (L2_u ::UT nilUT)
  ltac:(mkProjectsArgListTG (L2 ::RT λ (ds_d2B4 : L2), nilRT) ((L2_u ::UT nilUT)))
  L_u
  (λ (x_39828685 : ArgList (L2 ::RT λ (ds_d2B4 : L2), nilRT)) (v_x_39828685 : L_u),
   ltac:(flattenP (λ (ds_d2B4 : L2) (VV : L_u), L_wf VV ∧ True) x_39828685 v_x_39828685)).
Proof.
  buildPackG l2_pr2 l2_pr2_rel l2_pr2__l2_pr2_rel l2_pr2_rel_funct.
Defined.

#[global] Instance l2_pr2_upack: @uPack (L2_u ::UT nilUT) L_u.
Proof.
  buildUPackG l2_pr2_rel l2_pr2_rel_funct.
Defined.

Definition length_spec (ds_d2Bs : L): Type :=
  Nats.

#[global] Hint Unfold length_spec: lia_unfold.

Definition length (ds_d2Bs : L): length_spec ds_d2Bs.
Proof.
  destruct ds_d2Bs as [ds_d2Bs ds_d2Bs_p].
  induction ds_d2Bs as [ds_d2Bu xs IH_xs|].
  - refine (Suc (IH_xs ltac:(try clear IH_xs; solver))).
  - refine Zero.
Defined.

Inductive length_rel: L_u → Nats_u → Prop :=
  | length_App: ∀ ds_d2Bu xs (length_res : Nats_u),
                length_rel xs length_res → length_rel (App_u ds_d2Bu xs) (Suc_u length_res)
  | length_Emp: length_rel Emp_u Zero_u.

#[global] Hint Constructors length_rel: core_hint_db.

#[global] Instance length_lookup_rel: dictionary rel length := { lookup' := length_rel }.

#[global] Instance length_getF: getFunc length_rel := { getF' := length }.

Theorem length_rel_funct [ds_d2Bs : L_u]:
  ∀ (VV VV' : Nats_u), length_rel ds_d2Bs VV → (length_rel ds_d2Bs VV' → VV = VV').
Proof.
  induction ds_d2Bs as [ds_d2Bu xs IH_xs|]; rel_functionhood_body.
Qed.

#[global] Hint Resolve length_rel_funct: f_rel_funct_db.

#[global] Instance length_lookup_funct: dictionary functionhood length := {
    lookup' := length_rel_funct }.

Theorem length_App_lem ds_d2Bu xs length_App_lem_res:
  length_rel (App_u ds_d2Bu xs) length_App_lem_res
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

Theorem length_rel_ex (ds_d2Bs : L_u) (ds_d2Bs_p : L_wf ds_d2Bs ∧ True):
  length_rel ds_d2Bs ⌊ length (exist _ ds_d2Bs ds_d2Bs_p) -⌋.
Proof.
  Opaque length.
  existence_lemma_pre length;
  induction ds_d2Bs as [ds_d2Bu xs IH_xs|];
  [fix_notations; pose proof (IH_xs ltac:(try clear IH_xs; solver)) as IH_67415571; try clear IH_xs |
   fix_notations];
  simpl in *.
  Transparent length.
  all: (existence_lemma_quicksolve length; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve length_rel_ex: rel_ax_db.

#[global] Opaque length.

Theorem length__length_rel_rw (ds_d2Bs : L_u) (ds_d2Bs_p : L_wf ds_d2Bs ∧ True) (VV : Nats_u):
  ⌊ length (exist _ ds_d2Bs ds_d2Bs_p) -⌋ = VV ↔ length_rel ds_d2Bs VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite length__length_rel_rw: f_rel_funct_db.

#[global] Hint Resolve length__length_rel_rw: rel_ax_db.

#[global] Instance length_lookup_rw: dictionary rwLem length := {
    lookup' := length__length_rel_rw }.

Theorem length__length_rel (ds_d2Bs : L) (VV : Nats_u):
  ⌊ length ds_d2Bs -⌋ = VV ↔ length_rel ⌊ ds_d2Bs ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite length__length_rel: f_rel_funct_db.

Theorem length__length_rel' (ds_d2Bs_u : L_u) (ds_d2Bs : L) (VV : Nats_u):
  ds_d2Bs_u = ⌊ ds_d2Bs ⌋ → ⌊ length ds_d2Bs -⌋ = VV ↔ length_rel ds_d2Bs_u VV.
Proof.
  intros ->. refine (length__length_rel ds_d2Bs VV).
Qed.

#[global] Hint Resolve length__length_rel': f_rel_funct_db.

Theorem length_rel_mk (ds_d2Bs : L_u) (ds_d2Bs_p : L_wf ds_d2Bs ∧ True):
  {VV: _ | length_rel ds_d2Bs VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, length_rel ds_d2Bs VV) (length (exist _ ds_d2Bs ds_d2Bs_p)) _);
  rewrite <- length__length_rel';
  quicksolve.
Qed.

#[global] Hint Resolve length_rel_mk: f_rel_funct_db.

#[global] Instance length_pack:
  @Pack
  (L ::RT λ (ds_d2Bs : L), nilRT)
  (L_u ::UT nilUT)
  ltac:(mkProjectsArgListTG (L ::RT λ (ds_d2Bs : L), nilRT) ((L_u ::UT nilUT)))
  Nats_u
  (λ (x_82827291 : ArgList (L ::RT λ (ds_d2Bs : L), nilRT)) (v_x_82827291 : Nats_u),
   ltac:(flattenP (λ (ds_d2Bs : L) (VV : Nats_u), Nats_wf VV ∧ True) x_82827291 v_x_82827291)).
Proof.
  buildPackG length length_rel length__length_rel length_rel_funct.
Defined.

#[global] Instance length_upack: @uPack (L_u ::UT nilUT) Nats_u.
Proof.
  buildUPackG length_rel length_rel_funct.
Defined.

Definition length_unzip_1_spec (ds_d2B2 : L2): Type :=
  {{∃ (length2_res : Nats_u),
    length2_rel ⌊ ds_d2B2 -⌋ length2_res
    ∧ ∃ (l2_pr1_res : L_u),
      l2_pr1_rel ⌊ ds_d2B2 -⌋ l2_pr1_res
      ∧ ∃ (length_res : Nats_u), length_rel l2_pr1_res length_res ∧ length2_res == length_res}}.

#[global] Hint Unfold length_unzip_1_spec: lia_unfold.

Theorem length_unzip_1 (ds_d2B2 : L2): length_unzip_1_spec ds_d2B2.
Proof.
  destruct ds_d2B2 as [ds_d2B2 ds_d2B2_p].
  induction ds_d2B2 as [ds_d2B3 l IH_l|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (length2_res : Nats_u),
             length2_rel (App2_u ds_d2B3 l) length2_res
             ∧ ∃ (l2_pr1_res : L_u),
               l2_pr1_rel (App2_u ds_d2B3 l) l2_pr1_res
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

Definition length_unzip_2_spec (ds_d2B0 : L2): Type :=
  {{∃ (length2_res : Nats_u),
    length2_rel ⌊ ds_d2B0 -⌋ length2_res
    ∧ ∃ (l2_pr2_res : L_u),
      l2_pr2_rel ⌊ ds_d2B0 -⌋ l2_pr2_res
      ∧ ∃ (length_res : Nats_u), length_rel l2_pr2_res length_res ∧ length2_res == length_res}}.

#[global] Hint Unfold length_unzip_2_spec: lia_unfold.

Theorem length_unzip_2 (ds_d2B0 : L2): length_unzip_2_spec ds_d2B0.
Proof.
  destruct ds_d2B0 as [ds_d2B0 ds_d2B0_p].
  induction ds_d2B0 as [ds_d2B1 l IH_l|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (length2_res : Nats_u),
             length2_rel (App2_u ds_d2B1 l) length2_res
             ∧ ∃ (l2_pr2_res : L_u),
               l2_pr2_rel (App2_u ds_d2B1 l) l2_pr2_res
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
       ltac:(mkProjectsArgListTG ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT nilUT)))
       Z
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513)))
  (ds_d2Cn : L):
  Type :=
  L.

#[global] Hint Unfold map_spec: lia_unfold.

Definition map
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT nilUT)))
       Z
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513)))
  (ds_d2Cn : L):
  map_spec f ds_d2Cn.
Proof.
  destruct ds_d2Cn as [ds_d2Cn ds_d2Cn_p].
  try revert f_p; generalize dependent f; induction ds_d2Cn as [x xs IH_xs|]; intros.
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

Theorem map_rel_funct [f : @uPack (Z ::UT nilUT) Z] [ds_d2Cn : L_u]:
  ∀ (VV VV' : L_u), map_rel f ds_d2Cn VV → (map_rel f ds_d2Cn VV' → VV = VV').
Proof.
  try revert f_p; generalize dependent f; induction ds_d2Cn as [x xs IH_xs|]; intros;
  rel_functionhood_body.
Qed.

#[global] Hint Resolve map_rel_funct: f_rel_funct_db.

#[global] Instance map_lookup_funct: dictionary functionhood map := { lookup' := map_rel_funct }.

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
       ltac:(mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT) ((Z ::UT nilUT)))
       Z
       (λ (x_86795196 : ArgList ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_86795196 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z), True) x_86795196 v_x_86795196)))
  (ds_d2Cn : L_u)
  (ds_d2Cn_p : L_wf ds_d2Cn ∧ True):
  map_rel ⌊ f ⌋ ds_d2Cn ⌊ map f (exist _ ds_d2Cn ds_d2Cn_p) -⌋.
Proof.
  Opaque map.
  existence_lemma_pre map;
  try revert f_p; generalize dependent f; induction ds_d2Cn as [x xs IH_xs|]; intros;
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
       ltac:(mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT) ((Z ::UT nilUT)))
       Z
       (λ (x_86795196 : ArgList ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_86795196 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z), True) x_86795196 v_x_86795196)))
  (ds_d2Cn : L_u)
  (ds_d2Cn_p : L_wf ds_d2Cn ∧ True)
  (VV : L_u):
  ⌊ map f (exist _ ds_d2Cn ds_d2Cn_p) -⌋ = VV ↔ map_rel ⌊ f ⌋ ds_d2Cn VV.
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
       ltac:(mkProjectsArgListTG ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT nilUT)))
       Z
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513)))
  (ds_d2Cn : L)
  (VV : L_u):
  ⌊ map f ds_d2Cn -⌋ = VV ↔ map_rel ⌊ f ⌋ ⌊ ds_d2Cn ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite map__map_rel: f_rel_funct_db.

Theorem map__map_rel'
  (f_u : @uPack (Z ::UT nilUT) Z)
  (ds_d2Cn_u : L_u)
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT nilUT)))
       Z
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513)))
  (ds_d2Cn : L)
  (VV : L_u):
  f_u = ⌊ f ⌋ → (ds_d2Cn_u = ⌊ ds_d2Cn ⌋ → ⌊ map f ds_d2Cn -⌋ = VV ↔ map_rel f_u ds_d2Cn_u VV).
Proof.
  intros -> ->. refine (map__map_rel f ds_d2Cn VV).
Qed.

#[global] Hint Resolve map__map_rel': f_rel_funct_db.

Theorem map_rel_mk
  (f : @Pack
       ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT) ((Z ::UT nilUT)))
       Z
       (λ (x_86795196 : ArgList ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_86795196 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z), True) x_86795196 v_x_86795196)))
  (ds_d2Cn : L_u)
  (ds_d2Cn_p : L_wf ds_d2Cn ∧ True):
  {VV: _ | map_rel (packProj f) ds_d2Cn VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, map_rel (packProj f) ds_d2Cn VV)
          (map f (exist _ ds_d2Cn ds_d2Cn_p))
          _);
  rewrite <- map__map_rel';
  quicksolve.
Qed.

#[global] Hint Resolve map_rel_mk: f_rel_funct_db.

Definition length_map_spec
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT) ((Z ::UT nilUT)))
       Z
       (λ (x_44453395 : ArgList ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT))
          (v_x_44453395 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {VV: Z | True}) (VV : Z), True) x_44453395 v_x_44453395)))
  (ds_d2Bo : L):
  Type :=
  {{∃ (map_res : L_u),
    map_rel ⌊ f ⌋ ⌊ ds_d2Bo -⌋ map_res
    ∧ ∃ (length_res : Nats_u),
      length_rel map_res length_res
      ∧ ∃ (length_res_2 : Nats_u), length_rel ⌊ ds_d2Bo -⌋ length_res_2 ∧ length_res == length_res_2}}.

#[global] Hint Unfold length_map_spec: lia_unfold.

Theorem length_map
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT) ((Z ::UT nilUT)))
       Z
       (λ (x_44453395 : ArgList ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT))
          (v_x_44453395 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {VV: Z | True}) (VV : Z), True) x_44453395 v_x_44453395)))
  (ds_d2Bo : L):
  length_map_spec f ds_d2Bo.
Proof.
  destruct ds_d2Bo as [ds_d2Bo ds_d2Bo_p].
  try revert f_p; generalize dependent f; induction ds_d2Bo as [x xs IH_xs|]; intros.
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

Definition reverse_spec (ds_d2Cu : L): Type :=
  L.

#[global] Hint Unfold reverse_spec: lia_unfold.

Definition reverse (ds_d2Cu : L): reverse_spec ds_d2Cu.
Proof.
  destruct ds_d2Cu as [ds_d2Cu ds_d2Cu_p].
  induction ds_d2Cu as [x xs IH_xs|].
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

Theorem reverse_rel_funct [ds_d2Cu : L_u]:
  ∀ (VV VV' : L_u), reverse_rel ds_d2Cu VV → (reverse_rel ds_d2Cu VV' → VV = VV').
Proof.
  induction ds_d2Cu as [x xs IH_xs|]; rel_functionhood_body.
Qed.

#[global] Hint Resolve reverse_rel_funct: f_rel_funct_db.

#[global] Instance reverse_lookup_funct: dictionary functionhood reverse := {
    lookup' := reverse_rel_funct }.

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

Theorem reverse_rel_ex (ds_d2Cu : L_u) (ds_d2Cu_p : L_wf ds_d2Cu ∧ True):
  reverse_rel ds_d2Cu ⌊ reverse (exist _ ds_d2Cu ds_d2Cu_p) -⌋.
Proof.
  Opaque reverse.
  existence_lemma_pre reverse;
  induction ds_d2Cu as [x xs IH_xs|];
  [fix_notations; pose proof (IH_xs ltac:(try clear IH_xs; solver)) as IH_67415571; try clear IH_xs |
   fix_notations];
  simpl in *.
  Transparent reverse.
  all: (existence_lemma_quicksolve reverse; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve reverse_rel_ex: rel_ax_db.

#[global] Opaque reverse.

Theorem reverse__reverse_rel_rw (ds_d2Cu : L_u) (ds_d2Cu_p : L_wf ds_d2Cu ∧ True) (VV : L_u):
  ⌊ reverse (exist _ ds_d2Cu ds_d2Cu_p) -⌋ = VV ↔ reverse_rel ds_d2Cu VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite reverse__reverse_rel_rw: f_rel_funct_db.

#[global] Hint Resolve reverse__reverse_rel_rw: rel_ax_db.

#[global] Instance reverse_lookup_rw: dictionary rwLem reverse := {
    lookup' := reverse__reverse_rel_rw }.

Theorem reverse__reverse_rel (ds_d2Cu : L) (VV : L_u):
  ⌊ reverse ds_d2Cu -⌋ = VV ↔ reverse_rel ⌊ ds_d2Cu ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite reverse__reverse_rel: f_rel_funct_db.

Theorem reverse__reverse_rel' (ds_d2Cu_u : L_u) (ds_d2Cu : L) (VV : L_u):
  ds_d2Cu_u = ⌊ ds_d2Cu ⌋ → ⌊ reverse ds_d2Cu -⌋ = VV ↔ reverse_rel ds_d2Cu_u VV.
Proof.
  intros ->. refine (reverse__reverse_rel ds_d2Cu VV).
Qed.

#[global] Hint Resolve reverse__reverse_rel': f_rel_funct_db.

Theorem reverse_rel_mk (ds_d2Cu : L_u) (ds_d2Cu_p : L_wf ds_d2Cu ∧ True):
  {VV: _ | reverse_rel ds_d2Cu VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, reverse_rel ds_d2Cu VV) (reverse (exist _ ds_d2Cu ds_d2Cu_p)) _);
  rewrite <- reverse__reverse_rel';
  quicksolve.
Qed.

#[global] Hint Resolve reverse_rel_mk: f_rel_funct_db.

#[global] Instance reverse_pack:
  @Pack
  (L ::RT λ (ds_d2Cu : L), nilRT)
  (L_u ::UT nilUT)
  ltac:(mkProjectsArgListTG (L ::RT λ (ds_d2Cu : L), nilRT) ((L_u ::UT nilUT)))
  L_u
  (λ (x_49125896 : ArgList (L ::RT λ (ds_d2Cu : L), nilRT)) (v_x_49125896 : L_u),
   ltac:(flattenP (λ (ds_d2Cu : L) (VV : L_u), L_wf VV ∧ True) x_49125896 v_x_49125896)).
Proof.
  buildPackG reverse reverse_rel reverse__reverse_rel reverse_rel_funct.
Defined.

#[global] Instance reverse_upack: @uPack (L_u ::UT nilUT) L_u.
Proof.
  buildUPackG reverse_rel reverse_rel_funct.
Defined.

Definition reverse_nonempty_spec
  (ds_d2Cx : L)
  (ds_d2Cy : {{∃ (reverse_res : L_u), reverse_rel ⌊ ds_d2Cx -⌋ reverse_res ∧ reverse_res == Emp_u}}):
  Type :=
  {{⌊ ds_d2Cx -⌋ == Emp_u}}.

#[global] Hint Unfold reverse_nonempty_spec: lia_unfold.

Theorem reverse_nonempty
  (ds_d2Cx : L)
  (ds_d2Cy : {{∃ (reverse_res : L_u), reverse_rel ⌊ ds_d2Cx -⌋ reverse_res ∧ reverse_res == Emp_u}}):
  reverse_nonempty_spec ds_d2Cx ds_d2Cy.
Proof.
  destruct ds_d2Cx as [ds_d2Cx ds_d2Cx_p].
  destruct ds_d2Cy as [ds_d2Cy ds_d2Cy_p].
  destruct ds_d2Cx as [x xs|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), App_u x xs == Emp_u)
            (append_nonempty_ys
             (reverse (exist (λ (VV : L_u), L_wf VV ∧ True) xs ltac:(solver)))
             (App (# x) Emp)
             (subsumptionCast
              Unit
              (λ (ds_d2Ci : Unit),
               ∃ (append_res : L_u),
               append_rel
               ⌊ reverse (exist (λ (VV : L_u), L_wf VV ∧ True) xs ltac:(solver)) -⌋
               (App_u x Emp_u)
               append_res
               ∧ append_res == Emp_u)
              (exist (λ (ds_d2Cy : Unit),
                      ∃ (reverse_res : L_u),
                      reverse_rel (App_u x xs) reverse_res ∧ reverse_res == Emp_u) ds_d2Cy ltac:(solver))
              ltac:(solver)))
            ltac:(solver)).
  - refine (subsumptionCast Unit (λ (VV : Unit), Emp_u == Emp_u) (# unit) ltac:(solver)).
Qed.

Definition take_spec (ds_d2AQ : Nats) (ds_d2AR : L): Type :=
  L.

#[global] Hint Unfold take_spec: lia_unfold.

Definition take (ds_d2AQ : Nats) (ds_d2AR : L): take_spec ds_d2AQ ds_d2AR.
Proof.
  destruct ds_d2AQ as [ds_d2AQ ds_d2AQ_p].
  destruct ds_d2AR as [ds_d2AR ds_d2AR_p].
  try revert ds_d2AR_p; generalize dependent ds_d2AR;
  induction ds_d2AQ as [lq_anf7205759403792803925 IH_lq_anf7205759403792803925|];
  intros.
  - destruct ds_d2AR as [lq_anf7205759403792803923 lq_anf7205759403792803924|].
    + refine (App
              (# lq_anf7205759403792803923)
              (IH_lq_anf7205759403792803925
               ltac:(try clear IH_lq_anf7205759403792803925; solver)
               lq_anf7205759403792803924
               ltac:(try clear IH_lq_anf7205759403792803925; solver))).
    + refine Emp.
  - refine Emp.
Defined.

Inductive take_rel: Nats_u → L_u → L_u → Prop :=
  | take_Suc_App: ∀ lq_anf7205759403792803925 lq_anf7205759403792803923 lq_anf7205759403792803924
                    (take_res : L_u),
                  take_rel lq_anf7205759403792803925 lq_anf7205759403792803924 take_res
                  → take_rel
                    (Suc_u lq_anf7205759403792803925)
                    (App_u lq_anf7205759403792803923 lq_anf7205759403792803924)
                    (App_u lq_anf7205759403792803923 take_res)
  | take_Suc_Emp: ∀ lq_anf7205759403792803925, take_rel (Suc_u lq_anf7205759403792803925) Emp_u Emp_u
  | take_Zero_x: ∀ ds_d2AR, take_rel Zero_u ds_d2AR Emp_u.

#[global] Hint Constructors take_rel: core_hint_db.

#[global] Instance take_lookup_rel: dictionary rel take := { lookup' := take_rel }.

#[global] Instance take_getF: getFunc take_rel := { getF' := take }.

Theorem take_rel_funct [ds_d2AQ : Nats_u] [ds_d2AR : L_u]:
  ∀ (VV VV' : L_u), take_rel ds_d2AQ ds_d2AR VV → (take_rel ds_d2AQ ds_d2AR VV' → VV = VV').
Proof.
  try revert ds_d2AR_p; generalize dependent ds_d2AR;
  induction ds_d2AQ as [lq_anf7205759403792803925 IH_lq_anf7205759403792803925|];
  intros;
  [destruct ds_d2AR as [lq_anf7205759403792803923 lq_anf7205759403792803924|] |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve take_rel_funct: f_rel_funct_db.

#[global] Instance take_lookup_funct: dictionary functionhood take := {
    lookup' := take_rel_funct }.

Theorem take_Suc_App_lem
  lq_anf7205759403792803923 lq_anf7205759403792803924 lq_anf7205759403792803925 take_Suc_App_lem_res:
  take_rel
  (Suc_u lq_anf7205759403792803925)
  (App_u lq_anf7205759403792803923 lq_anf7205759403792803924)
  take_Suc_App_lem_res
  ↔ ∃ (take_res : L_u),
    take_rel lq_anf7205759403792803925 lq_anf7205759403792803924 take_res
    ∧ take_Suc_App_lem_res == App_u lq_anf7205759403792803923 take_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite take_Suc_App_lem: f_rel_back.

Theorem take_Suc_Emp_lem lq_anf7205759403792803925 take_Suc_Emp_lem_res:
  take_rel (Suc_u lq_anf7205759403792803925) Emp_u take_Suc_Emp_lem_res
  ↔ take_Suc_Emp_lem_res == Emp_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite take_Suc_Emp_lem: f_rel_back.

Theorem take_Zero_x_lem ds_d2AR take_Zero_x_lem_res:
  take_rel Zero_u ds_d2AR take_Zero_x_lem_res ↔ take_Zero_x_lem_res == Emp_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite take_Zero_x_lem: f_rel_back.

Theorem take_rel_ex
  (ds_d2AQ : Nats_u)
  (ds_d2AQ_p : Nats_wf ds_d2AQ ∧ True)
  (ds_d2AR : L_u)
  (ds_d2AR_p : L_wf ds_d2AR ∧ True):
  take_rel ds_d2AQ ds_d2AR ⌊ take (exist _ ds_d2AQ ds_d2AQ_p) (exist _ ds_d2AR ds_d2AR_p) -⌋.
Proof.
  Opaque take.
  existence_lemma_pre take;
  try revert ds_d2AR_p; generalize dependent ds_d2AR;
  induction ds_d2AQ as [lq_anf7205759403792803925 IH_lq_anf7205759403792803925|];
  intros;
  [destruct ds_d2AR as [lq_anf7205759403792803923 lq_anf7205759403792803924|];
   [fix_notations;
    pose proof (IH_lq_anf7205759403792803925
                ltac:(try clear IH_lq_anf7205759403792803925; solver)
                lq_anf7205759403792803924
                ltac:(try clear IH_lq_anf7205759403792803925; solver)) as IH_10753489;
    try clear IH_lq_anf7205759403792803925 |
    fix_notations] |
   fix_notations];
  simpl in *.
  Transparent take.
  all: (existence_lemma_quicksolve take; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve take_rel_ex: rel_ax_db.

#[global] Opaque take.

Theorem take__take_rel_rw
  (ds_d2AQ : Nats_u)
  (ds_d2AQ_p : Nats_wf ds_d2AQ ∧ True)
  (ds_d2AR : L_u)
  (ds_d2AR_p : L_wf ds_d2AR ∧ True)
  (VV : L_u):
  ⌊ take (exist _ ds_d2AQ ds_d2AQ_p) (exist _ ds_d2AR ds_d2AR_p) -⌋ = VV
  ↔ take_rel ds_d2AQ ds_d2AR VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite take__take_rel_rw: f_rel_funct_db.

#[global] Hint Resolve take__take_rel_rw: rel_ax_db.

#[global] Instance take_lookup_rw: dictionary rwLem take := { lookup' := take__take_rel_rw }.

Theorem take__take_rel (ds_d2AQ : Nats) (ds_d2AR : L) (VV : L_u):
  ⌊ take ds_d2AQ ds_d2AR -⌋ = VV ↔ take_rel ⌊ ds_d2AQ ⌋ ⌊ ds_d2AR ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite take__take_rel: f_rel_funct_db.

Theorem take__take_rel'
  (ds_d2AQ_u : Nats_u) (ds_d2AR_u : L_u) (ds_d2AQ : Nats) (ds_d2AR : L) (VV : L_u):
  ds_d2AQ_u = ⌊ ds_d2AQ ⌋
  → (ds_d2AR_u = ⌊ ds_d2AR ⌋ → ⌊ take ds_d2AQ ds_d2AR -⌋ = VV ↔ take_rel ds_d2AQ_u ds_d2AR_u VV).
Proof.
  intros -> ->. refine (take__take_rel ds_d2AQ ds_d2AR VV).
Qed.

#[global] Hint Resolve take__take_rel': f_rel_funct_db.

Theorem take_rel_mk
  (ds_d2AQ : Nats_u)
  (ds_d2AQ_p : Nats_wf ds_d2AQ ∧ True)
  (ds_d2AR : L_u)
  (ds_d2AR_p : L_wf ds_d2AR ∧ True):
  {VV: _ | take_rel ds_d2AQ ds_d2AR VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, take_rel ds_d2AQ ds_d2AR VV)
          (take (exist _ ds_d2AQ ds_d2AQ_p) (exist _ ds_d2AR ds_d2AR_p))
          _);
  rewrite <- take__take_rel';
  quicksolve.
Qed.

#[global] Hint Resolve take_rel_mk: f_rel_funct_db.

#[global] Instance take_pack:
  @Pack
  (Nats ::RT λ (ds_d2AQ : Nats), L ::RT λ (ds_d2AR : L), nilRT)
  (Nats_u ::UT (L_u ::UT nilUT))
  ltac:(mkProjectsArgListTG (Nats ::RT λ (ds_d2AQ : Nats), L ::RT λ (ds_d2AR : L), nilRT) ((Nats_u ::UT (L_u ::UT nilUT))))
  L_u
  (λ (x_16145195 : ArgList (Nats ::RT λ (ds_d2AQ : Nats), L ::RT λ (ds_d2AR : L), nilRT))
     (v_x_16145195 : L_u),
   ltac:(flattenP (λ (ds_d2AQ : Nats) (ds_d2AR : L) (VV : L_u), L_wf VV ∧ True) x_16145195 v_x_16145195)).
Proof.
  buildPackG take take_rel take__take_rel take_rel_funct.
Defined.

#[global] Instance take_upack: @uPack (Nats_u ::UT (L_u ::UT nilUT)) L_u.
Proof.
  buildUPackG take_rel take_rel_funct.
Defined.

Definition take_all_spec
  (ds_d2AF : Nats)
  (ds_d2AG : {ds_d2AG: L_u | L_wf ds_d2AG
                             ∧ ∃ (length_res : Nats_u),
                               length_rel ds_d2AG length_res
                               ∧ ∃ (geqN_res : bool), geqN_rel ⌊ ds_d2AF -⌋ length_res geqN_res ∧ is_true geqN_res}):
  Type :=
  {{∃ (take_res : L_u), take_rel ⌊ ds_d2AF -⌋ ⌊ ds_d2AG -⌋ take_res ∧ take_res == ⌊ ds_d2AG -⌋}}.

#[global] Hint Unfold take_all_spec: lia_unfold.

Theorem take_all
  (ds_d2AF : Nats)
  (ds_d2AG : {ds_d2AG: L_u | L_wf ds_d2AG
                             ∧ ∃ (length_res : Nats_u),
                               length_rel ds_d2AG length_res
                               ∧ ∃ (geqN_res : bool), geqN_rel ⌊ ds_d2AF -⌋ length_res geqN_res ∧ is_true geqN_res}):
  take_all_spec ds_d2AF ds_d2AG.
Proof.
  destruct ds_d2AF as [ds_d2AF ds_d2AF_p].
  destruct ds_d2AG as [ds_d2AG ds_d2AG_p].
  try revert ds_d2AG_p; generalize dependent ds_d2AG; induction ds_d2AF as [n IH_n|]; intros.
  - destruct ds_d2AG as [x xs|].
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
  - destruct ds_d2AG as [lq_anf7205759403792803974 lq_anf7205759403792803975|].
    + intros; exfalso; solver.
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit), ∃ (take_res : L_u), take_rel Zero_u Emp_u take_res ∧ take_res == Emp_u)
              (# unit)
              ltac:(solver)).
Qed.

Definition zip_spec (ds_d2BQ ds_d2BR : L): Type :=
  L2.

#[global] Hint Unfold zip_spec: lia_unfold.

Definition zip (ds_d2BQ ds_d2BR : L): zip_spec ds_d2BQ ds_d2BR.
Proof.
  destruct ds_d2BQ as [ds_d2BQ ds_d2BQ_p].
  destruct ds_d2BR as [ds_d2BR ds_d2BR_p].
  try revert ds_d2BR_p; generalize dependent ds_d2BR;
  induction ds_d2BQ as [lq_anf7205759403792803834 lq_anf7205759403792803835 IH_lq_anf7205759403792803835|];
  intros.
  - destruct ds_d2BR as [lq_anf7205759403792803832 lq_anf7205759403792803833|].
    + refine (App2
              (MkPair (# lq_anf7205759403792803834) (# lq_anf7205759403792803832))
              (IH_lq_anf7205759403792803835
               ltac:(try clear IH_lq_anf7205759403792803835; solver)
               lq_anf7205759403792803833
               ltac:(try clear IH_lq_anf7205759403792803835; solver))).
    + refine Emp2.
  - refine Emp2.
Defined.

Inductive zip_rel: L_u → L_u → L2_u → Prop :=
  | zip_App_App: ∀ lq_anf7205759403792803834 lq_anf7205759403792803835 lq_anf7205759403792803832 lq_anf7205759403792803833
                   (zip_res : L2_u),
                 zip_rel lq_anf7205759403792803835 lq_anf7205759403792803833 zip_res
                 → zip_rel
                   (App_u lq_anf7205759403792803834 lq_anf7205759403792803835)
                   (App_u lq_anf7205759403792803832 lq_anf7205759403792803833)
                   (App2_u (MkPair_u lq_anf7205759403792803834 lq_anf7205759403792803832) zip_res)
  | zip_App_Emp: ∀ lq_anf7205759403792803834 lq_anf7205759403792803835,
                 zip_rel (App_u lq_anf7205759403792803834 lq_anf7205759403792803835) Emp_u Emp2_u
  | zip_Emp_x: ∀ ds_d2BR, zip_rel Emp_u ds_d2BR Emp2_u.

#[global] Hint Constructors zip_rel: core_hint_db.

#[global] Instance zip_lookup_rel: dictionary rel zip := { lookup' := zip_rel }.

#[global] Instance zip_getF: getFunc zip_rel := { getF' := zip }.

Theorem zip_rel_funct [ds_d2BQ ds_d2BR : L_u]:
  ∀ (VV VV' : L2_u), zip_rel ds_d2BQ ds_d2BR VV → (zip_rel ds_d2BQ ds_d2BR VV' → VV = VV').
Proof.
  try revert ds_d2BR_p; generalize dependent ds_d2BR;
  induction ds_d2BQ as [lq_anf7205759403792803834 lq_anf7205759403792803835 IH_lq_anf7205759403792803835|];
  intros;
  [destruct ds_d2BR as [lq_anf7205759403792803832 lq_anf7205759403792803833|] |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve zip_rel_funct: f_rel_funct_db.

#[global] Instance zip_lookup_funct: dictionary functionhood zip := { lookup' := zip_rel_funct }.

Theorem zip_App_App_lem
  lq_anf7205759403792803832 lq_anf7205759403792803833 lq_anf7205759403792803834 lq_anf7205759403792803835 zip_App_App_lem_res:
  zip_rel
  (App_u lq_anf7205759403792803834 lq_anf7205759403792803835)
  (App_u lq_anf7205759403792803832 lq_anf7205759403792803833)
  zip_App_App_lem_res
  ↔ ∃ (zip_res : L2_u),
    zip_rel lq_anf7205759403792803835 lq_anf7205759403792803833 zip_res
    ∧ zip_App_App_lem_res
      == App2_u (MkPair_u lq_anf7205759403792803834 lq_anf7205759403792803832) zip_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite zip_App_App_lem: f_rel_back.

Theorem zip_App_Emp_lem lq_anf7205759403792803834 lq_anf7205759403792803835 zip_App_Emp_lem_res:
  zip_rel (App_u lq_anf7205759403792803834 lq_anf7205759403792803835) Emp_u zip_App_Emp_lem_res
  ↔ zip_App_Emp_lem_res == Emp2_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite zip_App_Emp_lem: f_rel_back.

Theorem zip_Emp_x_lem ds_d2BR zip_Emp_x_lem_res:
  zip_rel Emp_u ds_d2BR zip_Emp_x_lem_res ↔ zip_Emp_x_lem_res == Emp2_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite zip_Emp_x_lem: f_rel_back.

Theorem zip_rel_ex
  (ds_d2BQ : L_u) (ds_d2BQ_p : L_wf ds_d2BQ ∧ True) (ds_d2BR : L_u) (ds_d2BR_p : L_wf ds_d2BR ∧ True):
  zip_rel ds_d2BQ ds_d2BR ⌊ zip (exist _ ds_d2BQ ds_d2BQ_p) (exist _ ds_d2BR ds_d2BR_p) -⌋.
Proof.
  Opaque zip.
  existence_lemma_pre zip;
  try revert ds_d2BR_p; generalize dependent ds_d2BR;
  induction ds_d2BQ as [lq_anf7205759403792803834 lq_anf7205759403792803835 IH_lq_anf7205759403792803835|];
  intros;
  [destruct ds_d2BR as [lq_anf7205759403792803832 lq_anf7205759403792803833|];
   [fix_notations;
    pose proof (IH_lq_anf7205759403792803835
                ltac:(try clear IH_lq_anf7205759403792803835; solver)
                lq_anf7205759403792803833
                ltac:(try clear IH_lq_anf7205759403792803835; solver)) as IH_31308900;
    try clear IH_lq_anf7205759403792803835 |
    fix_notations] |
   fix_notations];
  simpl in *.
  Transparent zip.
  all: (existence_lemma_quicksolve zip; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve zip_rel_ex: rel_ax_db.

#[global] Opaque zip.

Theorem zip__zip_rel_rw
  (ds_d2BQ : L_u)
  (ds_d2BQ_p : L_wf ds_d2BQ ∧ True)
  (ds_d2BR : L_u)
  (ds_d2BR_p : L_wf ds_d2BR ∧ True)
  (VV : L2_u):
  ⌊ zip (exist _ ds_d2BQ ds_d2BQ_p) (exist _ ds_d2BR ds_d2BR_p) -⌋ = VV ↔ zip_rel ds_d2BQ ds_d2BR VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite zip__zip_rel_rw: f_rel_funct_db.

#[global] Hint Resolve zip__zip_rel_rw: rel_ax_db.

#[global] Instance zip_lookup_rw: dictionary rwLem zip := { lookup' := zip__zip_rel_rw }.

Theorem zip__zip_rel (ds_d2BQ ds_d2BR : L) (VV : L2_u):
  ⌊ zip ds_d2BQ ds_d2BR -⌋ = VV ↔ zip_rel ⌊ ds_d2BQ ⌋ ⌊ ds_d2BR ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite zip__zip_rel: f_rel_funct_db.

Theorem zip__zip_rel' (ds_d2BQ_u ds_d2BR_u : L_u) (ds_d2BQ ds_d2BR : L) (VV : L2_u):
  ds_d2BQ_u = ⌊ ds_d2BQ ⌋
  → (ds_d2BR_u = ⌊ ds_d2BR ⌋ → ⌊ zip ds_d2BQ ds_d2BR -⌋ = VV ↔ zip_rel ds_d2BQ_u ds_d2BR_u VV).
Proof.
  intros -> ->. refine (zip__zip_rel ds_d2BQ ds_d2BR VV).
Qed.

#[global] Hint Resolve zip__zip_rel': f_rel_funct_db.

Theorem zip_rel_mk
  (ds_d2BQ : L_u) (ds_d2BQ_p : L_wf ds_d2BQ ∧ True) (ds_d2BR : L_u) (ds_d2BR_p : L_wf ds_d2BR ∧ True):
  {VV: _ | zip_rel ds_d2BQ ds_d2BR VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, zip_rel ds_d2BQ ds_d2BR VV)
          (zip (exist _ ds_d2BQ ds_d2BQ_p) (exist _ ds_d2BR ds_d2BR_p))
          _);
  rewrite <- zip__zip_rel';
  quicksolve.
Qed.

#[global] Hint Resolve zip_rel_mk: f_rel_funct_db.

#[global] Instance zip_pack:
  @Pack
  (L ::RT λ (ds_d2BQ : L), L ::RT λ (ds_d2BR : L), nilRT)
  (L_u ::UT (L_u ::UT nilUT))
  ltac:(mkProjectsArgListTG (L ::RT λ (ds_d2BQ : L), L ::RT λ (ds_d2BR : L), nilRT) ((L_u ::UT (L_u ::UT nilUT))))
  L2_u
  (λ (x_60378309 : ArgList (L ::RT λ (ds_d2BQ : L), L ::RT λ (ds_d2BR : L), nilRT))
     (v_x_60378309 : L2_u),
   ltac:(flattenP (λ (ds_d2BQ ds_d2BR : L) (VV : L2_u), L2_wf VV ∧ True) x_60378309 v_x_60378309)).
Proof.
  buildPackG zip zip_rel zip__zip_rel zip_rel_funct.
Defined.

#[global] Instance zip_upack: @uPack (L_u ::UT (L_u ::UT nilUT)) L2_u.
Proof.
  buildUPackG zip_rel zip_rel_funct.
Defined.

Definition length_zip_spec
  (ds_d2Bj : Nats)
  (ds_d2Bk : {ds_d2Bk: L_u | L_wf ds_d2Bk
                             ∧ ∃ (length_res : Nats_u), length_rel ds_d2Bk length_res ∧ length_res == ⌊ ds_d2Bj -⌋})
  (ds_d2Bl : {ds_d2Bl: L_u | L_wf ds_d2Bl
                             ∧ ∃ (length_res : Nats_u), length_rel ds_d2Bl length_res ∧ length_res == ⌊ ds_d2Bj -⌋}):
  Type :=
  {{∃ (zip_res : L2_u),
    zip_rel ⌊ ds_d2Bk -⌋ ⌊ ds_d2Bl -⌋ zip_res
    ∧ ∃ (length2_res : Nats_u), length2_rel zip_res length2_res ∧ length2_res == ⌊ ds_d2Bj -⌋}}.

#[global] Hint Unfold length_zip_spec: lia_unfold.

Theorem length_zip
  (ds_d2Bj : Nats)
  (ds_d2Bk : {ds_d2Bk: L_u | L_wf ds_d2Bk
                             ∧ ∃ (length_res : Nats_u), length_rel ds_d2Bk length_res ∧ length_res == ⌊ ds_d2Bj -⌋})
  (ds_d2Bl : {ds_d2Bl: L_u | L_wf ds_d2Bl
                             ∧ ∃ (length_res : Nats_u), length_rel ds_d2Bl length_res ∧ length_res == ⌊ ds_d2Bj -⌋}):
  length_zip_spec ds_d2Bj ds_d2Bk ds_d2Bl.
Proof.
  destruct ds_d2Bj as [ds_d2Bj ds_d2Bj_p].
  destruct ds_d2Bk as [ds_d2Bk ds_d2Bk_p].
  destruct ds_d2Bl as [ds_d2Bl ds_d2Bl_p].
  try revert ds_d2Bl_p; generalize dependent ds_d2Bl;
  try revert ds_d2Bk_p; generalize dependent ds_d2Bk;
  induction ds_d2Bj as [n IH_n|];
  intros.
  - destruct ds_d2Bk as [x xs|].
    + destruct ds_d2Bl as [y ys|].
      * refine (subsumptionCast
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
      * intros; exfalso; solver.
    + intros; exfalso; solver.
  - destruct ds_d2Bk as [lq_anf7205759403792803873 lq_anf7205759403792803874|].
    + intros; exfalso; solver.
    + destruct ds_d2Bl as [lq_anf7205759403792803871 lq_anf7205759403792803872|].
      * intros; exfalso; solver.
      * refine (subsumptionCast
                Unit
                (λ (VV : Unit),
                 ∃ (zip_res : L2_u),
                 zip_rel Emp_u Emp_u zip_res
                 ∧ ∃ (length2_res : Nats_u), length2_rel zip_res length2_res ∧ length2_res == Zero_u)
                (# unit)
                ltac:(solver)).
Qed.

Definition length_zipWith_spec
  (ds_d2Be : Nats)
  (f : @Pack
       ({VV: Z | True}
        ::RT λ (lq_tmp0 : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG ({VV: Z | True}
 ::RT λ (lq_tmp0 : {VV: Z | True}),
      {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_41814097 : ArgList ({VV: Z | True}
                                 ::RT λ (lq_tmp0 : {VV: Z | True}),
                                      {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_41814097 : Z),
        ltac:(flattenP (λ (lq_tmp0 lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_41814097 v_x_41814097)))
  (ds_d2Bf : {ds_d2Bf: L_u | L_wf ds_d2Bf
                             ∧ ∃ (length_res : Nats_u), length_rel ds_d2Bf length_res ∧ length_res == ⌊ ds_d2Be -⌋})
  (ds_d2Bg : {ds_d2Bg: L_u | L_wf ds_d2Bg
                             ∧ ∃ (length_res : Nats_u), length_rel ds_d2Bg length_res ∧ length_res == ⌊ ds_d2Be -⌋}):
  Type :=
  {{∃ (zip_res : L2_u),
    zip_rel ⌊ ds_d2Bf -⌋ ⌊ ds_d2Bg -⌋ zip_res
    ∧ ∃ (length2_res : Nats_u), length2_rel zip_res length2_res ∧ length2_res == ⌊ ds_d2Be -⌋}}.

#[global] Hint Unfold length_zipWith_spec: lia_unfold.

Theorem length_zipWith
  (ds_d2Be : Nats)
  (f : @Pack
       ({VV: Z | True}
        ::RT λ (lq_tmp0 : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG ({VV: Z | True}
 ::RT λ (lq_tmp0 : {VV: Z | True}),
      {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_41814097 : ArgList ({VV: Z | True}
                                 ::RT λ (lq_tmp0 : {VV: Z | True}),
                                      {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_41814097 : Z),
        ltac:(flattenP (λ (lq_tmp0 lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_41814097 v_x_41814097)))
  (ds_d2Bf : {ds_d2Bf: L_u | L_wf ds_d2Bf
                             ∧ ∃ (length_res : Nats_u), length_rel ds_d2Bf length_res ∧ length_res == ⌊ ds_d2Be -⌋})
  (ds_d2Bg : {ds_d2Bg: L_u | L_wf ds_d2Bg
                             ∧ ∃ (length_res : Nats_u), length_rel ds_d2Bg length_res ∧ length_res == ⌊ ds_d2Be -⌋}):
  length_zipWith_spec ds_d2Be f ds_d2Bf ds_d2Bg.
Proof.
  destruct ds_d2Be as [ds_d2Be ds_d2Be_p].
  destruct ds_d2Bf as [ds_d2Bf ds_d2Bf_p].
  destruct ds_d2Bg as [ds_d2Bg ds_d2Bg_p].
  try revert ds_d2Bg_p; generalize dependent ds_d2Bg;
  try revert ds_d2Bf_p; generalize dependent ds_d2Bf;
  try revert f_p; generalize dependent f;
  induction ds_d2Be as [n IH_n|];
  intros.
  - destruct ds_d2Bf as [x xs|].
    + destruct ds_d2Bg as [y ys|].
      * refine (subsumptionCast
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
      * intros; exfalso; solver.
    + intros; exfalso; solver.
  - destruct ds_d2Bf as [lq_anf7205759403792803894 lq_anf7205759403792803895|].
    + intros; exfalso; solver.
    + destruct ds_d2Bg as [lq_anf7205759403792803892 lq_anf7205759403792803893|].
      * intros; exfalso; solver.
      * refine (subsumptionCast
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
       ltac:(mkProjectsArgListTG ({VV: Z | True}
 ::RT λ (lq_tmp0 : {VV: Z | True}),
      {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_41814097 : ArgList ({VV: Z | True}
                                 ::RT λ (lq_tmp0 : {VV: Z | True}),
                                      {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_41814097 : Z),
        ltac:(flattenP (λ (lq_tmp0 lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_41814097 v_x_41814097)))
  (ds_d2BG ds_d2BH : L):
  Type :=
  L.

#[global] Hint Unfold zipWith_spec: lia_unfold.

Definition zipWith
  (f : @Pack
       ({VV: Z | True}
        ::RT λ (lq_tmp0 : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG ({VV: Z | True}
 ::RT λ (lq_tmp0 : {VV: Z | True}),
      {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_41814097 : ArgList ({VV: Z | True}
                                 ::RT λ (lq_tmp0 : {VV: Z | True}),
                                      {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_41814097 : Z),
        ltac:(flattenP (λ (lq_tmp0 lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_41814097 v_x_41814097)))
  (ds_d2BG ds_d2BH : L):
  zipWith_spec f ds_d2BG ds_d2BH.
Proof.
  destruct ds_d2BG as [ds_d2BG ds_d2BG_p].
  destruct ds_d2BH as [ds_d2BH ds_d2BH_p].
  try revert ds_d2BH_p; generalize dependent ds_d2BH; try revert f_p; generalize dependent f;
  induction ds_d2BG as [lq_anf7205759403792803850 lq_anf7205759403792803851 IH_lq_anf7205759403792803851|];
  intros.
  - destruct ds_d2BH as [lq_anf7205759403792803848 lq_anf7205759403792803849|].
    + refine (App
              (getPackF f (# lq_anf7205759403792803850) (# lq_anf7205759403792803848))
              (IH_lq_anf7205759403792803851
               ltac:(try clear IH_lq_anf7205759403792803851; solver)
               f
               lq_anf7205759403792803849
               ltac:(try clear IH_lq_anf7205759403792803851; solver))).
    + refine Emp.
  - refine Emp.
Defined.

Inductive zipWith_rel: @uPack (Z ::UT (Z ::UT nilUT)) Z → L_u → L_u → L_u → Prop :=
  | zipWith_x_App_App: ∀ (f : @uPack (Z ::UT (Z ::UT nilUT)) Z)
                         lq_anf7205759403792803850 lq_anf7205759403792803851 lq_anf7205759403792803848 lq_anf7205759403792803849
                         (zipWith_res : L_u),
                       zipWith_rel f lq_anf7205759403792803851 lq_anf7205759403792803849 zipWith_res
                       → ∀ (f_res : Z),
                         getUPackRel f lq_anf7205759403792803850 lq_anf7205759403792803848 f_res
                         → zipWith_rel
                           f
                           (App_u lq_anf7205759403792803850 lq_anf7205759403792803851)
                           (App_u lq_anf7205759403792803848 lq_anf7205759403792803849)
                           (App_u f_res zipWith_res)
  | zipWith_x_App_Emp: ∀ (f : @uPack (Z ::UT (Z ::UT nilUT)) Z)
                         lq_anf7205759403792803850 lq_anf7205759403792803851,
                       zipWith_rel f (App_u lq_anf7205759403792803850 lq_anf7205759403792803851) Emp_u Emp_u
  | zipWith_x_Emp_x: ∀ (f : @uPack (Z ::UT (Z ::UT nilUT)) Z) ds_d2BH,
                     zipWith_rel f Emp_u ds_d2BH Emp_u.

#[global] Hint Constructors zipWith_rel: core_hint_db.

#[global] Instance zipWith_lookup_rel: dictionary rel zipWith := { lookup' := zipWith_rel }.

#[global] Instance zipWith_getF: getFunc zipWith_rel := { getF' := zipWith }.

Theorem zipWith_rel_funct [f : @uPack (Z ::UT (Z ::UT nilUT)) Z] [ds_d2BG ds_d2BH : L_u]:
  ∀ (VV VV' : L_u), zipWith_rel f ds_d2BG ds_d2BH VV → (zipWith_rel f ds_d2BG ds_d2BH VV' → VV = VV').
Proof.
  try revert ds_d2BH_p; generalize dependent ds_d2BH; try revert f_p; generalize dependent f;
  induction ds_d2BG as [lq_anf7205759403792803850 lq_anf7205759403792803851 IH_lq_anf7205759403792803851|];
  intros;
  [destruct ds_d2BH as [lq_anf7205759403792803848 lq_anf7205759403792803849|] |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve zipWith_rel_funct: f_rel_funct_db.

#[global] Instance zipWith_lookup_funct: dictionary functionhood zipWith := {
    lookup' := zipWith_rel_funct }.

Theorem zipWith_x_App_App_lem
  f lq_anf7205759403792803848 lq_anf7205759403792803849 lq_anf7205759403792803850 lq_anf7205759403792803851 zipWith_x_App_App_lem_res:
  zipWith_rel
  f
  (App_u lq_anf7205759403792803850 lq_anf7205759403792803851)
  (App_u lq_anf7205759403792803848 lq_anf7205759403792803849)
  zipWith_x_App_App_lem_res
  ↔ ∃ (zipWith_res : L_u),
    zipWith_rel f lq_anf7205759403792803851 lq_anf7205759403792803849 zipWith_res
    ∧ ∃ (f_res : Z),
      getUPackRel f lq_anf7205759403792803850 lq_anf7205759403792803848 f_res
      ∧ zipWith_x_App_App_lem_res == App_u f_res zipWith_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite zipWith_x_App_App_lem: f_rel_back.

Theorem zipWith_x_App_Emp_lem
  f lq_anf7205759403792803850 lq_anf7205759403792803851 zipWith_x_App_Emp_lem_res:
  zipWith_rel
  f
  (App_u lq_anf7205759403792803850 lq_anf7205759403792803851)
  Emp_u
  zipWith_x_App_Emp_lem_res
  ↔ zipWith_x_App_Emp_lem_res == Emp_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite zipWith_x_App_Emp_lem: f_rel_back.

Theorem zipWith_x_Emp_x_lem ds_d2BH f zipWith_x_Emp_x_lem_res:
  zipWith_rel f Emp_u ds_d2BH zipWith_x_Emp_x_lem_res ↔ zipWith_x_Emp_x_lem_res == Emp_u.
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
       ltac:(mkProjectsArgListTG ({lq_tmp0: Z | True}
 ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}),
      {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_15576161 : ArgList ({lq_tmp0: Z | True}
                                 ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}),
                                      {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_15576161 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {lq_tmp0: Z | True})
   (lq_tmp1 : {lq_tmp1: Z | True})
   (VV : Z),
 True) x_15576161 v_x_15576161)))
  (ds_d2BG : L_u)
  (ds_d2BG_p : L_wf ds_d2BG ∧ True)
  (ds_d2BH : L_u)
  (ds_d2BH_p : L_wf ds_d2BH ∧ True):
  zipWith_rel
  ⌊ f ⌋
  ds_d2BG
  ds_d2BH
  ⌊ zipWith f (exist _ ds_d2BG ds_d2BG_p) (exist _ ds_d2BH ds_d2BH_p) -⌋.
Proof.
  Opaque zipWith.
  existence_lemma_pre zipWith;
  try revert ds_d2BH_p; generalize dependent ds_d2BH; try revert f_p; generalize dependent f;
  induction ds_d2BG as [lq_anf7205759403792803850 lq_anf7205759403792803851 IH_lq_anf7205759403792803851|];
  intros;
  [destruct ds_d2BH as [lq_anf7205759403792803848 lq_anf7205759403792803849|];
   [fix_notations;
    pose proof (IH_lq_anf7205759403792803851
                ltac:(try clear IH_lq_anf7205759403792803851; solver)
                f
                lq_anf7205759403792803849
                ltac:(try clear IH_lq_anf7205759403792803851; solver)) as IH_88794620;
    try clear IH_lq_anf7205759403792803851 |
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
       ltac:(mkProjectsArgListTG ({lq_tmp0: Z | True}
 ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}),
      {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_15576161 : ArgList ({lq_tmp0: Z | True}
                                 ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}),
                                      {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_15576161 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {lq_tmp0: Z | True})
   (lq_tmp1 : {lq_tmp1: Z | True})
   (VV : Z),
 True) x_15576161 v_x_15576161)))
  (ds_d2BG : L_u)
  (ds_d2BG_p : L_wf ds_d2BG ∧ True)
  (ds_d2BH : L_u)
  (ds_d2BH_p : L_wf ds_d2BH ∧ True)
  (VV : L_u):
  ⌊ zipWith f (exist _ ds_d2BG ds_d2BG_p) (exist _ ds_d2BH ds_d2BH_p) -⌋ = VV
  ↔ zipWith_rel ⌊ f ⌋ ds_d2BG ds_d2BH VV.
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
       ltac:(mkProjectsArgListTG ({VV: Z | True}
 ::RT λ (lq_tmp0 : {VV: Z | True}),
      {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_41814097 : ArgList ({VV: Z | True}
                                 ::RT λ (lq_tmp0 : {VV: Z | True}),
                                      {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_41814097 : Z),
        ltac:(flattenP (λ (lq_tmp0 lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_41814097 v_x_41814097)))
  (ds_d2BG ds_d2BH : L)
  (VV : L_u):
  ⌊ zipWith f ds_d2BG ds_d2BH -⌋ = VV ↔ zipWith_rel ⌊ f ⌋ ⌊ ds_d2BG ⌋ ⌊ ds_d2BH ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite zipWith__zipWith_rel: f_rel_funct_db.

Theorem zipWith__zipWith_rel'
  (f_u : @uPack (Z ::UT (Z ::UT nilUT)) Z)
  (ds_d2BG_u ds_d2BH_u : L_u)
  (f : @Pack
       ({VV: Z | True}
        ::RT λ (lq_tmp0 : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG ({VV: Z | True}
 ::RT λ (lq_tmp0 : {VV: Z | True}),
      {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_41814097 : ArgList ({VV: Z | True}
                                 ::RT λ (lq_tmp0 : {VV: Z | True}),
                                      {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_41814097 : Z),
        ltac:(flattenP (λ (lq_tmp0 lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_41814097 v_x_41814097)))
  (ds_d2BG ds_d2BH : L)
  (VV : L_u):
  f_u = ⌊ f ⌋
  → (ds_d2BG_u = ⌊ ds_d2BG ⌋
     → (ds_d2BH_u = ⌊ ds_d2BH ⌋
        → ⌊ zipWith f ds_d2BG ds_d2BH -⌋ = VV ↔ zipWith_rel f_u ds_d2BG_u ds_d2BH_u VV)).
Proof.
  intros -> -> ->. refine (zipWith__zipWith_rel f ds_d2BG ds_d2BH VV).
Qed.

#[global] Hint Resolve zipWith__zipWith_rel': f_rel_funct_db.

Theorem zipWith_rel_mk
  (f : @Pack
       ({lq_tmp0: Z | True}
        ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}),
             {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG ({lq_tmp0: Z | True}
 ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}),
      {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_15576161 : ArgList ({lq_tmp0: Z | True}
                                 ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}),
                                      {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_15576161 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {lq_tmp0: Z | True})
   (lq_tmp1 : {lq_tmp1: Z | True})
   (VV : Z),
 True) x_15576161 v_x_15576161)))
  (ds_d2BG : L_u)
  (ds_d2BG_p : L_wf ds_d2BG ∧ True)
  (ds_d2BH : L_u)
  (ds_d2BH_p : L_wf ds_d2BH ∧ True):
  {VV: _ | zipWith_rel (packProj f) ds_d2BG ds_d2BH VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, zipWith_rel (packProj f) ds_d2BG ds_d2BH VV)
          (zipWith f (exist _ ds_d2BG ds_d2BG_p) (exist _ ds_d2BH ds_d2BH_p))
          _);
  rewrite <- zipWith__zipWith_rel';
  quicksolve.
Qed.

#[global] Hint Resolve zipWith_rel_mk: f_rel_funct_db.

Definition zip_take_spec (ds_d2C2 m : L): Type :=
  {{∃ (zip_res : L2_u),
    zip_rel ⌊ ds_d2C2 -⌋ ⌊ m -⌋ zip_res
    ∧ ∃ (length_res : Nats_u),
      length_rel ⌊ ds_d2C2 -⌋ length_res
      ∧ ∃ (take_res : L_u),
        take_rel length_res ⌊ m -⌋ take_res
        ∧ ∃ (length_res_2 : Nats_u),
          length_rel ⌊ m -⌋ length_res_2
          ∧ ∃ (take_res_2 : L_u),
            take_rel length_res_2 ⌊ ds_d2C2 -⌋ take_res_2
            ∧ ∃ (zip_res_2 : L2_u), zip_rel take_res_2 take_res zip_res_2 ∧ zip_res == zip_res_2}}.

#[global] Hint Unfold zip_take_spec: lia_unfold.

Theorem zip_take (ds_d2C2 m : L): zip_take_spec ds_d2C2 m.
Proof.
  destruct ds_d2C2 as [ds_d2C2 ds_d2C2_p].
  destruct m as [m m_p].
  try revert m_p; generalize dependent m;
  induction ds_d2C2 as [lq_anf7205759403792803956 lq_anf7205759403792803957 IH_lq_anf7205759403792803957|];
  intros.
  - destruct m as [lq_anf7205759403792803936 lq_anf7205759403792803937|].
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∃ (zip_res : L2_u),
               zip_rel
               (App_u lq_anf7205759403792803956 lq_anf7205759403792803957)
               (App_u lq_anf7205759403792803936 lq_anf7205759403792803937)
               zip_res
               ∧ ∃ (length_res : Nats_u),
                 length_rel (App_u lq_anf7205759403792803956 lq_anf7205759403792803957) length_res
                 ∧ ∃ (take_res : L_u),
                   take_rel length_res (App_u lq_anf7205759403792803936 lq_anf7205759403792803937) take_res
                   ∧ ∃ (length_res_2 : Nats_u),
                     length_rel (App_u lq_anf7205759403792803936 lq_anf7205759403792803937) length_res_2
                     ∧ ∃ (take_res_2 : L_u),
                       take_rel length_res_2 (App_u lq_anf7205759403792803956 lq_anf7205759403792803957) take_res_2
                       ∧ ∃ (zip_res_2 : L2_u), zip_rel take_res_2 take_res zip_res_2 ∧ zip_res == zip_res_2)
              (IH_lq_anf7205759403792803957
               ltac:(try clear IH_lq_anf7205759403792803957; solver)
               lq_anf7205759403792803937
               ltac:(try clear IH_lq_anf7205759403792803957; solver))
              ltac:(solver)).
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∃ (zip_res : L2_u),
               zip_rel (App_u lq_anf7205759403792803956 lq_anf7205759403792803957) Emp_u zip_res
               ∧ ∃ (length_res : Nats_u),
                 length_rel (App_u lq_anf7205759403792803956 lq_anf7205759403792803957) length_res
                 ∧ ∃ (take_res : L_u),
                   take_rel length_res Emp_u take_res
                   ∧ ∃ (length_res_2 : Nats_u),
                     length_rel Emp_u length_res_2
                     ∧ ∃ (take_res_2 : L_u),
                       take_rel length_res_2 (App_u lq_anf7205759403792803956 lq_anf7205759403792803957) take_res_2
                       ∧ ∃ (zip_res_2 : L2_u), zip_rel take_res_2 take_res zip_res_2 ∧ zip_res == zip_res_2)
              (# unit)
              ltac:(solver)).
  - assert (h_39899679 : true).
    { refine (zip
              (take (length (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) Emp)
              (take (length Emp) (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver)))). }
    refine (subsumptionCast
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
            (# unit)
            ltac:(solver)).
Qed.
