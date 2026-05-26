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

Definition geqN_spec (ds_d2z8 ds_d2z9 : Nats): Type :=
  Bool.

#[global] Hint Unfold geqN_spec: lia_unfold.

Definition geqN (ds_d2z8 ds_d2z9 : Nats): geqN_spec ds_d2z8 ds_d2z9.
Proof.
  destruct ds_d2z8 as [ds_d2z8 ds_d2z8_p].
  destruct ds_d2z9 as [ds_d2z9 ds_d2z9_p].
  try revert ds_d2z8_p; generalize dependent ds_d2z8;
  induction ds_d2z9 as [lq_anf7205759403792803869 IH_lq_anf7205759403792803869|];
  intros.
  - destruct ds_d2z8 as [m|].
    + refine (IH_lq_anf7205759403792803869
              ltac:(try clear IH_lq_anf7205759403792803869; solver)
              m
              ltac:(try clear IH_lq_anf7205759403792803869; solver)).
    + refine (# false).
  - refine (# true).
Defined.

Inductive geqN_rel: Nats_u → Nats_u → bool → Prop :=
  | geqN_Suc_Suc: ∀ m lq_anf7205759403792803869 (geqN_res : bool),
                  geqN_rel m lq_anf7205759403792803869 geqN_res
                  → geqN_rel (Suc_u m) (Suc_u lq_anf7205759403792803869) geqN_res
  | geqN_Zero_Suc: ∀ lq_anf7205759403792803869,
                   geqN_rel Zero_u (Suc_u lq_anf7205759403792803869) false
  | geqN_x_Zero: ∀ ds_d2z8, geqN_rel ds_d2z8 Zero_u true.

#[global] Hint Constructors geqN_rel: core_hint_db.

#[global] Instance geqN_lookup_rel: dictionary rel geqN := { lookup' := geqN_rel }.

#[global] Instance geqN_getF: getFunc geqN_rel := { getF' := geqN }.

Theorem geqN_rel_funct [ds_d2z8 ds_d2z9 : Nats_u]:
  ∀ (VV VV' : bool), geqN_rel ds_d2z8 ds_d2z9 VV → (geqN_rel ds_d2z8 ds_d2z9 VV' → VV = VV').
Proof.
  try revert ds_d2z8_p; generalize dependent ds_d2z8;
  induction ds_d2z9 as [lq_anf7205759403792803869 IH_lq_anf7205759403792803869|];
  intros;
  [destruct ds_d2z8 as [m|] |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve geqN_rel_funct: f_rel_funct_db.

#[global] Instance geqN_lookup_funct: dictionary functionhood geqN := {
    lookup' := geqN_rel_funct }.

Theorem geqN_Suc_Suc_lem lq_anf7205759403792803869 m geqN_Suc_Suc_lem_res:
  geqN_rel (Suc_u m) (Suc_u lq_anf7205759403792803869) geqN_Suc_Suc_lem_res
  ↔ ∃ (geqN_res : bool),
    geqN_rel m lq_anf7205759403792803869 geqN_res ∧ geqN_Suc_Suc_lem_res == geqN_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite geqN_Suc_Suc_lem: f_rel_back.

Theorem geqN_Zero_Suc_lem lq_anf7205759403792803869 geqN_Zero_Suc_lem_res:
  geqN_rel Zero_u (Suc_u lq_anf7205759403792803869) geqN_Zero_Suc_lem_res
  ↔ geqN_Zero_Suc_lem_res == false.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite geqN_Zero_Suc_lem: f_rel_back.

Theorem geqN_x_Zero_lem ds_d2z8 geqN_x_Zero_lem_res:
  geqN_rel ds_d2z8 Zero_u geqN_x_Zero_lem_res ↔ geqN_x_Zero_lem_res == true.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite geqN_x_Zero_lem: f_rel_back.

Theorem geqN_rel_ex
  (ds_d2z8 : Nats_u)
  (ds_d2z8_p : Nats_wf ds_d2z8 ∧ True)
  (ds_d2z9 : Nats_u)
  (ds_d2z9_p : Nats_wf ds_d2z9 ∧ True):
  geqN_rel ds_d2z8 ds_d2z9 ⌊ geqN (exist _ ds_d2z8 ds_d2z8_p) (exist _ ds_d2z9 ds_d2z9_p) -⌋.
Proof.
  Opaque geqN.
  existence_lemma_pre geqN;
  try revert ds_d2z8_p; generalize dependent ds_d2z8;
  induction ds_d2z9 as [lq_anf7205759403792803869 IH_lq_anf7205759403792803869|];
  intros;
  [destruct ds_d2z8 as [m|];
   [fix_notations;
    pose proof (IH_lq_anf7205759403792803869
                ltac:(try clear IH_lq_anf7205759403792803869; solver)
                m
                ltac:(try clear IH_lq_anf7205759403792803869; solver)) as IH_26162361;
    try clear IH_lq_anf7205759403792803869 |
    fix_notations] |
   fix_notations];
  simpl in *.
  Transparent geqN.
  all: (existence_lemma_quicksolve geqN; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve geqN_rel_ex: rel_ax_db.

#[global] Opaque geqN.

Theorem geqN__geqN_rel_rw
  (ds_d2z8 : Nats_u)
  (ds_d2z8_p : Nats_wf ds_d2z8 ∧ True)
  (ds_d2z9 : Nats_u)
  (ds_d2z9_p : Nats_wf ds_d2z9 ∧ True)
  (VV : bool):
  ⌊ geqN (exist _ ds_d2z8 ds_d2z8_p) (exist _ ds_d2z9 ds_d2z9_p) -⌋ = VV
  ↔ geqN_rel ds_d2z8 ds_d2z9 VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite geqN__geqN_rel_rw: f_rel_funct_db.

#[global] Hint Resolve geqN__geqN_rel_rw: rel_ax_db.

#[global] Instance geqN_lookup_rw: dictionary rwLem geqN := { lookup' := geqN__geqN_rel_rw }.

Theorem geqN__geqN_rel (ds_d2z8 ds_d2z9 : Nats) (VV : bool):
  ⌊ geqN ds_d2z8 ds_d2z9 -⌋ = VV ↔ geqN_rel ⌊ ds_d2z8 ⌋ ⌊ ds_d2z9 ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite geqN__geqN_rel: f_rel_funct_db.

Theorem geqN__geqN_rel' (ds_d2z8_u ds_d2z9_u : Nats_u) (ds_d2z8 ds_d2z9 : Nats) (VV : bool):
  ds_d2z8_u = ⌊ ds_d2z8 ⌋
  → (ds_d2z9_u = ⌊ ds_d2z9 ⌋ → ⌊ geqN ds_d2z8 ds_d2z9 -⌋ = VV ↔ geqN_rel ds_d2z8_u ds_d2z9_u VV).
Proof.
  intros -> ->. refine (geqN__geqN_rel ds_d2z8 ds_d2z9 VV).
Qed.

#[global] Hint Resolve geqN__geqN_rel': f_rel_funct_db.

Theorem geqN_rel_mk
  (ds_d2z8 : Nats_u)
  (ds_d2z8_p : Nats_wf ds_d2z8 ∧ True)
  (ds_d2z9 : Nats_u)
  (ds_d2z9_p : Nats_wf ds_d2z9 ∧ True):
  {VV: _ | geqN_rel ds_d2z8 ds_d2z9 VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, geqN_rel ds_d2z8 ds_d2z9 VV)
          (geqN (exist _ ds_d2z8 ds_d2z8_p) (exist _ ds_d2z9 ds_d2z9_p))
          _);
  rewrite <- geqN__geqN_rel';
  quicksolve.
Qed.

#[global] Hint Resolve geqN_rel_mk: f_rel_funct_db.

#[global] Instance geqN_pack:
  @Pack
  (Nats ::RT λ (ds_d2z8 : Nats), Nats ::RT λ (ds_d2z9 : Nats), nilRT)
  (Nats_u ::UT (Nats_u ::UT nilUT))
  ltac:(mkProjectsArgListTG (Nats ::RT λ (ds_d2z8 : Nats), Nats ::RT λ (ds_d2z9 : Nats), nilRT) ((Nats_u ::UT (Nats_u ::UT nilUT))))
  bool
  (λ (x_84801047 : ArgList (Nats ::RT λ (ds_d2z8 : Nats), Nats ::RT λ (ds_d2z9 : Nats), nilRT))
     (v_x_84801047 : bool),
   ltac:(flattenP (λ (ds_d2z8 ds_d2z9 : Nats) (VV : bool), True) x_84801047 v_x_84801047)).
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

Definition length2_spec (ds_d2zO : L2): Type :=
  Nats.

#[global] Hint Unfold length2_spec: lia_unfold.

Definition length2 (ds_d2zO : L2): length2_spec ds_d2zO.
Proof.
  destruct ds_d2zO as [ds_d2zO ds_d2zO_p].
  induction ds_d2zO as [ds_d2zQ xs IH_xs|].
  - refine (Suc (IH_xs ltac:(try clear IH_xs; solver))).
  - refine Zero.
Defined.

Inductive length2_rel: L2_u → Nats_u → Prop :=
  | length2_App2: ∀ ds_d2zQ xs (length2_res : Nats_u),
                  length2_rel xs length2_res → length2_rel (App2_u ds_d2zQ xs) (Suc_u length2_res)
  | length2_Emp2: length2_rel Emp2_u Zero_u.

#[global] Hint Constructors length2_rel: core_hint_db.

#[global] Instance length2_lookup_rel: dictionary rel length2 := { lookup' := length2_rel }.

#[global] Instance length2_getF: getFunc length2_rel := { getF' := length2 }.

Theorem length2_rel_funct [ds_d2zO : L2_u]:
  ∀ (VV VV' : Nats_u), length2_rel ds_d2zO VV → (length2_rel ds_d2zO VV' → VV = VV').
Proof.
  induction ds_d2zO as [ds_d2zQ xs IH_xs|]; rel_functionhood_body.
Qed.

#[global] Hint Resolve length2_rel_funct: f_rel_funct_db.

#[global] Instance length2_lookup_funct: dictionary functionhood length2 := {
    lookup' := length2_rel_funct }.

Theorem length2_App2_lem ds_d2zQ xs length2_App2_lem_res:
  length2_rel (App2_u ds_d2zQ xs) length2_App2_lem_res
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

Theorem length2_rel_ex (ds_d2zO : L2_u) (ds_d2zO_p : L2_wf ds_d2zO ∧ True):
  length2_rel ds_d2zO ⌊ length2 (exist _ ds_d2zO ds_d2zO_p) -⌋.
Proof.
  Opaque length2.
  existence_lemma_pre length2;
  induction ds_d2zO as [ds_d2zQ xs IH_xs|];
  [fix_notations; pose proof (IH_xs ltac:(try clear IH_xs; solver)) as IH_67415571; try clear IH_xs |
   fix_notations];
  simpl in *.
  Transparent length2.
  all: (existence_lemma_quicksolve length2; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve length2_rel_ex: rel_ax_db.

#[global] Opaque length2.

Theorem length2__length2_rel_rw (ds_d2zO : L2_u) (ds_d2zO_p : L2_wf ds_d2zO ∧ True) (VV : Nats_u):
  ⌊ length2 (exist _ ds_d2zO ds_d2zO_p) -⌋ = VV ↔ length2_rel ds_d2zO VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite length2__length2_rel_rw: f_rel_funct_db.

#[global] Hint Resolve length2__length2_rel_rw: rel_ax_db.

#[global] Instance length2_lookup_rw: dictionary rwLem length2 := {
    lookup' := length2__length2_rel_rw }.

Theorem length2__length2_rel (ds_d2zO : L2) (VV : Nats_u):
  ⌊ length2 ds_d2zO -⌋ = VV ↔ length2_rel ⌊ ds_d2zO ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite length2__length2_rel: f_rel_funct_db.

Theorem length2__length2_rel' (ds_d2zO_u : L2_u) (ds_d2zO : L2) (VV : Nats_u):
  ds_d2zO_u = ⌊ ds_d2zO ⌋ → ⌊ length2 ds_d2zO -⌋ = VV ↔ length2_rel ds_d2zO_u VV.
Proof.
  intros ->. refine (length2__length2_rel ds_d2zO VV).
Qed.

#[global] Hint Resolve length2__length2_rel': f_rel_funct_db.

Theorem length2_rel_mk (ds_d2zO : L2_u) (ds_d2zO_p : L2_wf ds_d2zO ∧ True):
  {VV: _ | length2_rel ds_d2zO VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, length2_rel ds_d2zO VV) (length2 (exist _ ds_d2zO ds_d2zO_p)) _);
  rewrite <- length2__length2_rel';
  quicksolve.
Qed.

#[global] Hint Resolve length2_rel_mk: f_rel_funct_db.

#[global] Instance length2_pack:
  @Pack
  (L2 ::RT λ (ds_d2zO : L2), nilRT)
  (L2_u ::UT nilUT)
  ltac:(mkProjectsArgListTG (L2 ::RT λ (ds_d2zO : L2), nilRT) ((L2_u ::UT nilUT)))
  Nats_u
  (λ (x_63136410 : ArgList (L2 ::RT λ (ds_d2zO : L2), nilRT)) (v_x_63136410 : Nats_u),
   ltac:(flattenP (λ (ds_d2zO : L2) (VV : Nats_u), Nats_wf VV ∧ True) x_63136410 v_x_63136410)).
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

Definition unzip_spec (ds_d2zU : L2): Type :=
  PairL.

#[global] Hint Unfold unzip_spec: lia_unfold.

Definition unzip (ds_d2zU : L2): unzip_spec ds_d2zU.
Proof.
  destruct ds_d2zU as [ds_d2zU ds_d2zU_p].
  induction ds_d2zU as [ds_d2A4 l IH_l|].
  - destruct ds_d2A4 as [x y].
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

Definition append_spec (ds_d2AP ys : L): Type :=
  L.

#[global] Hint Unfold append_spec: lia_unfold.

Definition append (ds_d2AP ys : L): append_spec ds_d2AP ys.
Proof.
  destruct ds_d2AP as [ds_d2AP ds_d2AP_p].
  destruct ys as [ys ys_p].
  try revert ys_p; generalize dependent ys; induction ds_d2AP as [x xs IH_xs|]; intros.
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

Theorem append_rel_funct [ds_d2AP ys : L_u]:
  ∀ (VV VV' : L_u), append_rel ds_d2AP ys VV → (append_rel ds_d2AP ys VV' → VV = VV').
Proof.
  try revert ys_p; generalize dependent ys; induction ds_d2AP as [x xs IH_xs|]; intros;
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
  (ds_d2AP : L_u) (ds_d2AP_p : L_wf ds_d2AP ∧ True) (ys : L_u) (ys_p : L_wf ys ∧ True):
  append_rel ds_d2AP ys ⌊ append (exist _ ds_d2AP ds_d2AP_p) (exist _ ys ys_p) -⌋.
Proof.
  Opaque append.
  existence_lemma_pre append;
  try revert ys_p; generalize dependent ys; induction ds_d2AP as [x xs IH_xs|]; intros;
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
  (ds_d2AP : L_u) (ds_d2AP_p : L_wf ds_d2AP ∧ True) (ys : L_u) (ys_p : L_wf ys ∧ True) (VV : L_u):
  ⌊ append (exist _ ds_d2AP ds_d2AP_p) (exist _ ys ys_p) -⌋ = VV ↔ append_rel ds_d2AP ys VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite append__append_rel_rw: f_rel_funct_db.

#[global] Hint Resolve append__append_rel_rw: rel_ax_db.

#[global] Instance append_lookup_rw: dictionary rwLem append := {
    lookup' := append__append_rel_rw }.

Theorem append__append_rel (ds_d2AP ys : L) (VV : L_u):
  ⌊ append ds_d2AP ys -⌋ = VV ↔ append_rel ⌊ ds_d2AP ⌋ ⌊ ys ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite append__append_rel: f_rel_funct_db.

Theorem append__append_rel' (ds_d2AP_u ys_u : L_u) (ds_d2AP ys : L) (VV : L_u):
  ds_d2AP_u = ⌊ ds_d2AP ⌋
  → (ys_u = ⌊ ys ⌋ → ⌊ append ds_d2AP ys -⌋ = VV ↔ append_rel ds_d2AP_u ys_u VV).
Proof.
  intros -> ->. refine (append__append_rel ds_d2AP ys VV).
Qed.

#[global] Hint Resolve append__append_rel': f_rel_funct_db.

Theorem append_rel_mk
  (ds_d2AP : L_u) (ds_d2AP_p : L_wf ds_d2AP ∧ True) (ys : L_u) (ys_p : L_wf ys ∧ True):
  {VV: _ | append_rel ds_d2AP ys VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, append_rel ds_d2AP ys VV)
          (append (exist _ ds_d2AP ds_d2AP_p) (exist _ ys ys_p))
          _);
  rewrite <- append__append_rel';
  quicksolve.
Qed.

#[global] Hint Resolve append_rel_mk: f_rel_funct_db.

#[global] Instance append_pack:
  @Pack
  (L ::RT λ (ds_d2AP : L), L ::RT λ (ys : L), nilRT)
  (L_u ::UT (L_u ::UT nilUT))
  ltac:(mkProjectsArgListTG (L ::RT λ (ds_d2AP : L), L ::RT λ (ys : L), nilRT) ((L_u ::UT (L_u ::UT nilUT))))
  L_u
  (λ (x_82774912 : ArgList (L ::RT λ (ds_d2AP : L), L ::RT λ (ys : L), nilRT)) (v_x_82774912 : L_u),
   ltac:(flattenP (λ (ds_d2AP ys : L) (VV : L_u), L_wf VV ∧ True) x_82774912 v_x_82774912)).
Proof.
  buildPackG append append_rel append__append_rel append_rel_funct.
Defined.

#[global] Instance append_upack: @uPack (L_u ::UT (L_u ::UT nilUT)) L_u.
Proof.
  buildUPackG append_rel append_rel_funct.
Defined.

Definition append_nonempty_xs_spec
  (ds_d2Ay ds_d2Az : L)
  (ds_d2AA : {{∃ (append_res : L_u),
               append_rel ⌊ ds_d2Ay -⌋ ⌊ ds_d2Az -⌋ append_res ∧ append_res == Emp_u}}):
  Type :=
  {{⌊ ds_d2Ay -⌋ == Emp_u}}.

#[global] Hint Unfold append_nonempty_xs_spec: lia_unfold.

Theorem append_nonempty_xs
  (ds_d2Ay ds_d2Az : L)
  (ds_d2AA : {{∃ (append_res : L_u),
               append_rel ⌊ ds_d2Ay -⌋ ⌊ ds_d2Az -⌋ append_res ∧ append_res == Emp_u}}):
  append_nonempty_xs_spec ds_d2Ay ds_d2Az ds_d2AA.
Proof.
  destruct ds_d2Ay as [ds_d2Ay ds_d2Ay_p].
  destruct ds_d2Az as [ds_d2Az ds_d2Az_p].
  destruct ds_d2AA as [ds_d2AA ds_d2AA_p].
  destruct ds_d2Ay as [lq_anf7205759403792803719 lq_anf7205759403792803720|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), App_u lq_anf7205759403792803719 lq_anf7205759403792803720 == Emp_u)
            (exist (λ (ds_d2AA : Unit),
                    ∃ (append_res : L_u),
                    append_rel (App_u lq_anf7205759403792803719 lq_anf7205759403792803720) ds_d2Az append_res
                    ∧ append_res == Emp_u) ds_d2AA ltac:(solver))
            ltac:(solver)).
  - destruct ds_d2Az as [lq_anf7205759403792803717 lq_anf7205759403792803718|].
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit), Emp_u == Emp_u)
              (exist (λ (ds_d2AA : Unit),
                      ∃ (append_res : L_u),
                      append_rel Emp_u (App_u lq_anf7205759403792803717 lq_anf7205759403792803718) append_res
                      ∧ append_res == Emp_u) ds_d2AA ltac:(solver))
              ltac:(solver)).
    + refine (subsumptionCast Unit (λ (VV : Unit), Emp_u == Emp_u) (# unit) ltac:(solver)).
Qed.

Definition append_nonempty_ys_spec
  (ds_d2AF ds_d2AG : L)
  (ds_d2AH : {{∃ (append_res : L_u),
               append_rel ⌊ ds_d2AF -⌋ ⌊ ds_d2AG -⌋ append_res ∧ append_res == Emp_u}}):
  Type :=
  {{⌊ ds_d2AG -⌋ == Emp_u}}.

#[global] Hint Unfold append_nonempty_ys_spec: lia_unfold.

Theorem append_nonempty_ys
  (ds_d2AF ds_d2AG : L)
  (ds_d2AH : {{∃ (append_res : L_u),
               append_rel ⌊ ds_d2AF -⌋ ⌊ ds_d2AG -⌋ append_res ∧ append_res == Emp_u}}):
  append_nonempty_ys_spec ds_d2AF ds_d2AG ds_d2AH.
Proof.
  destruct ds_d2AF as [ds_d2AF ds_d2AF_p].
  destruct ds_d2AG as [ds_d2AG ds_d2AG_p].
  destruct ds_d2AH as [ds_d2AH ds_d2AH_p].
  destruct ds_d2AF as [lq_anf7205759403792803710 lq_anf7205759403792803711|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ds_d2AG == Emp_u)
            (exist (λ (ds_d2AH : Unit),
                    ∃ (append_res : L_u),
                    append_rel (App_u lq_anf7205759403792803710 lq_anf7205759403792803711) ds_d2AG append_res
                    ∧ append_res == Emp_u) ds_d2AH ltac:(solver))
            ltac:(solver)).
  - destruct ds_d2AG as [lq_anf7205759403792803708 lq_anf7205759403792803709|].
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit), App_u lq_anf7205759403792803708 lq_anf7205759403792803709 == Emp_u)
              (exist (λ (ds_d2AH : Unit),
                      ∃ (append_res : L_u),
                      append_rel Emp_u (App_u lq_anf7205759403792803708 lq_anf7205759403792803709) append_res
                      ∧ append_res == Emp_u) ds_d2AH ltac:(solver))
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
  (ds_d2AS : L):
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
  (ds_d2AS : L):
  concatMap_spec f ds_d2AS.
Proof.
  destruct ds_d2AS as [ds_d2AS ds_d2AS_p].
  try revert f_p; generalize dependent f; induction ds_d2AS as [x xs IH_xs|]; intros.
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

Theorem concatMap_rel_funct [f : @uPack (Z ::UT nilUT) L_u] [ds_d2AS : L_u]:
  ∀ (VV VV' : L_u), concatMap_rel f ds_d2AS VV → (concatMap_rel f ds_d2AS VV' → VV = VV').
Proof.
  try revert f_p; generalize dependent f; induction ds_d2AS as [x xs IH_xs|]; intros;
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
  (ds_d2AS : L_u)
  (ds_d2AS_p : L_wf ds_d2AS ∧ True):
  concatMap_rel ⌊ f ⌋ ds_d2AS ⌊ concatMap f (exist _ ds_d2AS ds_d2AS_p) -⌋.
Proof.
  Opaque concatMap.
  existence_lemma_pre concatMap;
  try revert f_p; generalize dependent f; induction ds_d2AS as [x xs IH_xs|]; intros;
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
  (ds_d2AS : L_u)
  (ds_d2AS_p : L_wf ds_d2AS ∧ True)
  (VV : L_u):
  ⌊ concatMap f (exist _ ds_d2AS ds_d2AS_p) -⌋ = VV ↔ concatMap_rel ⌊ f ⌋ ds_d2AS VV.
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
  (ds_d2AS : L)
  (VV : L_u):
  ⌊ concatMap f ds_d2AS -⌋ = VV ↔ concatMap_rel ⌊ f ⌋ ⌊ ds_d2AS ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite concatMap__concatMap_rel: f_rel_funct_db.

Theorem concatMap__concatMap_rel'
  (f_u : @uPack (Z ::UT nilUT) L_u)
  (ds_d2AS_u : L_u)
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT nilUT)))
       L_u
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : L_u),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : L_u), L_wf VV ∧ True) x_40877513 v_x_40877513)))
  (ds_d2AS : L)
  (VV : L_u):
  f_u = ⌊ f ⌋
  → (ds_d2AS_u = ⌊ ds_d2AS ⌋ → ⌊ concatMap f ds_d2AS -⌋ = VV ↔ concatMap_rel f_u ds_d2AS_u VV).
Proof.
  intros -> ->. refine (concatMap__concatMap_rel f ds_d2AS VV).
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
  (ds_d2AS : L_u)
  (ds_d2AS_p : L_wf ds_d2AS ∧ True):
  {VV: _ | concatMap_rel (packProj f) ds_d2AS VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, concatMap_rel (packProj f) ds_d2AS VV)
          (concatMap f (exist _ ds_d2AS ds_d2AS_p))
          _);
  rewrite <- concatMap__concatMap_rel';
  quicksolve.
Qed.

#[global] Hint Resolve concatMap_rel_mk: f_rel_funct_db.

Definition l2_pr1_spec (ds_d2zy : L2): Type :=
  L.

#[global] Hint Unfold l2_pr1_spec: lia_unfold.

Definition l2_pr1 (ds_d2zy : L2): l2_pr1_spec ds_d2zy.
Proof.
  destruct ds_d2zy as [ds_d2zy ds_d2zy_p].
  induction ds_d2zy as [ds_d2zB l IH_l|].
  - destruct ds_d2zB as [x ds_d2zC].
    + refine (App (# x) (IH_l ltac:(try clear IH_l; solver))).
  - refine Emp.
Defined.

Inductive l2_pr1_rel: L2_u → L_u → Prop :=
  | l2_pr1__App2_MkPair_x: ∀ ds_d2zC l x (l2_pr1_res : L_u),
                           l2_pr1_rel l l2_pr1_res → l2_pr1_rel (App2_u (MkPair_u x ds_d2zC) l) (App_u x l2_pr1_res)
  | l2_pr1_Emp2: l2_pr1_rel Emp2_u Emp_u.

#[global] Hint Constructors l2_pr1_rel: core_hint_db.

#[global] Instance l2_pr1_lookup_rel: dictionary rel l2_pr1 := { lookup' := l2_pr1_rel }.

#[global] Instance l2_pr1_getF: getFunc l2_pr1_rel := { getF' := l2_pr1 }.

Theorem l2_pr1_rel_funct [ds_d2zy : L2_u]:
  ∀ (VV VV' : L_u), l2_pr1_rel ds_d2zy VV → (l2_pr1_rel ds_d2zy VV' → VV = VV').
Proof.
  induction ds_d2zy as [ds_d2zB l IH_l|];
  [destruct ds_d2zB as [x ds_d2zC] |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve l2_pr1_rel_funct: f_rel_funct_db.

#[global] Instance l2_pr1_lookup_funct: dictionary functionhood l2_pr1 := {
    lookup' := l2_pr1_rel_funct }.

Theorem l2_pr1__App2_MkPair_x_lem ds_d2zC l x l2_pr1__App2_MkPair_x_lem_res:
  l2_pr1_rel (App2_u (MkPair_u x ds_d2zC) l) l2_pr1__App2_MkPair_x_lem_res
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

Theorem l2_pr1_rel_ex (ds_d2zy : L2_u) (ds_d2zy_p : L2_wf ds_d2zy ∧ True):
  l2_pr1_rel ds_d2zy ⌊ l2_pr1 (exist _ ds_d2zy ds_d2zy_p) -⌋.
Proof.
  Opaque l2_pr1.
  existence_lemma_pre l2_pr1;
  induction ds_d2zy as [ds_d2zB l IH_l|];
  [destruct ds_d2zB as [x ds_d2zC];
   [fix_notations; pose proof (IH_l ltac:(try clear IH_l; solver)) as IH_26190279; try clear IH_l] |
   fix_notations];
  simpl in *.
  Transparent l2_pr1.
  all: (existence_lemma_quicksolve l2_pr1; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve l2_pr1_rel_ex: rel_ax_db.

#[global] Opaque l2_pr1.

Theorem l2_pr1__l2_pr1_rel_rw (ds_d2zy : L2_u) (ds_d2zy_p : L2_wf ds_d2zy ∧ True) (VV : L_u):
  ⌊ l2_pr1 (exist _ ds_d2zy ds_d2zy_p) -⌋ = VV ↔ l2_pr1_rel ds_d2zy VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite l2_pr1__l2_pr1_rel_rw: f_rel_funct_db.

#[global] Hint Resolve l2_pr1__l2_pr1_rel_rw: rel_ax_db.

#[global] Instance l2_pr1_lookup_rw: dictionary rwLem l2_pr1 := {
    lookup' := l2_pr1__l2_pr1_rel_rw }.

Theorem l2_pr1__l2_pr1_rel (ds_d2zy : L2) (VV : L_u):
  ⌊ l2_pr1 ds_d2zy -⌋ = VV ↔ l2_pr1_rel ⌊ ds_d2zy ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite l2_pr1__l2_pr1_rel: f_rel_funct_db.

Theorem l2_pr1__l2_pr1_rel' (ds_d2zy_u : L2_u) (ds_d2zy : L2) (VV : L_u):
  ds_d2zy_u = ⌊ ds_d2zy ⌋ → ⌊ l2_pr1 ds_d2zy -⌋ = VV ↔ l2_pr1_rel ds_d2zy_u VV.
Proof.
  intros ->. refine (l2_pr1__l2_pr1_rel ds_d2zy VV).
Qed.

#[global] Hint Resolve l2_pr1__l2_pr1_rel': f_rel_funct_db.

Theorem l2_pr1_rel_mk (ds_d2zy : L2_u) (ds_d2zy_p : L2_wf ds_d2zy ∧ True):
  {VV: _ | l2_pr1_rel ds_d2zy VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, l2_pr1_rel ds_d2zy VV) (l2_pr1 (exist _ ds_d2zy ds_d2zy_p)) _);
  rewrite <- l2_pr1__l2_pr1_rel';
  quicksolve.
Qed.

#[global] Hint Resolve l2_pr1_rel_mk: f_rel_funct_db.

#[global] Instance l2_pr1_pack:
  @Pack
  (L2 ::RT λ (ds_d2zy : L2), nilRT)
  (L2_u ::UT nilUT)
  ltac:(mkProjectsArgListTG (L2 ::RT λ (ds_d2zy : L2), nilRT) ((L2_u ::UT nilUT)))
  L_u
  (λ (x_36045560 : ArgList (L2 ::RT λ (ds_d2zy : L2), nilRT)) (v_x_36045560 : L_u),
   ltac:(flattenP (λ (ds_d2zy : L2) (VV : L_u), L_wf VV ∧ True) x_36045560 v_x_36045560)).
Proof.
  buildPackG l2_pr1 l2_pr1_rel l2_pr1__l2_pr1_rel l2_pr1_rel_funct.
Defined.

#[global] Instance l2_pr1_upack: @uPack (L2_u ::UT nilUT) L_u.
Proof.
  buildUPackG l2_pr1_rel l2_pr1_rel_funct.
Defined.

Definition l2_pr2_spec (ds_d2zt : L2): Type :=
  L.

#[global] Hint Unfold l2_pr2_spec: lia_unfold.

Definition l2_pr2 (ds_d2zt : L2): l2_pr2_spec ds_d2zt.
Proof.
  destruct ds_d2zt as [ds_d2zt ds_d2zt_p].
  induction ds_d2zt as [ds_d2zw l IH_l|].
  - destruct ds_d2zw as [ds_d2zx y].
    + refine (App (# y) (IH_l ltac:(try clear IH_l; solver))).
  - refine Emp.
Defined.

Inductive l2_pr2_rel: L2_u → L_u → Prop :=
  | l2_pr2__App2_MkPair_x: ∀ ds_d2zx l y (l2_pr2_res : L_u),
                           l2_pr2_rel l l2_pr2_res → l2_pr2_rel (App2_u (MkPair_u ds_d2zx y) l) (App_u y l2_pr2_res)
  | l2_pr2_Emp2: l2_pr2_rel Emp2_u Emp_u.

#[global] Hint Constructors l2_pr2_rel: core_hint_db.

#[global] Instance l2_pr2_lookup_rel: dictionary rel l2_pr2 := { lookup' := l2_pr2_rel }.

#[global] Instance l2_pr2_getF: getFunc l2_pr2_rel := { getF' := l2_pr2 }.

Theorem l2_pr2_rel_funct [ds_d2zt : L2_u]:
  ∀ (VV VV' : L_u), l2_pr2_rel ds_d2zt VV → (l2_pr2_rel ds_d2zt VV' → VV = VV').
Proof.
  induction ds_d2zt as [ds_d2zw l IH_l|];
  [destruct ds_d2zw as [ds_d2zx y] |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve l2_pr2_rel_funct: f_rel_funct_db.

#[global] Instance l2_pr2_lookup_funct: dictionary functionhood l2_pr2 := {
    lookup' := l2_pr2_rel_funct }.

Theorem l2_pr2__App2_MkPair_x_lem ds_d2zx l y l2_pr2__App2_MkPair_x_lem_res:
  l2_pr2_rel (App2_u (MkPair_u ds_d2zx y) l) l2_pr2__App2_MkPair_x_lem_res
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

Theorem l2_pr2_rel_ex (ds_d2zt : L2_u) (ds_d2zt_p : L2_wf ds_d2zt ∧ True):
  l2_pr2_rel ds_d2zt ⌊ l2_pr2 (exist _ ds_d2zt ds_d2zt_p) -⌋.
Proof.
  Opaque l2_pr2.
  existence_lemma_pre l2_pr2;
  induction ds_d2zt as [ds_d2zw l IH_l|];
  [destruct ds_d2zw as [ds_d2zx y];
   [fix_notations; pose proof (IH_l ltac:(try clear IH_l; solver)) as IH_26190279; try clear IH_l] |
   fix_notations];
  simpl in *.
  Transparent l2_pr2.
  all: (existence_lemma_quicksolve l2_pr2; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve l2_pr2_rel_ex: rel_ax_db.

#[global] Opaque l2_pr2.

Theorem l2_pr2__l2_pr2_rel_rw (ds_d2zt : L2_u) (ds_d2zt_p : L2_wf ds_d2zt ∧ True) (VV : L_u):
  ⌊ l2_pr2 (exist _ ds_d2zt ds_d2zt_p) -⌋ = VV ↔ l2_pr2_rel ds_d2zt VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite l2_pr2__l2_pr2_rel_rw: f_rel_funct_db.

#[global] Hint Resolve l2_pr2__l2_pr2_rel_rw: rel_ax_db.

#[global] Instance l2_pr2_lookup_rw: dictionary rwLem l2_pr2 := {
    lookup' := l2_pr2__l2_pr2_rel_rw }.

Theorem l2_pr2__l2_pr2_rel (ds_d2zt : L2) (VV : L_u):
  ⌊ l2_pr2 ds_d2zt -⌋ = VV ↔ l2_pr2_rel ⌊ ds_d2zt ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite l2_pr2__l2_pr2_rel: f_rel_funct_db.

Theorem l2_pr2__l2_pr2_rel' (ds_d2zt_u : L2_u) (ds_d2zt : L2) (VV : L_u):
  ds_d2zt_u = ⌊ ds_d2zt ⌋ → ⌊ l2_pr2 ds_d2zt -⌋ = VV ↔ l2_pr2_rel ds_d2zt_u VV.
Proof.
  intros ->. refine (l2_pr2__l2_pr2_rel ds_d2zt VV).
Qed.

#[global] Hint Resolve l2_pr2__l2_pr2_rel': f_rel_funct_db.

Theorem l2_pr2_rel_mk (ds_d2zt : L2_u) (ds_d2zt_p : L2_wf ds_d2zt ∧ True):
  {VV: _ | l2_pr2_rel ds_d2zt VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, l2_pr2_rel ds_d2zt VV) (l2_pr2 (exist _ ds_d2zt ds_d2zt_p)) _);
  rewrite <- l2_pr2__l2_pr2_rel';
  quicksolve.
Qed.

#[global] Hint Resolve l2_pr2_rel_mk: f_rel_funct_db.

#[global] Instance l2_pr2_pack:
  @Pack
  (L2 ::RT λ (ds_d2zt : L2), nilRT)
  (L2_u ::UT nilUT)
  ltac:(mkProjectsArgListTG (L2 ::RT λ (ds_d2zt : L2), nilRT) ((L2_u ::UT nilUT)))
  L_u
  (λ (x_59981671 : ArgList (L2 ::RT λ (ds_d2zt : L2), nilRT)) (v_x_59981671 : L_u),
   ltac:(flattenP (λ (ds_d2zt : L2) (VV : L_u), L_wf VV ∧ True) x_59981671 v_x_59981671)).
Proof.
  buildPackG l2_pr2 l2_pr2_rel l2_pr2__l2_pr2_rel l2_pr2_rel_funct.
Defined.

#[global] Instance l2_pr2_upack: @uPack (L2_u ::UT nilUT) L_u.
Proof.
  buildUPackG l2_pr2_rel l2_pr2_rel_funct.
Defined.

Definition length_spec (ds_d2zR : L): Type :=
  Nats.

#[global] Hint Unfold length_spec: lia_unfold.

Definition length (ds_d2zR : L): length_spec ds_d2zR.
Proof.
  destruct ds_d2zR as [ds_d2zR ds_d2zR_p].
  induction ds_d2zR as [ds_d2zT xs IH_xs|].
  - refine (Suc (IH_xs ltac:(try clear IH_xs; solver))).
  - refine Zero.
Defined.

Inductive length_rel: L_u → Nats_u → Prop :=
  | length_App: ∀ ds_d2zT xs (length_res : Nats_u),
                length_rel xs length_res → length_rel (App_u ds_d2zT xs) (Suc_u length_res)
  | length_Emp: length_rel Emp_u Zero_u.

#[global] Hint Constructors length_rel: core_hint_db.

#[global] Instance length_lookup_rel: dictionary rel length := { lookup' := length_rel }.

#[global] Instance length_getF: getFunc length_rel := { getF' := length }.

Theorem length_rel_funct [ds_d2zR : L_u]:
  ∀ (VV VV' : Nats_u), length_rel ds_d2zR VV → (length_rel ds_d2zR VV' → VV = VV').
Proof.
  induction ds_d2zR as [ds_d2zT xs IH_xs|]; rel_functionhood_body.
Qed.

#[global] Hint Resolve length_rel_funct: f_rel_funct_db.

#[global] Instance length_lookup_funct: dictionary functionhood length := {
    lookup' := length_rel_funct }.

Theorem length_App_lem ds_d2zT xs length_App_lem_res:
  length_rel (App_u ds_d2zT xs) length_App_lem_res
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

Theorem length_rel_ex (ds_d2zR : L_u) (ds_d2zR_p : L_wf ds_d2zR ∧ True):
  length_rel ds_d2zR ⌊ length (exist _ ds_d2zR ds_d2zR_p) -⌋.
Proof.
  Opaque length.
  existence_lemma_pre length;
  induction ds_d2zR as [ds_d2zT xs IH_xs|];
  [fix_notations; pose proof (IH_xs ltac:(try clear IH_xs; solver)) as IH_67415571; try clear IH_xs |
   fix_notations];
  simpl in *.
  Transparent length.
  all: (existence_lemma_quicksolve length; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve length_rel_ex: rel_ax_db.

#[global] Opaque length.

Theorem length__length_rel_rw (ds_d2zR : L_u) (ds_d2zR_p : L_wf ds_d2zR ∧ True) (VV : Nats_u):
  ⌊ length (exist _ ds_d2zR ds_d2zR_p) -⌋ = VV ↔ length_rel ds_d2zR VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite length__length_rel_rw: f_rel_funct_db.

#[global] Hint Resolve length__length_rel_rw: rel_ax_db.

#[global] Instance length_lookup_rw: dictionary rwLem length := {
    lookup' := length__length_rel_rw }.

Theorem length__length_rel (ds_d2zR : L) (VV : Nats_u):
  ⌊ length ds_d2zR -⌋ = VV ↔ length_rel ⌊ ds_d2zR ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite length__length_rel: f_rel_funct_db.

Theorem length__length_rel' (ds_d2zR_u : L_u) (ds_d2zR : L) (VV : Nats_u):
  ds_d2zR_u = ⌊ ds_d2zR ⌋ → ⌊ length ds_d2zR -⌋ = VV ↔ length_rel ds_d2zR_u VV.
Proof.
  intros ->. refine (length__length_rel ds_d2zR VV).
Qed.

#[global] Hint Resolve length__length_rel': f_rel_funct_db.

Theorem length_rel_mk (ds_d2zR : L_u) (ds_d2zR_p : L_wf ds_d2zR ∧ True):
  {VV: _ | length_rel ds_d2zR VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, length_rel ds_d2zR VV) (length (exist _ ds_d2zR ds_d2zR_p)) _);
  rewrite <- length__length_rel';
  quicksolve.
Qed.

#[global] Hint Resolve length_rel_mk: f_rel_funct_db.

#[global] Instance length_pack:
  @Pack
  (L ::RT λ (ds_d2zR : L), nilRT)
  (L_u ::UT nilUT)
  ltac:(mkProjectsArgListTG (L ::RT λ (ds_d2zR : L), nilRT) ((L_u ::UT nilUT)))
  Nats_u
  (λ (x_88816125 : ArgList (L ::RT λ (ds_d2zR : L), nilRT)) (v_x_88816125 : Nats_u),
   ltac:(flattenP (λ (ds_d2zR : L) (VV : Nats_u), Nats_wf VV ∧ True) x_88816125 v_x_88816125)).
Proof.
  buildPackG length length_rel length__length_rel length_rel_funct.
Defined.

#[global] Instance length_upack: @uPack (L_u ::UT nilUT) Nats_u.
Proof.
  buildUPackG length_rel length_rel_funct.
Defined.

Definition length_unzip_1_spec (ds_d2zr : L2): Type :=
  {{∃ (length2_res : Nats_u),
    length2_rel ⌊ ds_d2zr -⌋ length2_res
    ∧ ∃ (l2_pr1_res : L_u),
      l2_pr1_rel ⌊ ds_d2zr -⌋ l2_pr1_res
      ∧ ∃ (length_res : Nats_u), length_rel l2_pr1_res length_res ∧ length2_res == length_res}}.

#[global] Hint Unfold length_unzip_1_spec: lia_unfold.

Theorem length_unzip_1 (ds_d2zr : L2): length_unzip_1_spec ds_d2zr.
Proof.
  destruct ds_d2zr as [ds_d2zr ds_d2zr_p].
  induction ds_d2zr as [ds_d2zs l IH_l|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (length2_res : Nats_u),
             length2_rel (App2_u ds_d2zs l) length2_res
             ∧ ∃ (l2_pr1_res : L_u),
               l2_pr1_rel (App2_u ds_d2zs l) l2_pr1_res
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

Definition length_unzip_2_spec (ds_d2zp : L2): Type :=
  {{∃ (length2_res : Nats_u),
    length2_rel ⌊ ds_d2zp -⌋ length2_res
    ∧ ∃ (l2_pr2_res : L_u),
      l2_pr2_rel ⌊ ds_d2zp -⌋ l2_pr2_res
      ∧ ∃ (length_res : Nats_u), length_rel l2_pr2_res length_res ∧ length2_res == length_res}}.

#[global] Hint Unfold length_unzip_2_spec: lia_unfold.

Theorem length_unzip_2 (ds_d2zp : L2): length_unzip_2_spec ds_d2zp.
Proof.
  destruct ds_d2zp as [ds_d2zp ds_d2zp_p].
  induction ds_d2zp as [ds_d2zq l IH_l|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (length2_res : Nats_u),
             length2_rel (App2_u ds_d2zq l) length2_res
             ∧ ∃ (l2_pr2_res : L_u),
               l2_pr2_rel (App2_u ds_d2zq l) l2_pr2_res
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
  (ds_d2AM : L):
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
  (ds_d2AM : L):
  map_spec f ds_d2AM.
Proof.
  destruct ds_d2AM as [ds_d2AM ds_d2AM_p].
  try revert f_p; generalize dependent f; induction ds_d2AM as [x xs IH_xs|]; intros.
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

Theorem map_rel_funct [f : @uPack (Z ::UT nilUT) Z] [ds_d2AM : L_u]:
  ∀ (VV VV' : L_u), map_rel f ds_d2AM VV → (map_rel f ds_d2AM VV' → VV = VV').
Proof.
  try revert f_p; generalize dependent f; induction ds_d2AM as [x xs IH_xs|]; intros;
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
  (ds_d2AM : L_u)
  (ds_d2AM_p : L_wf ds_d2AM ∧ True):
  map_rel ⌊ f ⌋ ds_d2AM ⌊ map f (exist _ ds_d2AM ds_d2AM_p) -⌋.
Proof.
  Opaque map.
  existence_lemma_pre map;
  try revert f_p; generalize dependent f; induction ds_d2AM as [x xs IH_xs|]; intros;
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
  (ds_d2AM : L_u)
  (ds_d2AM_p : L_wf ds_d2AM ∧ True)
  (VV : L_u):
  ⌊ map f (exist _ ds_d2AM ds_d2AM_p) -⌋ = VV ↔ map_rel ⌊ f ⌋ ds_d2AM VV.
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
  (ds_d2AM : L)
  (VV : L_u):
  ⌊ map f ds_d2AM -⌋ = VV ↔ map_rel ⌊ f ⌋ ⌊ ds_d2AM ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite map__map_rel: f_rel_funct_db.

Theorem map__map_rel'
  (f_u : @uPack (Z ::UT nilUT) Z)
  (ds_d2AM_u : L_u)
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT nilUT)))
       Z
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513)))
  (ds_d2AM : L)
  (VV : L_u):
  f_u = ⌊ f ⌋ → (ds_d2AM_u = ⌊ ds_d2AM ⌋ → ⌊ map f ds_d2AM -⌋ = VV ↔ map_rel f_u ds_d2AM_u VV).
Proof.
  intros -> ->. refine (map__map_rel f ds_d2AM VV).
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
  (ds_d2AM : L_u)
  (ds_d2AM_p : L_wf ds_d2AM ∧ True):
  {VV: _ | map_rel (packProj f) ds_d2AM VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, map_rel (packProj f) ds_d2AM VV)
          (map f (exist _ ds_d2AM ds_d2AM_p))
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
  (ds_d2zN : L):
  Type :=
  {{∃ (map_res : L_u),
    map_rel ⌊ f ⌋ ⌊ ds_d2zN -⌋ map_res
    ∧ ∃ (length_res : Nats_u),
      length_rel map_res length_res
      ∧ ∃ (length_res_2 : Nats_u), length_rel ⌊ ds_d2zN -⌋ length_res_2 ∧ length_res == length_res_2}}.

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
  (ds_d2zN : L):
  length_map_spec f ds_d2zN.
Proof.
  destruct ds_d2zN as [ds_d2zN ds_d2zN_p].
  try revert f_p; generalize dependent f; induction ds_d2zN as [x xs IH_xs|]; intros.
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

Definition reverse_spec (ds_d2AT : L): Type :=
  L.

#[global] Hint Unfold reverse_spec: lia_unfold.

Definition reverse (ds_d2AT : L): reverse_spec ds_d2AT.
Proof.
  destruct ds_d2AT as [ds_d2AT ds_d2AT_p].
  induction ds_d2AT as [x xs IH_xs|].
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

Theorem reverse_rel_funct [ds_d2AT : L_u]:
  ∀ (VV VV' : L_u), reverse_rel ds_d2AT VV → (reverse_rel ds_d2AT VV' → VV = VV').
Proof.
  induction ds_d2AT as [x xs IH_xs|]; rel_functionhood_body.
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

Theorem reverse_rel_ex (ds_d2AT : L_u) (ds_d2AT_p : L_wf ds_d2AT ∧ True):
  reverse_rel ds_d2AT ⌊ reverse (exist _ ds_d2AT ds_d2AT_p) -⌋.
Proof.
  Opaque reverse.
  existence_lemma_pre reverse;
  induction ds_d2AT as [x xs IH_xs|];
  [fix_notations; pose proof (IH_xs ltac:(try clear IH_xs; solver)) as IH_67415571; try clear IH_xs |
   fix_notations];
  simpl in *.
  Transparent reverse.
  all: (existence_lemma_quicksolve reverse; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve reverse_rel_ex: rel_ax_db.

#[global] Opaque reverse.

Theorem reverse__reverse_rel_rw (ds_d2AT : L_u) (ds_d2AT_p : L_wf ds_d2AT ∧ True) (VV : L_u):
  ⌊ reverse (exist _ ds_d2AT ds_d2AT_p) -⌋ = VV ↔ reverse_rel ds_d2AT VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite reverse__reverse_rel_rw: f_rel_funct_db.

#[global] Hint Resolve reverse__reverse_rel_rw: rel_ax_db.

#[global] Instance reverse_lookup_rw: dictionary rwLem reverse := {
    lookup' := reverse__reverse_rel_rw }.

Theorem reverse__reverse_rel (ds_d2AT : L) (VV : L_u):
  ⌊ reverse ds_d2AT -⌋ = VV ↔ reverse_rel ⌊ ds_d2AT ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite reverse__reverse_rel: f_rel_funct_db.

Theorem reverse__reverse_rel' (ds_d2AT_u : L_u) (ds_d2AT : L) (VV : L_u):
  ds_d2AT_u = ⌊ ds_d2AT ⌋ → ⌊ reverse ds_d2AT -⌋ = VV ↔ reverse_rel ds_d2AT_u VV.
Proof.
  intros ->. refine (reverse__reverse_rel ds_d2AT VV).
Qed.

#[global] Hint Resolve reverse__reverse_rel': f_rel_funct_db.

Theorem reverse_rel_mk (ds_d2AT : L_u) (ds_d2AT_p : L_wf ds_d2AT ∧ True):
  {VV: _ | reverse_rel ds_d2AT VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, reverse_rel ds_d2AT VV) (reverse (exist _ ds_d2AT ds_d2AT_p)) _);
  rewrite <- reverse__reverse_rel';
  quicksolve.
Qed.

#[global] Hint Resolve reverse_rel_mk: f_rel_funct_db.

#[global] Instance reverse_pack:
  @Pack
  (L ::RT λ (ds_d2AT : L), nilRT)
  (L_u ::UT nilUT)
  ltac:(mkProjectsArgListTG (L ::RT λ (ds_d2AT : L), nilRT) ((L_u ::UT nilUT)))
  L_u
  (λ (x_71261062 : ArgList (L ::RT λ (ds_d2AT : L), nilRT)) (v_x_71261062 : L_u),
   ltac:(flattenP (λ (ds_d2AT : L) (VV : L_u), L_wf VV ∧ True) x_71261062 v_x_71261062)).
Proof.
  buildPackG reverse reverse_rel reverse__reverse_rel reverse_rel_funct.
Defined.

#[global] Instance reverse_upack: @uPack (L_u ::UT nilUT) L_u.
Proof.
  buildUPackG reverse_rel reverse_rel_funct.
Defined.

Definition reverse_nonempty_spec
  (ds_d2AW : L)
  (ds_d2AX : {{∃ (reverse_res : L_u), reverse_rel ⌊ ds_d2AW -⌋ reverse_res ∧ reverse_res == Emp_u}}):
  Type :=
  {{⌊ ds_d2AW -⌋ == Emp_u}}.

#[global] Hint Unfold reverse_nonempty_spec: lia_unfold.

Theorem reverse_nonempty
  (ds_d2AW : L)
  (ds_d2AX : {{∃ (reverse_res : L_u), reverse_rel ⌊ ds_d2AW -⌋ reverse_res ∧ reverse_res == Emp_u}}):
  reverse_nonempty_spec ds_d2AW ds_d2AX.
Proof.
  destruct ds_d2AW as [ds_d2AW ds_d2AW_p].
  destruct ds_d2AX as [ds_d2AX ds_d2AX_p].
  destruct ds_d2AW as [x xs|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), App_u x xs == Emp_u)
            (append_nonempty_ys
             (reverse (exist (λ (VV : L_u), L_wf VV ∧ True) xs ltac:(solver)))
             (App (# x) Emp)
             (subsumptionCast
              Unit
              (λ (ds_d2AH : Unit),
               ∃ (append_res : L_u),
               append_rel
               ⌊ reverse (exist (λ (VV : L_u), L_wf VV ∧ True) xs ltac:(solver)) -⌋
               (App_u x Emp_u)
               append_res
               ∧ append_res == Emp_u)
              (exist (λ (ds_d2AX : Unit),
                      ∃ (reverse_res : L_u),
                      reverse_rel (App_u x xs) reverse_res ∧ reverse_res == Emp_u) ds_d2AX ltac:(solver))
              ltac:(solver)))
            ltac:(solver)).
  - refine (subsumptionCast Unit (λ (VV : Unit), Emp_u == Emp_u) (# unit) ltac:(solver)).
Qed.

Definition take_spec (ds_d2zf : Nats) (ds_d2zg : L): Type :=
  L.

#[global] Hint Unfold take_spec: lia_unfold.

Definition take (ds_d2zf : Nats) (ds_d2zg : L): take_spec ds_d2zf ds_d2zg.
Proof.
  destruct ds_d2zf as [ds_d2zf ds_d2zf_p].
  destruct ds_d2zg as [ds_d2zg ds_d2zg_p].
  try revert ds_d2zg_p; generalize dependent ds_d2zg;
  induction ds_d2zf as [lq_anf7205759403792803826 IH_lq_anf7205759403792803826|];
  intros.
  - destruct ds_d2zg as [lq_anf7205759403792803824 lq_anf7205759403792803825|].
    + refine (App
              (# lq_anf7205759403792803824)
              (IH_lq_anf7205759403792803826
               ltac:(try clear IH_lq_anf7205759403792803826; solver)
               lq_anf7205759403792803825
               ltac:(try clear IH_lq_anf7205759403792803826; solver))).
    + refine Emp.
  - refine Emp.
Defined.

Inductive take_rel: Nats_u → L_u → L_u → Prop :=
  | take_Suc_App: ∀ lq_anf7205759403792803826 lq_anf7205759403792803824 lq_anf7205759403792803825
                    (take_res : L_u),
                  take_rel lq_anf7205759403792803826 lq_anf7205759403792803825 take_res
                  → take_rel
                    (Suc_u lq_anf7205759403792803826)
                    (App_u lq_anf7205759403792803824 lq_anf7205759403792803825)
                    (App_u lq_anf7205759403792803824 take_res)
  | take_Suc_Emp: ∀ lq_anf7205759403792803826, take_rel (Suc_u lq_anf7205759403792803826) Emp_u Emp_u
  | take_Zero_x: ∀ ds_d2zg, take_rel Zero_u ds_d2zg Emp_u.

#[global] Hint Constructors take_rel: core_hint_db.

#[global] Instance take_lookup_rel: dictionary rel take := { lookup' := take_rel }.

#[global] Instance take_getF: getFunc take_rel := { getF' := take }.

Theorem take_rel_funct [ds_d2zf : Nats_u] [ds_d2zg : L_u]:
  ∀ (VV VV' : L_u), take_rel ds_d2zf ds_d2zg VV → (take_rel ds_d2zf ds_d2zg VV' → VV = VV').
Proof.
  try revert ds_d2zg_p; generalize dependent ds_d2zg;
  induction ds_d2zf as [lq_anf7205759403792803826 IH_lq_anf7205759403792803826|];
  intros;
  [destruct ds_d2zg as [lq_anf7205759403792803824 lq_anf7205759403792803825|] |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve take_rel_funct: f_rel_funct_db.

#[global] Instance take_lookup_funct: dictionary functionhood take := {
    lookup' := take_rel_funct }.

Theorem take_Suc_App_lem
  lq_anf7205759403792803824 lq_anf7205759403792803825 lq_anf7205759403792803826 take_Suc_App_lem_res:
  take_rel
  (Suc_u lq_anf7205759403792803826)
  (App_u lq_anf7205759403792803824 lq_anf7205759403792803825)
  take_Suc_App_lem_res
  ↔ ∃ (take_res : L_u),
    take_rel lq_anf7205759403792803826 lq_anf7205759403792803825 take_res
    ∧ take_Suc_App_lem_res == App_u lq_anf7205759403792803824 take_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite take_Suc_App_lem: f_rel_back.

Theorem take_Suc_Emp_lem lq_anf7205759403792803826 take_Suc_Emp_lem_res:
  take_rel (Suc_u lq_anf7205759403792803826) Emp_u take_Suc_Emp_lem_res
  ↔ take_Suc_Emp_lem_res == Emp_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite take_Suc_Emp_lem: f_rel_back.

Theorem take_Zero_x_lem ds_d2zg take_Zero_x_lem_res:
  take_rel Zero_u ds_d2zg take_Zero_x_lem_res ↔ take_Zero_x_lem_res == Emp_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite take_Zero_x_lem: f_rel_back.

Theorem take_rel_ex
  (ds_d2zf : Nats_u)
  (ds_d2zf_p : Nats_wf ds_d2zf ∧ True)
  (ds_d2zg : L_u)
  (ds_d2zg_p : L_wf ds_d2zg ∧ True):
  take_rel ds_d2zf ds_d2zg ⌊ take (exist _ ds_d2zf ds_d2zf_p) (exist _ ds_d2zg ds_d2zg_p) -⌋.
Proof.
  Opaque take.
  existence_lemma_pre take;
  try revert ds_d2zg_p; generalize dependent ds_d2zg;
  induction ds_d2zf as [lq_anf7205759403792803826 IH_lq_anf7205759403792803826|];
  intros;
  [destruct ds_d2zg as [lq_anf7205759403792803824 lq_anf7205759403792803825|];
   [fix_notations;
    pose proof (IH_lq_anf7205759403792803826
                ltac:(try clear IH_lq_anf7205759403792803826; solver)
                lq_anf7205759403792803825
                ltac:(try clear IH_lq_anf7205759403792803826; solver)) as IH_48654783;
    try clear IH_lq_anf7205759403792803826 |
    fix_notations] |
   fix_notations];
  simpl in *.
  Transparent take.
  all: (existence_lemma_quicksolve take; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve take_rel_ex: rel_ax_db.

#[global] Opaque take.

Theorem take__take_rel_rw
  (ds_d2zf : Nats_u)
  (ds_d2zf_p : Nats_wf ds_d2zf ∧ True)
  (ds_d2zg : L_u)
  (ds_d2zg_p : L_wf ds_d2zg ∧ True)
  (VV : L_u):
  ⌊ take (exist _ ds_d2zf ds_d2zf_p) (exist _ ds_d2zg ds_d2zg_p) -⌋ = VV
  ↔ take_rel ds_d2zf ds_d2zg VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite take__take_rel_rw: f_rel_funct_db.

#[global] Hint Resolve take__take_rel_rw: rel_ax_db.

#[global] Instance take_lookup_rw: dictionary rwLem take := { lookup' := take__take_rel_rw }.

Theorem take__take_rel (ds_d2zf : Nats) (ds_d2zg : L) (VV : L_u):
  ⌊ take ds_d2zf ds_d2zg -⌋ = VV ↔ take_rel ⌊ ds_d2zf ⌋ ⌊ ds_d2zg ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite take__take_rel: f_rel_funct_db.

Theorem take__take_rel'
  (ds_d2zf_u : Nats_u) (ds_d2zg_u : L_u) (ds_d2zf : Nats) (ds_d2zg : L) (VV : L_u):
  ds_d2zf_u = ⌊ ds_d2zf ⌋
  → (ds_d2zg_u = ⌊ ds_d2zg ⌋ → ⌊ take ds_d2zf ds_d2zg -⌋ = VV ↔ take_rel ds_d2zf_u ds_d2zg_u VV).
Proof.
  intros -> ->. refine (take__take_rel ds_d2zf ds_d2zg VV).
Qed.

#[global] Hint Resolve take__take_rel': f_rel_funct_db.

Theorem take_rel_mk
  (ds_d2zf : Nats_u)
  (ds_d2zf_p : Nats_wf ds_d2zf ∧ True)
  (ds_d2zg : L_u)
  (ds_d2zg_p : L_wf ds_d2zg ∧ True):
  {VV: _ | take_rel ds_d2zf ds_d2zg VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, take_rel ds_d2zf ds_d2zg VV)
          (take (exist _ ds_d2zf ds_d2zf_p) (exist _ ds_d2zg ds_d2zg_p))
          _);
  rewrite <- take__take_rel';
  quicksolve.
Qed.

#[global] Hint Resolve take_rel_mk: f_rel_funct_db.

#[global] Instance take_pack:
  @Pack
  (Nats ::RT λ (ds_d2zf : Nats), L ::RT λ (ds_d2zg : L), nilRT)
  (Nats_u ::UT (L_u ::UT nilUT))
  ltac:(mkProjectsArgListTG (Nats ::RT λ (ds_d2zf : Nats), L ::RT λ (ds_d2zg : L), nilRT) ((Nats_u ::UT (L_u ::UT nilUT))))
  L_u
  (λ (x_24057690 : ArgList (Nats ::RT λ (ds_d2zf : Nats), L ::RT λ (ds_d2zg : L), nilRT))
     (v_x_24057690 : L_u),
   ltac:(flattenP (λ (ds_d2zf : Nats) (ds_d2zg : L) (VV : L_u), L_wf VV ∧ True) x_24057690 v_x_24057690)).
Proof.
  buildPackG take take_rel take__take_rel take_rel_funct.
Defined.

#[global] Instance take_upack: @uPack (Nats_u ::UT (L_u ::UT nilUT)) L_u.
Proof.
  buildUPackG take_rel take_rel_funct.
Defined.

Definition take_all_spec
  (ds_d2z4 : Nats)
  (ds_d2z5 : {ds_d2z5: L_u | L_wf ds_d2z5
                             ∧ ∃ (length_res : Nats_u),
                               length_rel ds_d2z5 length_res
                               ∧ ∃ (geqN_res : bool), geqN_rel ⌊ ds_d2z4 -⌋ length_res geqN_res ∧ is_true geqN_res}):
  Type :=
  {{∃ (take_res : L_u), take_rel ⌊ ds_d2z4 -⌋ ⌊ ds_d2z5 -⌋ take_res ∧ take_res == ⌊ ds_d2z5 -⌋}}.

#[global] Hint Unfold take_all_spec: lia_unfold.

Theorem take_all
  (ds_d2z4 : Nats)
  (ds_d2z5 : {ds_d2z5: L_u | L_wf ds_d2z5
                             ∧ ∃ (length_res : Nats_u),
                               length_rel ds_d2z5 length_res
                               ∧ ∃ (geqN_res : bool), geqN_rel ⌊ ds_d2z4 -⌋ length_res geqN_res ∧ is_true geqN_res}):
  take_all_spec ds_d2z4 ds_d2z5.
Proof.
  destruct ds_d2z4 as [ds_d2z4 ds_d2z4_p].
  destruct ds_d2z5 as [ds_d2z5 ds_d2z5_p].
  try revert ds_d2z5_p; generalize dependent ds_d2z5; induction ds_d2z4 as [n IH_n|]; intros.
  - destruct ds_d2z5 as [x xs|].
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
  - destruct ds_d2z5 as [lq_anf7205759403792803875 lq_anf7205759403792803876|].
    + intros; exfalso; solver.
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit), ∃ (take_res : L_u), take_rel Zero_u Emp_u take_res ∧ take_res == Emp_u)
              (# unit)
              ltac:(solver)).
Qed.

Definition zip_spec (ds_d2Af ds_d2Ag : L): Type :=
  L2.

#[global] Hint Unfold zip_spec: lia_unfold.

Definition zip (ds_d2Af ds_d2Ag : L): zip_spec ds_d2Af ds_d2Ag.
Proof.
  destruct ds_d2Af as [ds_d2Af ds_d2Af_p].
  destruct ds_d2Ag as [ds_d2Ag ds_d2Ag_p].
  try revert ds_d2Ag_p; generalize dependent ds_d2Ag;
  induction ds_d2Af as [lq_anf7205759403792803735 lq_anf7205759403792803736 IH_lq_anf7205759403792803736|];
  intros.
  - destruct ds_d2Ag as [lq_anf7205759403792803733 lq_anf7205759403792803734|].
    + refine (App2
              (MkPair (# lq_anf7205759403792803735) (# lq_anf7205759403792803733))
              (IH_lq_anf7205759403792803736
               ltac:(try clear IH_lq_anf7205759403792803736; solver)
               lq_anf7205759403792803734
               ltac:(try clear IH_lq_anf7205759403792803736; solver))).
    + refine Emp2.
  - refine Emp2.
Defined.

Inductive zip_rel: L_u → L_u → L2_u → Prop :=
  | zip_App_App: ∀ lq_anf7205759403792803735 lq_anf7205759403792803736 lq_anf7205759403792803733 lq_anf7205759403792803734
                   (zip_res : L2_u),
                 zip_rel lq_anf7205759403792803736 lq_anf7205759403792803734 zip_res
                 → zip_rel
                   (App_u lq_anf7205759403792803735 lq_anf7205759403792803736)
                   (App_u lq_anf7205759403792803733 lq_anf7205759403792803734)
                   (App2_u (MkPair_u lq_anf7205759403792803735 lq_anf7205759403792803733) zip_res)
  | zip_App_Emp: ∀ lq_anf7205759403792803735 lq_anf7205759403792803736,
                 zip_rel (App_u lq_anf7205759403792803735 lq_anf7205759403792803736) Emp_u Emp2_u
  | zip_Emp_x: ∀ ds_d2Ag, zip_rel Emp_u ds_d2Ag Emp2_u.

#[global] Hint Constructors zip_rel: core_hint_db.

#[global] Instance zip_lookup_rel: dictionary rel zip := { lookup' := zip_rel }.

#[global] Instance zip_getF: getFunc zip_rel := { getF' := zip }.

Theorem zip_rel_funct [ds_d2Af ds_d2Ag : L_u]:
  ∀ (VV VV' : L2_u), zip_rel ds_d2Af ds_d2Ag VV → (zip_rel ds_d2Af ds_d2Ag VV' → VV = VV').
Proof.
  try revert ds_d2Ag_p; generalize dependent ds_d2Ag;
  induction ds_d2Af as [lq_anf7205759403792803735 lq_anf7205759403792803736 IH_lq_anf7205759403792803736|];
  intros;
  [destruct ds_d2Ag as [lq_anf7205759403792803733 lq_anf7205759403792803734|] |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve zip_rel_funct: f_rel_funct_db.

#[global] Instance zip_lookup_funct: dictionary functionhood zip := { lookup' := zip_rel_funct }.

Theorem zip_App_App_lem
  lq_anf7205759403792803733 lq_anf7205759403792803734 lq_anf7205759403792803735 lq_anf7205759403792803736 zip_App_App_lem_res:
  zip_rel
  (App_u lq_anf7205759403792803735 lq_anf7205759403792803736)
  (App_u lq_anf7205759403792803733 lq_anf7205759403792803734)
  zip_App_App_lem_res
  ↔ ∃ (zip_res : L2_u),
    zip_rel lq_anf7205759403792803736 lq_anf7205759403792803734 zip_res
    ∧ zip_App_App_lem_res
      == App2_u (MkPair_u lq_anf7205759403792803735 lq_anf7205759403792803733) zip_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite zip_App_App_lem: f_rel_back.

Theorem zip_App_Emp_lem lq_anf7205759403792803735 lq_anf7205759403792803736 zip_App_Emp_lem_res:
  zip_rel (App_u lq_anf7205759403792803735 lq_anf7205759403792803736) Emp_u zip_App_Emp_lem_res
  ↔ zip_App_Emp_lem_res == Emp2_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite zip_App_Emp_lem: f_rel_back.

Theorem zip_Emp_x_lem ds_d2Ag zip_Emp_x_lem_res:
  zip_rel Emp_u ds_d2Ag zip_Emp_x_lem_res ↔ zip_Emp_x_lem_res == Emp2_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite zip_Emp_x_lem: f_rel_back.

Theorem zip_rel_ex
  (ds_d2Af : L_u) (ds_d2Af_p : L_wf ds_d2Af ∧ True) (ds_d2Ag : L_u) (ds_d2Ag_p : L_wf ds_d2Ag ∧ True):
  zip_rel ds_d2Af ds_d2Ag ⌊ zip (exist _ ds_d2Af ds_d2Af_p) (exist _ ds_d2Ag ds_d2Ag_p) -⌋.
Proof.
  Opaque zip.
  existence_lemma_pre zip;
  try revert ds_d2Ag_p; generalize dependent ds_d2Ag;
  induction ds_d2Af as [lq_anf7205759403792803735 lq_anf7205759403792803736 IH_lq_anf7205759403792803736|];
  intros;
  [destruct ds_d2Ag as [lq_anf7205759403792803733 lq_anf7205759403792803734|];
   [fix_notations;
    pose proof (IH_lq_anf7205759403792803736
                ltac:(try clear IH_lq_anf7205759403792803736; solver)
                lq_anf7205759403792803734
                ltac:(try clear IH_lq_anf7205759403792803736; solver)) as IH_75968956;
    try clear IH_lq_anf7205759403792803736 |
    fix_notations] |
   fix_notations];
  simpl in *.
  Transparent zip.
  all: (existence_lemma_quicksolve zip; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve zip_rel_ex: rel_ax_db.

#[global] Opaque zip.

Theorem zip__zip_rel_rw
  (ds_d2Af : L_u)
  (ds_d2Af_p : L_wf ds_d2Af ∧ True)
  (ds_d2Ag : L_u)
  (ds_d2Ag_p : L_wf ds_d2Ag ∧ True)
  (VV : L2_u):
  ⌊ zip (exist _ ds_d2Af ds_d2Af_p) (exist _ ds_d2Ag ds_d2Ag_p) -⌋ = VV ↔ zip_rel ds_d2Af ds_d2Ag VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite zip__zip_rel_rw: f_rel_funct_db.

#[global] Hint Resolve zip__zip_rel_rw: rel_ax_db.

#[global] Instance zip_lookup_rw: dictionary rwLem zip := { lookup' := zip__zip_rel_rw }.

Theorem zip__zip_rel (ds_d2Af ds_d2Ag : L) (VV : L2_u):
  ⌊ zip ds_d2Af ds_d2Ag -⌋ = VV ↔ zip_rel ⌊ ds_d2Af ⌋ ⌊ ds_d2Ag ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite zip__zip_rel: f_rel_funct_db.

Theorem zip__zip_rel' (ds_d2Af_u ds_d2Ag_u : L_u) (ds_d2Af ds_d2Ag : L) (VV : L2_u):
  ds_d2Af_u = ⌊ ds_d2Af ⌋
  → (ds_d2Ag_u = ⌊ ds_d2Ag ⌋ → ⌊ zip ds_d2Af ds_d2Ag -⌋ = VV ↔ zip_rel ds_d2Af_u ds_d2Ag_u VV).
Proof.
  intros -> ->. refine (zip__zip_rel ds_d2Af ds_d2Ag VV).
Qed.

#[global] Hint Resolve zip__zip_rel': f_rel_funct_db.

Theorem zip_rel_mk
  (ds_d2Af : L_u) (ds_d2Af_p : L_wf ds_d2Af ∧ True) (ds_d2Ag : L_u) (ds_d2Ag_p : L_wf ds_d2Ag ∧ True):
  {VV: _ | zip_rel ds_d2Af ds_d2Ag VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, zip_rel ds_d2Af ds_d2Ag VV)
          (zip (exist _ ds_d2Af ds_d2Af_p) (exist _ ds_d2Ag ds_d2Ag_p))
          _);
  rewrite <- zip__zip_rel';
  quicksolve.
Qed.

#[global] Hint Resolve zip_rel_mk: f_rel_funct_db.

#[global] Instance zip_pack:
  @Pack
  (L ::RT λ (ds_d2Af : L), L ::RT λ (ds_d2Ag : L), nilRT)
  (L_u ::UT (L_u ::UT nilUT))
  ltac:(mkProjectsArgListTG (L ::RT λ (ds_d2Af : L), L ::RT λ (ds_d2Ag : L), nilRT) ((L_u ::UT (L_u ::UT nilUT))))
  L2_u
  (λ (x_52318321 : ArgList (L ::RT λ (ds_d2Af : L), L ::RT λ (ds_d2Ag : L), nilRT))
     (v_x_52318321 : L2_u),
   ltac:(flattenP (λ (ds_d2Af ds_d2Ag : L) (VV : L2_u), L2_wf VV ∧ True) x_52318321 v_x_52318321)).
Proof.
  buildPackG zip zip_rel zip__zip_rel zip_rel_funct.
Defined.

#[global] Instance zip_upack: @uPack (L_u ::UT (L_u ::UT nilUT)) L2_u.
Proof.
  buildUPackG zip_rel zip_rel_funct.
Defined.

Definition length_zip_spec
  (ds_d2zI : Nats)
  (ds_d2zJ : {ds_d2zJ: L_u | L_wf ds_d2zJ
                             ∧ ∃ (length_res : Nats_u), length_rel ds_d2zJ length_res ∧ length_res == ⌊ ds_d2zI -⌋})
  (ds_d2zK : {ds_d2zK: L_u | L_wf ds_d2zK
                             ∧ ∃ (length_res : Nats_u), length_rel ds_d2zK length_res ∧ length_res == ⌊ ds_d2zI -⌋}):
  Type :=
  {{∃ (zip_res : L2_u),
    zip_rel ⌊ ds_d2zJ -⌋ ⌊ ds_d2zK -⌋ zip_res
    ∧ ∃ (length2_res : Nats_u), length2_rel zip_res length2_res ∧ length2_res == ⌊ ds_d2zI -⌋}}.

#[global] Hint Unfold length_zip_spec: lia_unfold.

Theorem length_zip
  (ds_d2zI : Nats)
  (ds_d2zJ : {ds_d2zJ: L_u | L_wf ds_d2zJ
                             ∧ ∃ (length_res : Nats_u), length_rel ds_d2zJ length_res ∧ length_res == ⌊ ds_d2zI -⌋})
  (ds_d2zK : {ds_d2zK: L_u | L_wf ds_d2zK
                             ∧ ∃ (length_res : Nats_u), length_rel ds_d2zK length_res ∧ length_res == ⌊ ds_d2zI -⌋}):
  length_zip_spec ds_d2zI ds_d2zJ ds_d2zK.
Proof.
  destruct ds_d2zI as [ds_d2zI ds_d2zI_p].
  destruct ds_d2zJ as [ds_d2zJ ds_d2zJ_p].
  destruct ds_d2zK as [ds_d2zK ds_d2zK_p].
  try revert ds_d2zK_p; generalize dependent ds_d2zK;
  try revert ds_d2zJ_p; generalize dependent ds_d2zJ;
  induction ds_d2zI as [n IH_n|];
  intros.
  - destruct ds_d2zJ as [x xs|].
    + destruct ds_d2zK as [y ys|].
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
  - destruct ds_d2zJ as [lq_anf7205759403792803774 lq_anf7205759403792803775|].
    + intros; exfalso; solver.
    + destruct ds_d2zK as [lq_anf7205759403792803772 lq_anf7205759403792803773|].
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
  (ds_d2zD : Nats)
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
  (ds_d2zE : {ds_d2zE: L_u | L_wf ds_d2zE
                             ∧ ∃ (length_res : Nats_u), length_rel ds_d2zE length_res ∧ length_res == ⌊ ds_d2zD -⌋})
  (ds_d2zF : {ds_d2zF: L_u | L_wf ds_d2zF
                             ∧ ∃ (length_res : Nats_u), length_rel ds_d2zF length_res ∧ length_res == ⌊ ds_d2zD -⌋}):
  Type :=
  {{∃ (zip_res : L2_u),
    zip_rel ⌊ ds_d2zE -⌋ ⌊ ds_d2zF -⌋ zip_res
    ∧ ∃ (length2_res : Nats_u), length2_rel zip_res length2_res ∧ length2_res == ⌊ ds_d2zD -⌋}}.

#[global] Hint Unfold length_zipWith_spec: lia_unfold.

Theorem length_zipWith
  (ds_d2zD : Nats)
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
  (ds_d2zE : {ds_d2zE: L_u | L_wf ds_d2zE
                             ∧ ∃ (length_res : Nats_u), length_rel ds_d2zE length_res ∧ length_res == ⌊ ds_d2zD -⌋})
  (ds_d2zF : {ds_d2zF: L_u | L_wf ds_d2zF
                             ∧ ∃ (length_res : Nats_u), length_rel ds_d2zF length_res ∧ length_res == ⌊ ds_d2zD -⌋}):
  length_zipWith_spec ds_d2zD f ds_d2zE ds_d2zF.
Proof.
  destruct ds_d2zD as [ds_d2zD ds_d2zD_p].
  destruct ds_d2zE as [ds_d2zE ds_d2zE_p].
  destruct ds_d2zF as [ds_d2zF ds_d2zF_p].
  try revert ds_d2zF_p; generalize dependent ds_d2zF;
  try revert ds_d2zE_p; generalize dependent ds_d2zE;
  try revert f_p; generalize dependent f;
  induction ds_d2zD as [n IH_n|];
  intros.
  - destruct ds_d2zE as [x xs|].
    + destruct ds_d2zF as [y ys|].
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
  - destruct ds_d2zE as [lq_anf7205759403792803795 lq_anf7205759403792803796|].
    + intros; exfalso; solver.
    + destruct ds_d2zF as [lq_anf7205759403792803793 lq_anf7205759403792803794|].
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
       ltac:(mkProjectsArgListTG ({VV: Z | True}
 ::RT λ (lq_tmp0 : {VV: Z | True}),
      {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_41814097 : ArgList ({VV: Z | True}
                                 ::RT λ (lq_tmp0 : {VV: Z | True}),
                                      {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_41814097 : Z),
        ltac:(flattenP (λ (lq_tmp0 lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_41814097 v_x_41814097)))
  (ds_d2A5 ds_d2A6 : L):
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
  (ds_d2A5 ds_d2A6 : L):
  zipWith_spec f ds_d2A5 ds_d2A6.
Proof.
  destruct ds_d2A5 as [ds_d2A5 ds_d2A5_p].
  destruct ds_d2A6 as [ds_d2A6 ds_d2A6_p].
  try revert ds_d2A6_p; generalize dependent ds_d2A6; try revert f_p; generalize dependent f;
  induction ds_d2A5 as [lq_anf7205759403792803751 lq_anf7205759403792803752 IH_lq_anf7205759403792803752|];
  intros.
  - destruct ds_d2A6 as [lq_anf7205759403792803749 lq_anf7205759403792803750|].
    + refine (App
              (getPackF f (# lq_anf7205759403792803751) (# lq_anf7205759403792803749))
              (IH_lq_anf7205759403792803752
               ltac:(try clear IH_lq_anf7205759403792803752; solver)
               f
               lq_anf7205759403792803750
               ltac:(try clear IH_lq_anf7205759403792803752; solver))).
    + refine Emp.
  - refine Emp.
Defined.

Inductive zipWith_rel: @uPack (Z ::UT (Z ::UT nilUT)) Z → L_u → L_u → L_u → Prop :=
  | zipWith_x_App_App: ∀ (f : @uPack (Z ::UT (Z ::UT nilUT)) Z)
                         lq_anf7205759403792803751 lq_anf7205759403792803752 lq_anf7205759403792803749 lq_anf7205759403792803750
                         (zipWith_res : L_u),
                       zipWith_rel f lq_anf7205759403792803752 lq_anf7205759403792803750 zipWith_res
                       → ∀ (f_res : Z),
                         getUPackRel f lq_anf7205759403792803751 lq_anf7205759403792803749 f_res
                         → zipWith_rel
                           f
                           (App_u lq_anf7205759403792803751 lq_anf7205759403792803752)
                           (App_u lq_anf7205759403792803749 lq_anf7205759403792803750)
                           (App_u f_res zipWith_res)
  | zipWith_x_App_Emp: ∀ (f : @uPack (Z ::UT (Z ::UT nilUT)) Z)
                         lq_anf7205759403792803751 lq_anf7205759403792803752,
                       zipWith_rel f (App_u lq_anf7205759403792803751 lq_anf7205759403792803752) Emp_u Emp_u
  | zipWith_x_Emp_x: ∀ (f : @uPack (Z ::UT (Z ::UT nilUT)) Z) ds_d2A6,
                     zipWith_rel f Emp_u ds_d2A6 Emp_u.

#[global] Hint Constructors zipWith_rel: core_hint_db.

#[global] Instance zipWith_lookup_rel: dictionary rel zipWith := { lookup' := zipWith_rel }.

#[global] Instance zipWith_getF: getFunc zipWith_rel := { getF' := zipWith }.

Theorem zipWith_rel_funct [f : @uPack (Z ::UT (Z ::UT nilUT)) Z] [ds_d2A5 ds_d2A6 : L_u]:
  ∀ (VV VV' : L_u), zipWith_rel f ds_d2A5 ds_d2A6 VV → (zipWith_rel f ds_d2A5 ds_d2A6 VV' → VV = VV').
Proof.
  try revert ds_d2A6_p; generalize dependent ds_d2A6; try revert f_p; generalize dependent f;
  induction ds_d2A5 as [lq_anf7205759403792803751 lq_anf7205759403792803752 IH_lq_anf7205759403792803752|];
  intros;
  [destruct ds_d2A6 as [lq_anf7205759403792803749 lq_anf7205759403792803750|] |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve zipWith_rel_funct: f_rel_funct_db.

#[global] Instance zipWith_lookup_funct: dictionary functionhood zipWith := {
    lookup' := zipWith_rel_funct }.

Theorem zipWith_x_App_App_lem
  f lq_anf7205759403792803749 lq_anf7205759403792803750 lq_anf7205759403792803751 lq_anf7205759403792803752 zipWith_x_App_App_lem_res:
  zipWith_rel
  f
  (App_u lq_anf7205759403792803751 lq_anf7205759403792803752)
  (App_u lq_anf7205759403792803749 lq_anf7205759403792803750)
  zipWith_x_App_App_lem_res
  ↔ ∃ (zipWith_res : L_u),
    zipWith_rel f lq_anf7205759403792803752 lq_anf7205759403792803750 zipWith_res
    ∧ ∃ (f_res : Z),
      getUPackRel f lq_anf7205759403792803751 lq_anf7205759403792803749 f_res
      ∧ zipWith_x_App_App_lem_res == App_u f_res zipWith_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite zipWith_x_App_App_lem: f_rel_back.

Theorem zipWith_x_App_Emp_lem
  f lq_anf7205759403792803751 lq_anf7205759403792803752 zipWith_x_App_Emp_lem_res:
  zipWith_rel
  f
  (App_u lq_anf7205759403792803751 lq_anf7205759403792803752)
  Emp_u
  zipWith_x_App_Emp_lem_res
  ↔ zipWith_x_App_Emp_lem_res == Emp_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite zipWith_x_App_Emp_lem: f_rel_back.

Theorem zipWith_x_Emp_x_lem ds_d2A6 f zipWith_x_Emp_x_lem_res:
  zipWith_rel f Emp_u ds_d2A6 zipWith_x_Emp_x_lem_res ↔ zipWith_x_Emp_x_lem_res == Emp_u.
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
  (ds_d2A5 : L_u)
  (ds_d2A5_p : L_wf ds_d2A5 ∧ True)
  (ds_d2A6 : L_u)
  (ds_d2A6_p : L_wf ds_d2A6 ∧ True):
  zipWith_rel
  ⌊ f ⌋
  ds_d2A5
  ds_d2A6
  ⌊ zipWith f (exist _ ds_d2A5 ds_d2A5_p) (exist _ ds_d2A6 ds_d2A6_p) -⌋.
Proof.
  Opaque zipWith.
  existence_lemma_pre zipWith;
  try revert ds_d2A6_p; generalize dependent ds_d2A6; try revert f_p; generalize dependent f;
  induction ds_d2A5 as [lq_anf7205759403792803751 lq_anf7205759403792803752 IH_lq_anf7205759403792803752|];
  intros;
  [destruct ds_d2A6 as [lq_anf7205759403792803749 lq_anf7205759403792803750|];
   [fix_notations;
    pose proof (IH_lq_anf7205759403792803752
                ltac:(try clear IH_lq_anf7205759403792803752; solver)
                f
                lq_anf7205759403792803750
                ltac:(try clear IH_lq_anf7205759403792803752; solver)) as IH_47294567;
    try clear IH_lq_anf7205759403792803752 |
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
  (ds_d2A5 : L_u)
  (ds_d2A5_p : L_wf ds_d2A5 ∧ True)
  (ds_d2A6 : L_u)
  (ds_d2A6_p : L_wf ds_d2A6 ∧ True)
  (VV : L_u):
  ⌊ zipWith f (exist _ ds_d2A5 ds_d2A5_p) (exist _ ds_d2A6 ds_d2A6_p) -⌋ = VV
  ↔ zipWith_rel ⌊ f ⌋ ds_d2A5 ds_d2A6 VV.
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
  (ds_d2A5 ds_d2A6 : L)
  (VV : L_u):
  ⌊ zipWith f ds_d2A5 ds_d2A6 -⌋ = VV ↔ zipWith_rel ⌊ f ⌋ ⌊ ds_d2A5 ⌋ ⌊ ds_d2A6 ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite zipWith__zipWith_rel: f_rel_funct_db.

Theorem zipWith__zipWith_rel'
  (f_u : @uPack (Z ::UT (Z ::UT nilUT)) Z)
  (ds_d2A5_u ds_d2A6_u : L_u)
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
  (ds_d2A5 ds_d2A6 : L)
  (VV : L_u):
  f_u = ⌊ f ⌋
  → (ds_d2A5_u = ⌊ ds_d2A5 ⌋
     → (ds_d2A6_u = ⌊ ds_d2A6 ⌋
        → ⌊ zipWith f ds_d2A5 ds_d2A6 -⌋ = VV ↔ zipWith_rel f_u ds_d2A5_u ds_d2A6_u VV)).
Proof.
  intros -> -> ->. refine (zipWith__zipWith_rel f ds_d2A5 ds_d2A6 VV).
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
  (ds_d2A5 : L_u)
  (ds_d2A5_p : L_wf ds_d2A5 ∧ True)
  (ds_d2A6 : L_u)
  (ds_d2A6_p : L_wf ds_d2A6 ∧ True):
  {VV: _ | zipWith_rel (packProj f) ds_d2A5 ds_d2A6 VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, zipWith_rel (packProj f) ds_d2A5 ds_d2A6 VV)
          (zipWith f (exist _ ds_d2A5 ds_d2A5_p) (exist _ ds_d2A6 ds_d2A6_p))
          _);
  rewrite <- zipWith__zipWith_rel';
  quicksolve.
Qed.

#[global] Hint Resolve zipWith_rel_mk: f_rel_funct_db.

Definition zip_take_spec (ds_d2Ar m : L): Type :=
  {{∃ (zip_res : L2_u),
    zip_rel ⌊ ds_d2Ar -⌋ ⌊ m -⌋ zip_res
    ∧ ∃ (length_res : Nats_u),
      length_rel ⌊ ds_d2Ar -⌋ length_res
      ∧ ∃ (take_res : L_u),
        take_rel length_res ⌊ m -⌋ take_res
        ∧ ∃ (length_res_2 : Nats_u),
          length_rel ⌊ m -⌋ length_res_2
          ∧ ∃ (take_res_2 : L_u),
            take_rel length_res_2 ⌊ ds_d2Ar -⌋ take_res_2
            ∧ ∃ (zip_res_2 : L2_u), zip_rel take_res_2 take_res zip_res_2 ∧ zip_res == zip_res_2}}.

#[global] Hint Unfold zip_take_spec: lia_unfold.

Theorem zip_take (ds_d2Ar m : L): zip_take_spec ds_d2Ar m.
Proof.
  destruct ds_d2Ar as [ds_d2Ar ds_d2Ar_p].
  destruct m as [m m_p].
  try revert m_p; generalize dependent m;
  induction ds_d2Ar as [lq_anf7205759403792803857 lq_anf7205759403792803858 IH_lq_anf7205759403792803858|];
  intros.
  - destruct m as [lq_anf7205759403792803837 lq_anf7205759403792803838|].
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∃ (zip_res : L2_u),
               zip_rel
               (App_u lq_anf7205759403792803857 lq_anf7205759403792803858)
               (App_u lq_anf7205759403792803837 lq_anf7205759403792803838)
               zip_res
               ∧ ∃ (length_res : Nats_u),
                 length_rel (App_u lq_anf7205759403792803857 lq_anf7205759403792803858) length_res
                 ∧ ∃ (take_res : L_u),
                   take_rel length_res (App_u lq_anf7205759403792803837 lq_anf7205759403792803838) take_res
                   ∧ ∃ (length_res_2 : Nats_u),
                     length_rel (App_u lq_anf7205759403792803837 lq_anf7205759403792803838) length_res_2
                     ∧ ∃ (take_res_2 : L_u),
                       take_rel length_res_2 (App_u lq_anf7205759403792803857 lq_anf7205759403792803858) take_res_2
                       ∧ ∃ (zip_res_2 : L2_u), zip_rel take_res_2 take_res zip_res_2 ∧ zip_res == zip_res_2)
              (IH_lq_anf7205759403792803858
               ltac:(try clear IH_lq_anf7205759403792803858; solver)
               lq_anf7205759403792803838
               ltac:(try clear IH_lq_anf7205759403792803858; solver))
              ltac:(solver)).
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∃ (zip_res : L2_u),
               zip_rel (App_u lq_anf7205759403792803857 lq_anf7205759403792803858) Emp_u zip_res
               ∧ ∃ (length_res : Nats_u),
                 length_rel (App_u lq_anf7205759403792803857 lq_anf7205759403792803858) length_res
                 ∧ ∃ (take_res : L_u),
                   take_rel length_res Emp_u take_res
                   ∧ ∃ (length_res_2 : Nats_u),
                     length_rel Emp_u length_res_2
                     ∧ ∃ (take_res_2 : L_u),
                       take_rel length_res_2 (App_u lq_anf7205759403792803857 lq_anf7205759403792803858) take_res_2
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
            (let H_59619593: ⌊ zip Emp (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver)) ⌋
                             == ⌊ zip Emp Emp ⌋ :=
             ltac:(solver) in
             let H_26013249: ⌊ zip Emp Emp ⌋
                             == ⌊ zip (take (length (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) Emp) Emp ⌋ :=
             ltac:(solver) in
             let H_90026285: ⌊ zip (take (length (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) Emp) Emp ⌋
                             == ⌊ zip
                                  (take (length (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) Emp)
                                  (take Zero (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) ⌋ :=
             ltac:(solver) in
             let H_26027000: ⌊ zip
                               (take (length (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) Emp)
                               (take Zero (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) ⌋
                             == ⌊ zip
                                  (take (length (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) Emp)
                                  (take (length Emp) (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) ⌋ :=
             ltac:(solver) in
             # unit)
            ltac:(solver)).
Qed.
