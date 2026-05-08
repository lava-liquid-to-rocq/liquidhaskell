From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Set Universe Polymorphism. 
From Coq Require Import Unicode.Utf8.

Definition flip_spec
  (f : @Pack
       ({VV: Z | True}
        ::RT λ (f : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({VV: Z | True}
  ::RT λ (f : {VV: Z | True}),
       {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_64625469 : ArgList ({VV: Z | True}
                                 ::RT λ (f : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_64625469 : Z),
        ltac:(flattenP (λ (f lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_64625469 v_x_64625469)))
  (x : {x: Z | True})
  (y : {y: Z | True}):
  Type :=
  {VV: Z | True}.

#[global] Hint Unfold flip_spec: lia_unfold.

Definition flip
  (f : @Pack
       ({VV: Z | True}
        ::RT λ (f : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({VV: Z | True}
  ::RT λ (f : {VV: Z | True}),
       {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_64625469 : ArgList ({VV: Z | True}
                                 ::RT λ (f : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_64625469 : Z),
        ltac:(flattenP (λ (f lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_64625469 v_x_64625469)))
  (x : {x: Z | True})
  (y : {y: Z | True}):
  flip_spec f x y.
Proof.
  destruct x as [x x_p]. destruct y as [y y_p]. refine (getPackF f (# y) (# x)).
Defined.

Inductive flip_rel: @uPack (Z ::UT (Z ::UT nilUT)) Z → Z → Z → Z → Prop :=
  | flip_Constr: ∀ (f : @uPack (Z ::UT (Z ::UT nilUT)) Z) x y f_res,
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
  flip_rel f x y flip_inv_lem_res ↔ ∃ f_res, getUPackRel f y x f_res ∧ flip_inv_lem_res == f_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite flip_inv_lem: f_rel_back.

Theorem flip_rel_ex
  (f : @Pack
       ({f: Z | True}
        ::RT λ (f : {f: Z | True}), {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({f: Z | True}
  ::RT λ (f : {f: Z | True}),
       {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_66360476 : ArgList ({f: Z | True}
                                 ::RT λ (f : {f: Z | True}),
                                      {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_66360476 : Z),
        ltac:(flattenP (λ (f : {f: Z | True}) (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z),
 True) x_66360476 v_x_66360476)))
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
       ({f: Z | True}
        ::RT λ (f : {f: Z | True}), {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({f: Z | True}
  ::RT λ (f : {f: Z | True}),
       {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_66360476 : ArgList ({f: Z | True}
                                 ::RT λ (f : {f: Z | True}),
                                      {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_66360476 : Z),
        ltac:(flattenP (λ (f : {f: Z | True}) (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z),
 True) x_66360476 v_x_66360476)))
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
        ::RT λ (f : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({VV: Z | True}
  ::RT λ (f : {VV: Z | True}),
       {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_64625469 : ArgList ({VV: Z | True}
                                 ::RT λ (f : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_64625469 : Z),
        ltac:(flattenP (λ (f lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_64625469 v_x_64625469)))
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
        ::RT λ (f : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({VV: Z | True}
  ::RT λ (f : {VV: Z | True}),
       {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_64625469 : ArgList ({VV: Z | True}
                                 ::RT λ (f : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_64625469 : Z),
        ltac:(flattenP (λ (f lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_64625469 v_x_64625469)))
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
       ({f: Z | True}
        ::RT λ (f : {f: Z | True}), {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({f: Z | True}
  ::RT λ (f : {f: Z | True}),
       {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_66360476 : ArgList ({f: Z | True}
                                 ::RT λ (f : {f: Z | True}),
                                      {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_66360476 : Z),
        ltac:(flattenP (λ (f : {f: Z | True}) (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z),
 True) x_66360476 v_x_66360476)))
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

Definition geqN_spec (m n : Nats): Type :=
  Bool.

#[global] Hint Unfold geqN_spec: lia_unfold.

Definition geqN (m n : Nats): geqN_spec m n.
Proof.
  destruct m as [m m_p].
  destruct n as [n n_p].
  try revert m_p; generalize dependent m;
  induction n as [lq_anf7205759403792803866 IH_lq_anf7205759403792803866|];
  intros.
  - destruct m as [m|].
    + refine (IH_lq_anf7205759403792803866
              ltac:(try clear IH_lq_anf7205759403792803866; solver)
              m
              ltac:(try clear IH_lq_anf7205759403792803866; solver)).
    + refine (# false).
  - refine (# true).
Defined.

Inductive geqN_rel: Nats_u → Nats_u → bool → Prop :=
  | geqN_x_Zero: ∀ m, geqN_rel m Zero_u true
  | geqN_Zero_Suc: ∀ lq_anf7205759403792803866,
                   geqN_rel Zero_u (Suc_u lq_anf7205759403792803866) false
  | geqN_Suc_Suc: ∀ m lq_anf7205759403792803866 geqN_res,
                  geqN_rel m lq_anf7205759403792803866 geqN_res
                  → geqN_rel (Suc_u m) (Suc_u lq_anf7205759403792803866) geqN_res.

#[global] Hint Constructors geqN_rel: core_hint_db.

#[global] Instance geqN_lookup_rel: dictionary rel geqN := { lookup' := geqN_rel }.

#[global] Instance geqN_getF: getFunc geqN_rel := { getF' := geqN }.

Theorem geqN_rel_funct [m n : Nats_u]:
  ∀ (VV VV' : bool), geqN_rel m n VV → (geqN_rel m n VV' → VV = VV').
Proof.
  try revert m_p; generalize dependent m;
  induction n as [lq_anf7205759403792803866 IH_lq_anf7205759403792803866|];
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

Theorem geqN_Zero_Suc_lem lq_anf7205759403792803866 geqN_Zero_Suc_lem_res:
  geqN_rel Zero_u (Suc_u lq_anf7205759403792803866) geqN_Zero_Suc_lem_res
  ↔ geqN_Zero_Suc_lem_res == false.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite geqN_Zero_Suc_lem: f_rel_back.

Theorem geqN_Suc_Suc_lem lq_anf7205759403792803866 m geqN_Suc_Suc_lem_res:
  geqN_rel (Suc_u m) (Suc_u lq_anf7205759403792803866) geqN_Suc_Suc_lem_res
  ↔ ∃ geqN_res, geqN_rel m lq_anf7205759403792803866 geqN_res ∧ geqN_Suc_Suc_lem_res == geqN_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite geqN_Suc_Suc_lem: f_rel_back.

Theorem geqN_rel_ex (m : Nats_u) (m_p : Nats_wf m ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True):
  geqN_rel m n ⌊ geqN (exist _ m m_p) (exist _ n n_p) -⌋.
Proof.
  Opaque geqN.
  existence_lemma_pre geqN;
  try revert m_p; generalize dependent m;
  induction n as [lq_anf7205759403792803866 IH_lq_anf7205759403792803866|];
  intros;
  [destruct m as [m|];
   [fix_notations;
    pose proof (IH_lq_anf7205759403792803866
                ltac:(try clear IH_lq_anf7205759403792803866; solver)
                m
                ltac:(try clear IH_lq_anf7205759403792803866; solver)) as IH_70997580;
    try clear IH_lq_anf7205759403792803866 |
    fix_notations] |
   fix_notations];
  simpl in *.
  Transparent geqN.
  all: (existence_lemma_quicksolve geqN; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve geqN_rel_ex: rel_ax_db.

#[global] Opaque geqN.

Theorem geqN__geqN_rel_rw
  (m : Nats_u) (m_p : Nats_wf m ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True) (VV : bool):
  ⌊ geqN (exist _ m m_p) (exist _ n n_p) -⌋ = VV ↔ geqN_rel m n VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite geqN__geqN_rel_rw: f_rel_funct_db.

#[global] Hint Resolve geqN__geqN_rel_rw: rel_ax_db.

#[global] Instance geqN_lookup_rw: dictionary rwLem geqN := { lookup' := geqN__geqN_rel_rw }.

Theorem geqN__geqN_rel (m n : Nats) (VV : bool): ⌊ geqN m n -⌋ = VV ↔ geqN_rel ⌊ m ⌋ ⌊ n ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite geqN__geqN_rel: f_rel_funct_db.

Theorem geqN__geqN_rel' (m_u n_u : Nats_u) (m n : Nats) (VV : bool):
  m_u = ⌊ m ⌋ → (n_u = ⌊ n ⌋ → ⌊ geqN m n -⌋ = VV ↔ geqN_rel m_u n_u VV).
Proof.
  intros -> ->. refine (geqN__geqN_rel m n VV).
Qed.

#[global] Hint Resolve geqN__geqN_rel': f_rel_funct_db.

Theorem geqN_rel_mk (m : Nats_u) (m_p : Nats_wf m ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True):
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

Definition length2_spec (l : L2): Type :=
  Nats.

#[global] Hint Unfold length2_spec: lia_unfold.

Definition length2 (l : L2): length2_spec l.
Proof.
  destruct l as [l l_p].
  induction l as [ds_d2zN xs IH_xs|].
  - refine (Suc (IH_xs ltac:(try clear IH_xs; solver))).
  - refine Zero.
Defined.

Inductive length2_rel: L2_u → Nats_u → Prop :=
  | length2_Emp2: length2_rel Emp2_u Zero_u
  | length2_App2: ∀ ds_d2zN xs length2_res,
                  length2_rel xs length2_res → length2_rel (App2_u ds_d2zN xs) (Suc_u length2_res).

#[global] Hint Constructors length2_rel: core_hint_db.

#[global] Instance length2_lookup_rel: dictionary rel length2 := { lookup' := length2_rel }.

#[global] Instance length2_getF: getFunc length2_rel := { getF' := length2 }.

Theorem length2_rel_funct [l : L2_u]:
  ∀ (VV VV' : Nats_u), length2_rel l VV → (length2_rel l VV' → VV = VV').
Proof.
  induction l as [ds_d2zN xs IH_xs|]; rel_functionhood_body.
Qed.

#[global] Hint Resolve length2_rel_funct: f_rel_funct_db.

Theorem length2_Emp2_lem length2_Emp2_lem_res:
  length2_rel Emp2_u length2_Emp2_lem_res ↔ length2_Emp2_lem_res == Zero_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite length2_Emp2_lem: f_rel_back.

Theorem length2_App2_lem ds_d2zN xs length2_App2_lem_res:
  length2_rel (App2_u ds_d2zN xs) length2_App2_lem_res
  ↔ ∃ length2_res, length2_rel xs length2_res ∧ length2_App2_lem_res == Suc_u length2_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite length2_App2_lem: f_rel_back.

Theorem length2_rel_ex (l : L2_u) (l_p : L2_wf l ∧ True):
  length2_rel l ⌊ length2 (exist _ l l_p) -⌋.
Proof.
  Opaque length2.
  existence_lemma_pre length2;
  induction l as [ds_d2zN xs IH_xs|];
  [fix_notations; pose proof (IH_xs ltac:(try clear IH_xs; solver)) as IH_67415571; try clear IH_xs |
   fix_notations];
  simpl in *.
  Transparent length2.
  all: (existence_lemma_quicksolve length2; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve length2_rel_ex: rel_ax_db.

#[global] Opaque length2.

Theorem length2__length2_rel_rw (l : L2_u) (l_p : L2_wf l ∧ True) (VV : Nats_u):
  ⌊ length2 (exist _ l l_p) -⌋ = VV ↔ length2_rel l VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite length2__length2_rel_rw: f_rel_funct_db.

#[global] Hint Resolve length2__length2_rel_rw: rel_ax_db.

#[global] Instance length2_lookup_rw: dictionary rwLem length2 := {
    lookup' := length2__length2_rel_rw }.

Theorem length2__length2_rel (l : L2) (VV : Nats_u): ⌊ length2 l -⌋ = VV ↔ length2_rel ⌊ l ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite length2__length2_rel: f_rel_funct_db.

Theorem length2__length2_rel' (l_u : L2_u) (l : L2) (VV : Nats_u):
  l_u = ⌊ l ⌋ → ⌊ length2 l -⌋ = VV ↔ length2_rel l_u VV.
Proof.
  intros ->. refine (length2__length2_rel l VV).
Qed.

#[global] Hint Resolve length2__length2_rel': f_rel_funct_db.

Theorem length2_rel_mk (l : L2_u) (l_p : L2_wf l ∧ True): {VV: _ | length2_rel l VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, length2_rel l VV) (length2 (exist _ l l_p)) _);
  rewrite <- length2__length2_rel';
  quicksolve.
Qed.

#[global] Hint Resolve length2_rel_mk: f_rel_funct_db.

#[global] Instance length2_pack:
  @Pack
  (L2 ::RT λ (l : L2), nilRT)
  (L2_u ::UT nilUT)
  ltac:(mkProjectsArgListTG ((L2 ::RT λ (l : L2), nilRT)) ((L2_u ::UT nilUT)))
  Nats_u
  (λ (x_48046240 : ArgList (L2 ::RT λ (l : L2), nilRT)) (v_x_48046240 : Nats_u),
   ltac:(flattenP (λ (l : L2) (VV : Nats_u), Nats_wf VV ∧ True) x_48046240 v_x_48046240)).
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

Definition unzip_spec (l : L2): Type :=
  PairL.

#[global] Hint Unfold unzip_spec: lia_unfold.

Definition unzip (l : L2): unzip_spec l.
Proof.
  destruct l as [l l_p].
  induction l as [ds_d2A1 l IH_l|].
  - destruct ds_d2A1 as [x y].
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

Definition append_spec (lq_tmp0 lq_tmp1 : L): Type :=
  L.

#[global] Hint Unfold append_spec: lia_unfold.

Definition append (lq_tmp0 lq_tmp1 : L): append_spec lq_tmp0 lq_tmp1.
Proof.
  destruct lq_tmp0 as [lq_tmp0 lq_tmp0_p].
  destruct lq_tmp1 as [lq_tmp1 lq_tmp1_p].
  try revert lq_tmp1_p; generalize dependent lq_tmp1; induction lq_tmp0 as [x xs IH_xs|]; intros.
  - refine (App (# x) (IH_xs ltac:(try clear IH_xs; solver) lq_tmp1 ltac:(try clear IH_xs; solver))).
  - refine (exist (λ (lq_tmp1 : L_u), L_wf lq_tmp1 ∧ True) lq_tmp1 ltac:(solver)).
Defined.

Inductive append_rel: L_u → L_u → L_u → Prop :=
  | append_Emp_x: ∀ lq_tmp1, append_rel Emp_u lq_tmp1 lq_tmp1
  | append_App_x: ∀ x xs lq_tmp1 append_res,
                  append_rel xs lq_tmp1 append_res → append_rel (App_u x xs) lq_tmp1 (App_u x append_res).

#[global] Hint Constructors append_rel: core_hint_db.

#[global] Instance append_lookup_rel: dictionary rel append := { lookup' := append_rel }.

#[global] Instance append_getF: getFunc append_rel := { getF' := append }.

Theorem append_rel_funct [lq_tmp0 lq_tmp1 : L_u]:
  ∀ (VV VV' : L_u), append_rel lq_tmp0 lq_tmp1 VV → (append_rel lq_tmp0 lq_tmp1 VV' → VV = VV').
Proof.
  try revert lq_tmp1_p; generalize dependent lq_tmp1; induction lq_tmp0 as [x xs IH_xs|]; intros;
  rel_functionhood_body.
Qed.

#[global] Hint Resolve append_rel_funct: f_rel_funct_db.

Theorem append_Emp_x_lem lq_tmp1 append_Emp_x_lem_res:
  append_rel Emp_u lq_tmp1 append_Emp_x_lem_res ↔ append_Emp_x_lem_res == lq_tmp1.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite append_Emp_x_lem: f_rel_back.

Theorem append_App_x_lem lq_tmp1 x xs append_App_x_lem_res:
  append_rel (App_u x xs) lq_tmp1 append_App_x_lem_res
  ↔ ∃ append_res, append_rel xs lq_tmp1 append_res ∧ append_App_x_lem_res == App_u x append_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite append_App_x_lem: f_rel_back.

Theorem append_rel_ex
  (lq_tmp0 : L_u) (lq_tmp0_p : L_wf lq_tmp0 ∧ True) (lq_tmp1 : L_u) (lq_tmp1_p : L_wf lq_tmp1 ∧ True):
  append_rel lq_tmp0 lq_tmp1 ⌊ append (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p) -⌋.
Proof.
  Opaque append.
  existence_lemma_pre append;
  try revert lq_tmp1_p; generalize dependent lq_tmp1; induction lq_tmp0 as [x xs IH_xs|]; intros;
  [fix_notations;
   pose proof (IH_xs
               ltac:(try clear IH_xs; solver)
               lq_tmp1
               ltac:(try clear IH_xs; solver)) as IH_26846909;
   try clear IH_xs |
   fix_notations];
  simpl in *.
  Transparent append.
  all: (existence_lemma_quicksolve append; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve append_rel_ex: rel_ax_db.

#[global] Opaque append.

Theorem append__append_rel_rw
  (lq_tmp0 : L_u)
  (lq_tmp0_p : L_wf lq_tmp0 ∧ True)
  (lq_tmp1 : L_u)
  (lq_tmp1_p : L_wf lq_tmp1 ∧ True)
  (VV : L_u):
  ⌊ append (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p) -⌋ = VV
  ↔ append_rel lq_tmp0 lq_tmp1 VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite append__append_rel_rw: f_rel_funct_db.

#[global] Hint Resolve append__append_rel_rw: rel_ax_db.

#[global] Instance append_lookup_rw: dictionary rwLem append := {
    lookup' := append__append_rel_rw }.

Theorem append__append_rel (lq_tmp0 lq_tmp1 : L) (VV : L_u):
  ⌊ append lq_tmp0 lq_tmp1 -⌋ = VV ↔ append_rel ⌊ lq_tmp0 ⌋ ⌊ lq_tmp1 ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite append__append_rel: f_rel_funct_db.

Theorem append__append_rel' (lq_tmp0_u lq_tmp1_u : L_u) (lq_tmp0 lq_tmp1 : L) (VV : L_u):
  lq_tmp0_u = ⌊ lq_tmp0 ⌋
  → (lq_tmp1_u = ⌊ lq_tmp1 ⌋ → ⌊ append lq_tmp0 lq_tmp1 -⌋ = VV ↔ append_rel lq_tmp0_u lq_tmp1_u VV).
Proof.
  intros -> ->. refine (append__append_rel lq_tmp0 lq_tmp1 VV).
Qed.

#[global] Hint Resolve append__append_rel': f_rel_funct_db.

Theorem append_rel_mk
  (lq_tmp0 : L_u) (lq_tmp0_p : L_wf lq_tmp0 ∧ True) (lq_tmp1 : L_u) (lq_tmp1_p : L_wf lq_tmp1 ∧ True):
  {VV: _ | append_rel lq_tmp0 lq_tmp1 VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, append_rel lq_tmp0 lq_tmp1 VV)
          (append (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p))
          _);
  rewrite <- append__append_rel';
  quicksolve.
Qed.

#[global] Hint Resolve append_rel_mk: f_rel_funct_db.

#[global] Instance append_pack:
  @Pack
  (L ::RT λ (lq_tmp0 : L), L ::RT λ (lq_tmp1 : L), nilRT)
  (L_u ::UT (L_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((L ::RT λ (lq_tmp0 : L), L ::RT λ (lq_tmp1 : L), nilRT)) ((L_u ::UT (L_u ::UT nilUT))))
  L_u
  (λ (x_59358093 : ArgList (L ::RT λ (lq_tmp0 : L), L ::RT λ (lq_tmp1 : L), nilRT))
     (v_x_59358093 : L_u),
   ltac:(flattenP (λ (lq_tmp0 lq_tmp1 : L) (VV : L_u), L_wf VV ∧ True) x_59358093 v_x_59358093)).
Proof.
  buildPackG append append_rel append__append_rel append_rel_funct.
Defined.

#[global] Instance append_upack: @uPack (L_u ::UT (L_u ::UT nilUT)) L_u.
Proof.
  buildUPackG append_rel append_rel_funct.
Defined.

Definition append_nonempty_xs_spec
  (xs ys : L) (p : {{∃ append_res, append_rel ⌊ xs ⌋ ⌊ ys ⌋ append_res ∧ append_res == Emp_u}}):
  Type :=
  {{⌊ xs ⌋ == Emp_u}}.

#[global] Hint Unfold append_nonempty_xs_spec: lia_unfold.

Theorem append_nonempty_xs
  (xs ys : L) (p : {{∃ append_res, append_rel ⌊ xs ⌋ ⌊ ys ⌋ append_res ∧ append_res == Emp_u}}):
  append_nonempty_xs_spec xs ys p.
Proof.
  destruct xs as [xs xs_p].
  destruct ys as [ys ys_p].
  destruct p as [p p_p].
  destruct xs as [lq_anf7205759403792803716 lq_anf7205759403792803717|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), xs == Emp_u)
            (exist (λ (p : Unit),
                    ∃ append_res,
                    append_rel (App_u lq_anf7205759403792803716 lq_anf7205759403792803717) ys append_res
                    ∧ append_res == Emp_u) p ltac:(solver))
            ltac:(solver)).
  - destruct ys as [lq_anf7205759403792803714 lq_anf7205759403792803715|].
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit), xs == Emp_u)
              (exist (λ (p : Unit),
                      ∃ append_res,
                      append_rel Emp_u (App_u lq_anf7205759403792803714 lq_anf7205759403792803715) append_res
                      ∧ append_res == Emp_u) p ltac:(solver))
              ltac:(solver)).
    + refine (subsumptionCast Unit (λ (VV : Unit), xs == Emp_u) (# unit) ltac:(solver)).
Qed.

Definition append_nonempty_ys_spec
  (xs ys : L) (p : {{∃ append_res, append_rel ⌊ xs ⌋ ⌊ ys ⌋ append_res ∧ append_res == Emp_u}}):
  Type :=
  {{⌊ ys ⌋ == Emp_u}}.

#[global] Hint Unfold append_nonempty_ys_spec: lia_unfold.

Theorem append_nonempty_ys
  (xs ys : L) (p : {{∃ append_res, append_rel ⌊ xs ⌋ ⌊ ys ⌋ append_res ∧ append_res == Emp_u}}):
  append_nonempty_ys_spec xs ys p.
Proof.
  destruct xs as [xs xs_p].
  destruct ys as [ys ys_p].
  destruct p as [p p_p].
  destruct xs as [lq_anf7205759403792803707 lq_anf7205759403792803708|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ys == Emp_u)
            (exist (λ (p : Unit),
                    ∃ append_res,
                    append_rel (App_u lq_anf7205759403792803707 lq_anf7205759403792803708) ys append_res
                    ∧ append_res == Emp_u) p ltac:(solver))
            ltac:(solver)).
  - destruct ys as [lq_anf7205759403792803705 lq_anf7205759403792803706|].
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit), ys == Emp_u)
              (exist (λ (p : Unit),
                      ∃ append_res,
                      append_rel Emp_u (App_u lq_anf7205759403792803705 lq_anf7205759403792803706) append_res
                      ∧ append_res == Emp_u) p ltac:(solver))
              ltac:(solver)).
    + refine (subsumptionCast Unit (λ (VV : Unit), ys == Emp_u) (# unit) ltac:(solver)).
Qed.

Definition concatMap_spec
  (lq_tmp1 : @Pack
             ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
             L_u
             (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
                (v_x_40877513 : L_u),
              ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : L_u), L_wf VV ∧ True) x_40877513 v_x_40877513)))
  (lq_tmp3 : L):
  Type :=
  L.

#[global] Hint Unfold concatMap_spec: lia_unfold.

Definition concatMap
  (lq_tmp1 : @Pack
             ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
             L_u
             (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
                (v_x_40877513 : L_u),
              ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : L_u), L_wf VV ∧ True) x_40877513 v_x_40877513)))
  (lq_tmp3 : L):
  concatMap_spec lq_tmp1 lq_tmp3.
Proof.
  destruct lq_tmp3 as [lq_tmp3 lq_tmp3_p].
  try revert lq_tmp1_p; generalize dependent lq_tmp1; induction lq_tmp3 as [x xs IH_xs|]; intros.
  - refine (append (getPackF lq_tmp1 (# x)) (IH_xs ltac:(try clear IH_xs; solver) lq_tmp1)).
  - refine Emp.
Defined.

Inductive concatMap_rel: @uPack (Z ::UT nilUT) L_u → L_u → L_u → Prop :=
  | concatMap_x_Emp: ∀ (lq_tmp1 : @uPack (Z ::UT nilUT) L_u), concatMap_rel lq_tmp1 Emp_u Emp_u
  | concatMap_x_App: ∀ (lq_tmp1 : @uPack (Z ::UT nilUT) L_u) x xs concatMap_res,
                     concatMap_rel lq_tmp1 xs concatMap_res
                     → ∀ lq_tmp1_res,
                       getUPackRel lq_tmp1 x lq_tmp1_res
                       → ∀ append_res,
                         append_rel lq_tmp1_res concatMap_res append_res
                         → concatMap_rel lq_tmp1 (App_u x xs) append_res.

#[global] Hint Constructors concatMap_rel: core_hint_db.

#[global] Instance concatMap_lookup_rel: dictionary rel concatMap := { lookup' := concatMap_rel }.

#[global] Instance concatMap_getF: getFunc concatMap_rel := { getF' := concatMap }.

Theorem concatMap_rel_funct [lq_tmp1 : @uPack (Z ::UT nilUT) L_u] [lq_tmp3 : L_u]:
  ∀ (VV VV' : L_u), concatMap_rel lq_tmp1 lq_tmp3 VV → (concatMap_rel lq_tmp1 lq_tmp3 VV' → VV = VV').
Proof.
  try revert lq_tmp1_p; generalize dependent lq_tmp1; induction lq_tmp3 as [x xs IH_xs|]; intros;
  rel_functionhood_body.
Qed.

#[global] Hint Resolve concatMap_rel_funct: f_rel_funct_db.

Theorem concatMap_x_Emp_lem lq_tmp1 concatMap_x_Emp_lem_res:
  concatMap_rel lq_tmp1 Emp_u concatMap_x_Emp_lem_res ↔ concatMap_x_Emp_lem_res == Emp_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite concatMap_x_Emp_lem: f_rel_back.

Theorem concatMap_x_App_lem lq_tmp1 x xs concatMap_x_App_lem_res:
  concatMap_rel lq_tmp1 (App_u x xs) concatMap_x_App_lem_res
  ↔ ∃ concatMap_res,
    concatMap_rel lq_tmp1 xs concatMap_res
    ∧ ∃ lq_tmp1_res,
      getUPackRel lq_tmp1 x lq_tmp1_res
      ∧ ∃ append_res,
        append_rel lq_tmp1_res concatMap_res append_res ∧ concatMap_x_App_lem_res == append_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite concatMap_x_App_lem: f_rel_back.

Theorem concatMap_rel_ex
  (lq_tmp1 : @Pack
             ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({lq_tmp1: Z | True}
  ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT nilUT)))
             L_u
             (λ (x_86795196 : ArgList ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
                (v_x_86795196 : L_u),
              ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : L_u), L_wf VV ∧ True) x_86795196 v_x_86795196)))
  (lq_tmp3 : L_u)
  (lq_tmp3_p : L_wf lq_tmp3 ∧ True):
  concatMap_rel ⌊ lq_tmp1 ⌋ lq_tmp3 ⌊ concatMap lq_tmp1 (exist _ lq_tmp3 lq_tmp3_p) -⌋.
Proof.
  Opaque concatMap.
  existence_lemma_pre concatMap;
  try revert lq_tmp1_p; generalize dependent lq_tmp1; induction lq_tmp3 as [x xs IH_xs|]; intros;
  [fix_notations;
   pose proof (IH_xs ltac:(try clear IH_xs; solver) lq_tmp1) as IH_15591663;
   try clear IH_xs |
   fix_notations];
  simpl in *.
  Transparent concatMap.
  all: (existence_lemma_quicksolve concatMap; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve concatMap_rel_ex: rel_ax_db.

#[global] Opaque concatMap.

Theorem concatMap__concatMap_rel_rw
  (lq_tmp1 : @Pack
             ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({lq_tmp1: Z | True}
  ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT nilUT)))
             L_u
             (λ (x_86795196 : ArgList ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
                (v_x_86795196 : L_u),
              ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : L_u), L_wf VV ∧ True) x_86795196 v_x_86795196)))
  (lq_tmp3 : L_u)
  (lq_tmp3_p : L_wf lq_tmp3 ∧ True)
  (VV : L_u):
  ⌊ concatMap lq_tmp1 (exist _ lq_tmp3 lq_tmp3_p) -⌋ = VV ↔ concatMap_rel ⌊ lq_tmp1 ⌋ lq_tmp3 VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite concatMap__concatMap_rel_rw: f_rel_funct_db.

#[global] Hint Resolve concatMap__concatMap_rel_rw: rel_ax_db.

#[global] Instance concatMap_lookup_rw: dictionary rwLem concatMap := {
    lookup' := concatMap__concatMap_rel_rw }.

Theorem concatMap__concatMap_rel
  (lq_tmp1 : @Pack
             ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
             L_u
             (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
                (v_x_40877513 : L_u),
              ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : L_u), L_wf VV ∧ True) x_40877513 v_x_40877513)))
  (lq_tmp3 : L)
  (VV : L_u):
  ⌊ concatMap lq_tmp1 lq_tmp3 -⌋ = VV ↔ concatMap_rel ⌊ lq_tmp1 ⌋ ⌊ lq_tmp3 ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite concatMap__concatMap_rel: f_rel_funct_db.

Theorem concatMap__concatMap_rel'
  (lq_tmp1_u : @uPack (Z ::UT nilUT) L_u)
  (lq_tmp3_u : L_u)
  (lq_tmp1 : @Pack
             ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
             L_u
             (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
                (v_x_40877513 : L_u),
              ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : L_u), L_wf VV ∧ True) x_40877513 v_x_40877513)))
  (lq_tmp3 : L)
  (VV : L_u):
  lq_tmp1_u = ⌊ lq_tmp1 ⌋
  → (lq_tmp3_u = ⌊ lq_tmp3 ⌋
     → ⌊ concatMap lq_tmp1 lq_tmp3 -⌋ = VV ↔ concatMap_rel lq_tmp1_u lq_tmp3_u VV).
Proof.
  intros -> ->. refine (concatMap__concatMap_rel lq_tmp1 lq_tmp3 VV).
Qed.

#[global] Hint Resolve concatMap__concatMap_rel': f_rel_funct_db.

Theorem concatMap_rel_mk
  (lq_tmp1 : @Pack
             ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({lq_tmp1: Z | True}
  ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT nilUT)))
             L_u
             (λ (x_86795196 : ArgList ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
                (v_x_86795196 : L_u),
              ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : L_u), L_wf VV ∧ True) x_86795196 v_x_86795196)))
  (lq_tmp3 : L_u)
  (lq_tmp3_p : L_wf lq_tmp3 ∧ True):
  {VV: _ | concatMap_rel (packProj lq_tmp1) lq_tmp3 VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, concatMap_rel (packProj lq_tmp1) lq_tmp3 VV)
          (concatMap lq_tmp1 (exist _ lq_tmp3 lq_tmp3_p))
          _);
  rewrite <- concatMap__concatMap_rel';
  quicksolve.
Qed.

#[global] Hint Resolve concatMap_rel_mk: f_rel_funct_db.

Definition l2_pr1_spec (l : L2): Type :=
  L.

#[global] Hint Unfold l2_pr1_spec: lia_unfold.

Definition l2_pr1 (l : L2): l2_pr1_spec l.
Proof.
  destruct l as [l l_p].
  induction l as [ds_d2zy l IH_l|].
  - destruct ds_d2zy as [x ds_d2zz].
    + refine (App (# x) (IH_l ltac:(try clear IH_l; solver))).
  - refine Emp.
Defined.

Inductive l2_pr1_rel: L2_u → L_u → Prop :=
  | l2_pr1_Emp2: l2_pr1_rel Emp2_u Emp_u
  | l2_pr1__App2_MkPair_x: ∀ ds_d2zz l x l2_pr1_res,
                           l2_pr1_rel l l2_pr1_res → l2_pr1_rel (App2_u (MkPair_u x ds_d2zz) l) (App_u x l2_pr1_res).

#[global] Hint Constructors l2_pr1_rel: core_hint_db.

#[global] Instance l2_pr1_lookup_rel: dictionary rel l2_pr1 := { lookup' := l2_pr1_rel }.

#[global] Instance l2_pr1_getF: getFunc l2_pr1_rel := { getF' := l2_pr1 }.

Theorem l2_pr1_rel_funct [l : L2_u]:
  ∀ (VV VV' : L_u), l2_pr1_rel l VV → (l2_pr1_rel l VV' → VV = VV').
Proof.
  induction l as [ds_d2zy l IH_l|];
  [destruct ds_d2zy as [x ds_d2zz] |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve l2_pr1_rel_funct: f_rel_funct_db.

Theorem l2_pr1_Emp2_lem l2_pr1_Emp2_lem_res:
  l2_pr1_rel Emp2_u l2_pr1_Emp2_lem_res ↔ l2_pr1_Emp2_lem_res == Emp_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite l2_pr1_Emp2_lem: f_rel_back.

Theorem l2_pr1__App2_MkPair_x_lem ds_d2zz l x l2_pr1__App2_MkPair_x_lem_res:
  l2_pr1_rel (App2_u (MkPair_u x ds_d2zz) l) l2_pr1__App2_MkPair_x_lem_res
  ↔ ∃ l2_pr1_res, l2_pr1_rel l l2_pr1_res ∧ l2_pr1__App2_MkPair_x_lem_res == App_u x l2_pr1_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite l2_pr1__App2_MkPair_x_lem: f_rel_back.

Theorem l2_pr1_rel_ex (l : L2_u) (l_p : L2_wf l ∧ True): l2_pr1_rel l ⌊ l2_pr1 (exist _ l l_p) -⌋.
Proof.
  Opaque l2_pr1.
  existence_lemma_pre l2_pr1;
  induction l as [ds_d2zy l IH_l|];
  [destruct ds_d2zy as [x ds_d2zz];
   [fix_notations; pose proof (IH_l ltac:(try clear IH_l; solver)) as IH_26190279; try clear IH_l] |
   fix_notations];
  simpl in *.
  Transparent l2_pr1.
  all: (existence_lemma_quicksolve l2_pr1; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve l2_pr1_rel_ex: rel_ax_db.

#[global] Opaque l2_pr1.

Theorem l2_pr1__l2_pr1_rel_rw (l : L2_u) (l_p : L2_wf l ∧ True) (VV : L_u):
  ⌊ l2_pr1 (exist _ l l_p) -⌋ = VV ↔ l2_pr1_rel l VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite l2_pr1__l2_pr1_rel_rw: f_rel_funct_db.

#[global] Hint Resolve l2_pr1__l2_pr1_rel_rw: rel_ax_db.

#[global] Instance l2_pr1_lookup_rw: dictionary rwLem l2_pr1 := {
    lookup' := l2_pr1__l2_pr1_rel_rw }.

Theorem l2_pr1__l2_pr1_rel (l : L2) (VV : L_u): ⌊ l2_pr1 l -⌋ = VV ↔ l2_pr1_rel ⌊ l ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite l2_pr1__l2_pr1_rel: f_rel_funct_db.

Theorem l2_pr1__l2_pr1_rel' (l_u : L2_u) (l : L2) (VV : L_u):
  l_u = ⌊ l ⌋ → ⌊ l2_pr1 l -⌋ = VV ↔ l2_pr1_rel l_u VV.
Proof.
  intros ->. refine (l2_pr1__l2_pr1_rel l VV).
Qed.

#[global] Hint Resolve l2_pr1__l2_pr1_rel': f_rel_funct_db.

Theorem l2_pr1_rel_mk (l : L2_u) (l_p : L2_wf l ∧ True): {VV: _ | l2_pr1_rel l VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, l2_pr1_rel l VV) (l2_pr1 (exist _ l l_p)) _);
  rewrite <- l2_pr1__l2_pr1_rel';
  quicksolve.
Qed.

#[global] Hint Resolve l2_pr1_rel_mk: f_rel_funct_db.

#[global] Instance l2_pr1_pack:
  @Pack
  (L2 ::RT λ (l : L2), nilRT)
  (L2_u ::UT nilUT)
  ltac:(mkProjectsArgListTG ((L2 ::RT λ (l : L2), nilRT)) ((L2_u ::UT nilUT)))
  L_u
  (λ (x_48046240 : ArgList (L2 ::RT λ (l : L2), nilRT)) (v_x_48046240 : L_u),
   ltac:(flattenP (λ (l : L2) (VV : L_u), L_wf VV ∧ True) x_48046240 v_x_48046240)).
Proof.
  buildPackG l2_pr1 l2_pr1_rel l2_pr1__l2_pr1_rel l2_pr1_rel_funct.
Defined.

#[global] Instance l2_pr1_upack: @uPack (L2_u ::UT nilUT) L_u.
Proof.
  buildUPackG l2_pr1_rel l2_pr1_rel_funct.
Defined.

Definition l2_pr2_spec (l : L2): Type :=
  L.

#[global] Hint Unfold l2_pr2_spec: lia_unfold.

Definition l2_pr2 (l : L2): l2_pr2_spec l.
Proof.
  destruct l as [l l_p].
  induction l as [ds_d2zt l IH_l|].
  - destruct ds_d2zt as [ds_d2zu y].
    + refine (App (# y) (IH_l ltac:(try clear IH_l; solver))).
  - refine Emp.
Defined.

Inductive l2_pr2_rel: L2_u → L_u → Prop :=
  | l2_pr2_Emp2: l2_pr2_rel Emp2_u Emp_u
  | l2_pr2__App2_MkPair_x: ∀ ds_d2zu l y l2_pr2_res,
                           l2_pr2_rel l l2_pr2_res → l2_pr2_rel (App2_u (MkPair_u ds_d2zu y) l) (App_u y l2_pr2_res).

#[global] Hint Constructors l2_pr2_rel: core_hint_db.

#[global] Instance l2_pr2_lookup_rel: dictionary rel l2_pr2 := { lookup' := l2_pr2_rel }.

#[global] Instance l2_pr2_getF: getFunc l2_pr2_rel := { getF' := l2_pr2 }.

Theorem l2_pr2_rel_funct [l : L2_u]:
  ∀ (VV VV' : L_u), l2_pr2_rel l VV → (l2_pr2_rel l VV' → VV = VV').
Proof.
  induction l as [ds_d2zt l IH_l|];
  [destruct ds_d2zt as [ds_d2zu y] |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve l2_pr2_rel_funct: f_rel_funct_db.

Theorem l2_pr2_Emp2_lem l2_pr2_Emp2_lem_res:
  l2_pr2_rel Emp2_u l2_pr2_Emp2_lem_res ↔ l2_pr2_Emp2_lem_res == Emp_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite l2_pr2_Emp2_lem: f_rel_back.

Theorem l2_pr2__App2_MkPair_x_lem ds_d2zu l y l2_pr2__App2_MkPair_x_lem_res:
  l2_pr2_rel (App2_u (MkPair_u ds_d2zu y) l) l2_pr2__App2_MkPair_x_lem_res
  ↔ ∃ l2_pr2_res, l2_pr2_rel l l2_pr2_res ∧ l2_pr2__App2_MkPair_x_lem_res == App_u y l2_pr2_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite l2_pr2__App2_MkPair_x_lem: f_rel_back.

Theorem l2_pr2_rel_ex (l : L2_u) (l_p : L2_wf l ∧ True): l2_pr2_rel l ⌊ l2_pr2 (exist _ l l_p) -⌋.
Proof.
  Opaque l2_pr2.
  existence_lemma_pre l2_pr2;
  induction l as [ds_d2zt l IH_l|];
  [destruct ds_d2zt as [ds_d2zu y];
   [fix_notations; pose proof (IH_l ltac:(try clear IH_l; solver)) as IH_26190279; try clear IH_l] |
   fix_notations];
  simpl in *.
  Transparent l2_pr2.
  all: (existence_lemma_quicksolve l2_pr2; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve l2_pr2_rel_ex: rel_ax_db.

#[global] Opaque l2_pr2.

Theorem l2_pr2__l2_pr2_rel_rw (l : L2_u) (l_p : L2_wf l ∧ True) (VV : L_u):
  ⌊ l2_pr2 (exist _ l l_p) -⌋ = VV ↔ l2_pr2_rel l VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite l2_pr2__l2_pr2_rel_rw: f_rel_funct_db.

#[global] Hint Resolve l2_pr2__l2_pr2_rel_rw: rel_ax_db.

#[global] Instance l2_pr2_lookup_rw: dictionary rwLem l2_pr2 := {
    lookup' := l2_pr2__l2_pr2_rel_rw }.

Theorem l2_pr2__l2_pr2_rel (l : L2) (VV : L_u): ⌊ l2_pr2 l -⌋ = VV ↔ l2_pr2_rel ⌊ l ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite l2_pr2__l2_pr2_rel: f_rel_funct_db.

Theorem l2_pr2__l2_pr2_rel' (l_u : L2_u) (l : L2) (VV : L_u):
  l_u = ⌊ l ⌋ → ⌊ l2_pr2 l -⌋ = VV ↔ l2_pr2_rel l_u VV.
Proof.
  intros ->. refine (l2_pr2__l2_pr2_rel l VV).
Qed.

#[global] Hint Resolve l2_pr2__l2_pr2_rel': f_rel_funct_db.

Theorem l2_pr2_rel_mk (l : L2_u) (l_p : L2_wf l ∧ True): {VV: _ | l2_pr2_rel l VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, l2_pr2_rel l VV) (l2_pr2 (exist _ l l_p)) _);
  rewrite <- l2_pr2__l2_pr2_rel';
  quicksolve.
Qed.

#[global] Hint Resolve l2_pr2_rel_mk: f_rel_funct_db.

#[global] Instance l2_pr2_pack:
  @Pack
  (L2 ::RT λ (l : L2), nilRT)
  (L2_u ::UT nilUT)
  ltac:(mkProjectsArgListTG ((L2 ::RT λ (l : L2), nilRT)) ((L2_u ::UT nilUT)))
  L_u
  (λ (x_48046240 : ArgList (L2 ::RT λ (l : L2), nilRT)) (v_x_48046240 : L_u),
   ltac:(flattenP (λ (l : L2) (VV : L_u), L_wf VV ∧ True) x_48046240 v_x_48046240)).
Proof.
  buildPackG l2_pr2 l2_pr2_rel l2_pr2__l2_pr2_rel l2_pr2_rel_funct.
Defined.

#[global] Instance l2_pr2_upack: @uPack (L2_u ::UT nilUT) L_u.
Proof.
  buildUPackG l2_pr2_rel l2_pr2_rel_funct.
Defined.

Definition length_spec (l : L): Type :=
  Nats.

#[global] Hint Unfold length_spec: lia_unfold.

Definition length (l : L): length_spec l.
Proof.
  destruct l as [l l_p].
  induction l as [ds_d2zQ xs IH_xs|].
  - refine (Suc (IH_xs ltac:(try clear IH_xs; solver))).
  - refine Zero.
Defined.

Inductive length_rel: L_u → Nats_u → Prop :=
  | length_Emp: length_rel Emp_u Zero_u
  | length_App: ∀ ds_d2zQ xs length_res,
                length_rel xs length_res → length_rel (App_u ds_d2zQ xs) (Suc_u length_res).

#[global] Hint Constructors length_rel: core_hint_db.

#[global] Instance length_lookup_rel: dictionary rel length := { lookup' := length_rel }.

#[global] Instance length_getF: getFunc length_rel := { getF' := length }.

Theorem length_rel_funct [l : L_u]:
  ∀ (VV VV' : Nats_u), length_rel l VV → (length_rel l VV' → VV = VV').
Proof.
  induction l as [ds_d2zQ xs IH_xs|]; rel_functionhood_body.
Qed.

#[global] Hint Resolve length_rel_funct: f_rel_funct_db.

Theorem length_Emp_lem length_Emp_lem_res:
  length_rel Emp_u length_Emp_lem_res ↔ length_Emp_lem_res == Zero_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite length_Emp_lem: f_rel_back.

Theorem length_App_lem ds_d2zQ xs length_App_lem_res:
  length_rel (App_u ds_d2zQ xs) length_App_lem_res
  ↔ ∃ length_res, length_rel xs length_res ∧ length_App_lem_res == Suc_u length_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite length_App_lem: f_rel_back.

Theorem length_rel_ex (l : L_u) (l_p : L_wf l ∧ True): length_rel l ⌊ length (exist _ l l_p) -⌋.
Proof.
  Opaque length.
  existence_lemma_pre length;
  induction l as [ds_d2zQ xs IH_xs|];
  [fix_notations; pose proof (IH_xs ltac:(try clear IH_xs; solver)) as IH_67415571; try clear IH_xs |
   fix_notations];
  simpl in *.
  Transparent length.
  all: (existence_lemma_quicksolve length; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve length_rel_ex: rel_ax_db.

#[global] Opaque length.

Theorem length__length_rel_rw (l : L_u) (l_p : L_wf l ∧ True) (VV : Nats_u):
  ⌊ length (exist _ l l_p) -⌋ = VV ↔ length_rel l VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite length__length_rel_rw: f_rel_funct_db.

#[global] Hint Resolve length__length_rel_rw: rel_ax_db.

#[global] Instance length_lookup_rw: dictionary rwLem length := {
    lookup' := length__length_rel_rw }.

Theorem length__length_rel (l : L) (VV : Nats_u): ⌊ length l -⌋ = VV ↔ length_rel ⌊ l ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite length__length_rel: f_rel_funct_db.

Theorem length__length_rel' (l_u : L_u) (l : L) (VV : Nats_u):
  l_u = ⌊ l ⌋ → ⌊ length l -⌋ = VV ↔ length_rel l_u VV.
Proof.
  intros ->. refine (length__length_rel l VV).
Qed.

#[global] Hint Resolve length__length_rel': f_rel_funct_db.

Theorem length_rel_mk (l : L_u) (l_p : L_wf l ∧ True): {VV: _ | length_rel l VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, length_rel l VV) (length (exist _ l l_p)) _);
  rewrite <- length__length_rel';
  quicksolve.
Qed.

#[global] Hint Resolve length_rel_mk: f_rel_funct_db.

#[global] Instance length_pack:
  @Pack
  (L ::RT λ (l : L), nilRT)
  (L_u ::UT nilUT)
  ltac:(mkProjectsArgListTG ((L ::RT λ (l : L), nilRT)) ((L_u ::UT nilUT)))
  Nats_u
  (λ (x_41502435 : ArgList (L ::RT λ (l : L), nilRT)) (v_x_41502435 : Nats_u),
   ltac:(flattenP (λ (l : L) (VV : Nats_u), Nats_wf VV ∧ True) x_41502435 v_x_41502435)).
Proof.
  buildPackG length length_rel length__length_rel length_rel_funct.
Defined.

#[global] Instance length_upack: @uPack (L_u ::UT nilUT) Nats_u.
Proof.
  buildUPackG length_rel length_rel_funct.
Defined.

Definition length_unzip_1_spec (l : L2): Type :=
  {{∃ length2_res,
    length2_rel ⌊ l ⌋ length2_res
    ∧ ∃ l2_pr1_res,
      l2_pr1_rel ⌊ l ⌋ l2_pr1_res
      ∧ ∃ length_res, length_rel l2_pr1_res length_res ∧ length2_res == length_res}}.

#[global] Hint Unfold length_unzip_1_spec: lia_unfold.

Theorem length_unzip_1 (l : L2): length_unzip_1_spec l.
Proof.
  destruct l as [l l_p].
  induction l as [ds_d2zp l IH_l|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ length2_res,
             length2_rel l length2_res
             ∧ ∃ l2_pr1_res,
               l2_pr1_rel l l2_pr1_res
               ∧ ∃ length_res, length_rel l2_pr1_res length_res ∧ length2_res == length_res)
            (IH_l ltac:(try clear IH_l; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ length2_res,
             length2_rel l length2_res
             ∧ ∃ l2_pr1_res,
               l2_pr1_rel l l2_pr1_res
               ∧ ∃ length_res, length_rel l2_pr1_res length_res ∧ length2_res == length_res)
            (# unit)
            ltac:(solver)).
Qed.

Definition length_unzip_2_spec (l : L2): Type :=
  {{∃ length2_res,
    length2_rel ⌊ l ⌋ length2_res
    ∧ ∃ l2_pr2_res,
      l2_pr2_rel ⌊ l ⌋ l2_pr2_res
      ∧ ∃ length_res, length_rel l2_pr2_res length_res ∧ length2_res == length_res}}.

#[global] Hint Unfold length_unzip_2_spec: lia_unfold.

Theorem length_unzip_2 (l : L2): length_unzip_2_spec l.
Proof.
  destruct l as [l l_p].
  induction l as [ds_d2zn l IH_l|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ length2_res,
             length2_rel l length2_res
             ∧ ∃ l2_pr2_res,
               l2_pr2_rel l l2_pr2_res
               ∧ ∃ length_res, length_rel l2_pr2_res length_res ∧ length2_res == length_res)
            (IH_l ltac:(try clear IH_l; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ length2_res,
             length2_rel l length2_res
             ∧ ∃ l2_pr2_res,
               l2_pr2_rel l l2_pr2_res
               ∧ ∃ length_res, length_rel l2_pr2_res length_res ∧ length2_res == length_res)
            (# unit)
            ltac:(solver)).
Qed.

Definition map_spec
  (lq_tmp1 : @Pack
             ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
             Z
             (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
                (v_x_40877513 : Z),
              ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513)))
  (lq_tmp3 : L):
  Type :=
  L.

#[global] Hint Unfold map_spec: lia_unfold.

Definition map
  (lq_tmp1 : @Pack
             ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
             Z
             (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
                (v_x_40877513 : Z),
              ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513)))
  (lq_tmp3 : L):
  map_spec lq_tmp1 lq_tmp3.
Proof.
  destruct lq_tmp3 as [lq_tmp3 lq_tmp3_p].
  try revert lq_tmp1_p; generalize dependent lq_tmp1; induction lq_tmp3 as [x xs IH_xs|]; intros.
  - refine (App (getPackF lq_tmp1 (# x)) (IH_xs ltac:(try clear IH_xs; solver) lq_tmp1)).
  - refine Emp.
Defined.

Inductive map_rel: @uPack (Z ::UT nilUT) Z → L_u → L_u → Prop :=
  | map_x_Emp: ∀ (lq_tmp1 : @uPack (Z ::UT nilUT) Z), map_rel lq_tmp1 Emp_u Emp_u
  | map_x_App: ∀ (lq_tmp1 : @uPack (Z ::UT nilUT) Z) x xs map_res,
               map_rel lq_tmp1 xs map_res
               → ∀ lq_tmp1_res,
                 getUPackRel lq_tmp1 x lq_tmp1_res → map_rel lq_tmp1 (App_u x xs) (App_u lq_tmp1_res map_res).

#[global] Hint Constructors map_rel: core_hint_db.

#[global] Instance map_lookup_rel: dictionary rel map := { lookup' := map_rel }.

#[global] Instance map_getF: getFunc map_rel := { getF' := map }.

Theorem map_rel_funct [lq_tmp1 : @uPack (Z ::UT nilUT) Z] [lq_tmp3 : L_u]:
  ∀ (VV VV' : L_u), map_rel lq_tmp1 lq_tmp3 VV → (map_rel lq_tmp1 lq_tmp3 VV' → VV = VV').
Proof.
  try revert lq_tmp1_p; generalize dependent lq_tmp1; induction lq_tmp3 as [x xs IH_xs|]; intros;
  rel_functionhood_body.
Qed.

#[global] Hint Resolve map_rel_funct: f_rel_funct_db.

Theorem map_x_Emp_lem lq_tmp1 map_x_Emp_lem_res:
  map_rel lq_tmp1 Emp_u map_x_Emp_lem_res ↔ map_x_Emp_lem_res == Emp_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite map_x_Emp_lem: f_rel_back.

Theorem map_x_App_lem lq_tmp1 x xs map_x_App_lem_res:
  map_rel lq_tmp1 (App_u x xs) map_x_App_lem_res
  ↔ ∃ map_res,
    map_rel lq_tmp1 xs map_res
    ∧ ∃ lq_tmp1_res, getUPackRel lq_tmp1 x lq_tmp1_res ∧ map_x_App_lem_res == App_u lq_tmp1_res map_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite map_x_App_lem: f_rel_back.

Theorem map_rel_ex
  (lq_tmp1 : @Pack
             ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({lq_tmp1: Z | True}
  ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT nilUT)))
             Z
             (λ (x_86795196 : ArgList ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
                (v_x_86795196 : Z),
              ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z), True) x_86795196 v_x_86795196)))
  (lq_tmp3 : L_u)
  (lq_tmp3_p : L_wf lq_tmp3 ∧ True):
  map_rel ⌊ lq_tmp1 ⌋ lq_tmp3 ⌊ map lq_tmp1 (exist _ lq_tmp3 lq_tmp3_p) -⌋.
Proof.
  Opaque map.
  existence_lemma_pre map;
  try revert lq_tmp1_p; generalize dependent lq_tmp1; induction lq_tmp3 as [x xs IH_xs|]; intros;
  [fix_notations;
   pose proof (IH_xs ltac:(try clear IH_xs; solver) lq_tmp1) as IH_15591663;
   try clear IH_xs |
   fix_notations];
  simpl in *.
  Transparent map.
  all: (existence_lemma_quicksolve map; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve map_rel_ex: rel_ax_db.

#[global] Opaque map.

Theorem map__map_rel_rw
  (lq_tmp1 : @Pack
             ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({lq_tmp1: Z | True}
  ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT nilUT)))
             Z
             (λ (x_86795196 : ArgList ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
                (v_x_86795196 : Z),
              ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z), True) x_86795196 v_x_86795196)))
  (lq_tmp3 : L_u)
  (lq_tmp3_p : L_wf lq_tmp3 ∧ True)
  (VV : L_u):
  ⌊ map lq_tmp1 (exist _ lq_tmp3 lq_tmp3_p) -⌋ = VV ↔ map_rel ⌊ lq_tmp1 ⌋ lq_tmp3 VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite map__map_rel_rw: f_rel_funct_db.

#[global] Hint Resolve map__map_rel_rw: rel_ax_db.

#[global] Instance map_lookup_rw: dictionary rwLem map := { lookup' := map__map_rel_rw }.

Theorem map__map_rel
  (lq_tmp1 : @Pack
             ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
             Z
             (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
                (v_x_40877513 : Z),
              ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513)))
  (lq_tmp3 : L)
  (VV : L_u):
  ⌊ map lq_tmp1 lq_tmp3 -⌋ = VV ↔ map_rel ⌊ lq_tmp1 ⌋ ⌊ lq_tmp3 ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite map__map_rel: f_rel_funct_db.

Theorem map__map_rel'
  (lq_tmp1_u : @uPack (Z ::UT nilUT) Z)
  (lq_tmp3_u : L_u)
  (lq_tmp1 : @Pack
             ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
             Z
             (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
                (v_x_40877513 : Z),
              ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513)))
  (lq_tmp3 : L)
  (VV : L_u):
  lq_tmp1_u = ⌊ lq_tmp1 ⌋
  → (lq_tmp3_u = ⌊ lq_tmp3 ⌋ → ⌊ map lq_tmp1 lq_tmp3 -⌋ = VV ↔ map_rel lq_tmp1_u lq_tmp3_u VV).
Proof.
  intros -> ->. refine (map__map_rel lq_tmp1 lq_tmp3 VV).
Qed.

#[global] Hint Resolve map__map_rel': f_rel_funct_db.

Theorem map_rel_mk
  (lq_tmp1 : @Pack
             ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({lq_tmp1: Z | True}
  ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT nilUT)))
             Z
             (λ (x_86795196 : ArgList ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
                (v_x_86795196 : Z),
              ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z), True) x_86795196 v_x_86795196)))
  (lq_tmp3 : L_u)
  (lq_tmp3_p : L_wf lq_tmp3 ∧ True):
  {VV: _ | map_rel (packProj lq_tmp1) lq_tmp3 VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, map_rel (packProj lq_tmp1) lq_tmp3 VV)
          (map lq_tmp1 (exist _ lq_tmp3 lq_tmp3_p))
          _);
  rewrite <- map__map_rel';
  quicksolve.
Qed.

#[global] Hint Resolve map_rel_mk: f_rel_funct_db.

Definition length_map_spec
  (f : @Pack
       ({VV: Z | True} ::RT λ (f : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (f : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_46517173 : ArgList ({VV: Z | True} ::RT λ (f : {VV: Z | True}), nilRT)) (v_x_46517173 : Z),
        ltac:(flattenP (λ (f : {VV: Z | True}) (VV : Z), True) x_46517173 v_x_46517173)))
  (l : L):
  Type :=
  {{∃ map_res,
    map_rel ⌊ f ⌋ ⌊ l ⌋ map_res
    ∧ ∃ length_res,
      length_rel map_res length_res
      ∧ ∃ length_res_2, length_rel ⌊ l ⌋ length_res_2 ∧ length_res == length_res_2}}.

#[global] Hint Unfold length_map_spec: lia_unfold.

Theorem length_map
  (f : @Pack
       ({VV: Z | True} ::RT λ (f : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (f : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_46517173 : ArgList ({VV: Z | True} ::RT λ (f : {VV: Z | True}), nilRT)) (v_x_46517173 : Z),
        ltac:(flattenP (λ (f : {VV: Z | True}) (VV : Z), True) x_46517173 v_x_46517173)))
  (l : L):
  length_map_spec f l.
Proof.
  destruct l as [l l_p].
  try revert f_p; generalize dependent f; induction l as [x xs IH_xs|]; intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ map_res,
             map_rel f l map_res
             ∧ ∃ length_res,
               length_rel map_res length_res
               ∧ ∃ length_res_2, length_rel l length_res_2 ∧ length_res == length_res_2)
            (IH_xs ltac:(try clear IH_xs; solver) f)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ map_res,
             map_rel f l map_res
             ∧ ∃ length_res,
               length_rel map_res length_res
               ∧ ∃ length_res_2, length_rel l length_res_2 ∧ length_res == length_res_2)
            (# unit)
            ltac:(solver)).
Qed.

Definition reverse_spec (l : L): Type :=
  L.

#[global] Hint Unfold reverse_spec: lia_unfold.

Definition reverse (l : L): reverse_spec l.
Proof.
  destruct l as [l l_p].
  induction l as [x xs IH_xs|].
  - refine (append (IH_xs ltac:(try clear IH_xs; solver)) (App (# x) Emp)).
  - refine Emp.
Defined.

Inductive reverse_rel: L_u → L_u → Prop :=
  | reverse_Emp: reverse_rel Emp_u Emp_u
  | reverse_App: ∀ x xs reverse_res,
                 reverse_rel xs reverse_res
                 → ∀ append_res,
                   append_rel reverse_res (App_u x Emp_u) append_res → reverse_rel (App_u x xs) append_res.

#[global] Hint Constructors reverse_rel: core_hint_db.

#[global] Instance reverse_lookup_rel: dictionary rel reverse := { lookup' := reverse_rel }.

#[global] Instance reverse_getF: getFunc reverse_rel := { getF' := reverse }.

Theorem reverse_rel_funct [l : L_u]:
  ∀ (VV VV' : L_u), reverse_rel l VV → (reverse_rel l VV' → VV = VV').
Proof.
  induction l as [x xs IH_xs|]; rel_functionhood_body.
Qed.

#[global] Hint Resolve reverse_rel_funct: f_rel_funct_db.

Theorem reverse_Emp_lem reverse_Emp_lem_res:
  reverse_rel Emp_u reverse_Emp_lem_res ↔ reverse_Emp_lem_res == Emp_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite reverse_Emp_lem: f_rel_back.

Theorem reverse_App_lem x xs reverse_App_lem_res:
  reverse_rel (App_u x xs) reverse_App_lem_res
  ↔ ∃ reverse_res,
    reverse_rel xs reverse_res
    ∧ ∃ append_res,
      append_rel reverse_res (App_u x Emp_u) append_res ∧ reverse_App_lem_res == append_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite reverse_App_lem: f_rel_back.

Theorem reverse_rel_ex (l : L_u) (l_p : L_wf l ∧ True): reverse_rel l ⌊ reverse (exist _ l l_p) -⌋.
Proof.
  Opaque reverse.
  existence_lemma_pre reverse;
  induction l as [x xs IH_xs|];
  [fix_notations; pose proof (IH_xs ltac:(try clear IH_xs; solver)) as IH_67415571; try clear IH_xs |
   fix_notations];
  simpl in *.
  Transparent reverse.
  all: (existence_lemma_quicksolve reverse; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve reverse_rel_ex: rel_ax_db.

#[global] Opaque reverse.

Theorem reverse__reverse_rel_rw (l : L_u) (l_p : L_wf l ∧ True) (VV : L_u):
  ⌊ reverse (exist _ l l_p) -⌋ = VV ↔ reverse_rel l VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite reverse__reverse_rel_rw: f_rel_funct_db.

#[global] Hint Resolve reverse__reverse_rel_rw: rel_ax_db.

#[global] Instance reverse_lookup_rw: dictionary rwLem reverse := {
    lookup' := reverse__reverse_rel_rw }.

Theorem reverse__reverse_rel (l : L) (VV : L_u): ⌊ reverse l -⌋ = VV ↔ reverse_rel ⌊ l ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite reverse__reverse_rel: f_rel_funct_db.

Theorem reverse__reverse_rel' (l_u : L_u) (l : L) (VV : L_u):
  l_u = ⌊ l ⌋ → ⌊ reverse l -⌋ = VV ↔ reverse_rel l_u VV.
Proof.
  intros ->. refine (reverse__reverse_rel l VV).
Qed.

#[global] Hint Resolve reverse__reverse_rel': f_rel_funct_db.

Theorem reverse_rel_mk (l : L_u) (l_p : L_wf l ∧ True): {VV: _ | reverse_rel l VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, reverse_rel l VV) (reverse (exist _ l l_p)) _);
  rewrite <- reverse__reverse_rel';
  quicksolve.
Qed.

#[global] Hint Resolve reverse_rel_mk: f_rel_funct_db.

#[global] Instance reverse_pack:
  @Pack
  (L ::RT λ (l : L), nilRT)
  (L_u ::UT nilUT)
  ltac:(mkProjectsArgListTG ((L ::RT λ (l : L), nilRT)) ((L_u ::UT nilUT)))
  L_u
  (λ (x_41502435 : ArgList (L ::RT λ (l : L), nilRT)) (v_x_41502435 : L_u),
   ltac:(flattenP (λ (l : L) (VV : L_u), L_wf VV ∧ True) x_41502435 v_x_41502435)).
Proof.
  buildPackG reverse reverse_rel reverse__reverse_rel reverse_rel_funct.
Defined.

#[global] Instance reverse_upack: @uPack (L_u ::UT nilUT) L_u.
Proof.
  buildUPackG reverse_rel reverse_rel_funct.
Defined.

Definition reverse_nonempty_spec
  (l : L) (p : {{∃ reverse_res, reverse_rel ⌊ l ⌋ reverse_res ∧ reverse_res == Emp_u}}):
  Type :=
  {{⌊ l ⌋ == Emp_u}}.

#[global] Hint Unfold reverse_nonempty_spec: lia_unfold.

Theorem reverse_nonempty
  (l : L) (p : {{∃ reverse_res, reverse_rel ⌊ l ⌋ reverse_res ∧ reverse_res == Emp_u}}):
  reverse_nonempty_spec l p.
Proof.
  destruct l as [l l_p].
  destruct p as [p p_p].
  destruct l as [x xs|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), l == Emp_u)
            (append_nonempty_ys
             (reverse (exist (λ (VV : L_u), L_wf VV ∧ True) xs ltac:(solver)))
             (App (# x) Emp)
             (subsumptionCast
              Unit
              (λ (p : Unit),
               ∃ append_res,
               append_rel
               ⌊ reverse (exist (λ (VV : L_u), L_wf VV ∧ True) xs ltac:(solver)) ⌋
               (App_u x Emp_u)
               append_res
               ∧ append_res == Emp_u)
              (exist (λ (p : Unit),
                      ∃ reverse_res, reverse_rel (App_u x xs) reverse_res ∧ reverse_res == Emp_u) p ltac:(solver))
              ltac:(solver)))
            ltac:(solver)).
  - refine (subsumptionCast Unit (λ (VV : Unit), l == Emp_u) (# unit) ltac:(solver)).
Qed.

Definition take_spec (n : Nats) (l : L): Type :=
  L.

#[global] Hint Unfold take_spec: lia_unfold.

Definition take (n : Nats) (l : L): take_spec n l.
Proof.
  destruct n as [n n_p].
  destruct l as [l l_p].
  try revert l_p; generalize dependent l;
  induction n as [lq_anf7205759403792803823 IH_lq_anf7205759403792803823|];
  intros.
  - destruct l as [lq_anf7205759403792803821 lq_anf7205759403792803822|].
    + refine (App
              (# lq_anf7205759403792803821)
              (IH_lq_anf7205759403792803823
               ltac:(try clear IH_lq_anf7205759403792803823; solver)
               lq_anf7205759403792803822
               ltac:(try clear IH_lq_anf7205759403792803823; solver))).
    + refine Emp.
  - refine Emp.
Defined.

Inductive take_rel: Nats_u → L_u → L_u → Prop :=
  | take_Zero_x: ∀ l, take_rel Zero_u l Emp_u
  | take_Suc_Emp: ∀ lq_anf7205759403792803823, take_rel (Suc_u lq_anf7205759403792803823) Emp_u Emp_u
  | take_Suc_App: ∀ lq_anf7205759403792803823 lq_anf7205759403792803821 lq_anf7205759403792803822 take_res,
                  take_rel lq_anf7205759403792803823 lq_anf7205759403792803822 take_res
                  → take_rel
                    (Suc_u lq_anf7205759403792803823)
                    (App_u lq_anf7205759403792803821 lq_anf7205759403792803822)
                    (App_u lq_anf7205759403792803821 take_res).

#[global] Hint Constructors take_rel: core_hint_db.

#[global] Instance take_lookup_rel: dictionary rel take := { lookup' := take_rel }.

#[global] Instance take_getF: getFunc take_rel := { getF' := take }.

Theorem take_rel_funct [n : Nats_u] [l : L_u]:
  ∀ (VV VV' : L_u), take_rel n l VV → (take_rel n l VV' → VV = VV').
Proof.
  try revert l_p; generalize dependent l;
  induction n as [lq_anf7205759403792803823 IH_lq_anf7205759403792803823|];
  intros;
  [destruct l as [lq_anf7205759403792803821 lq_anf7205759403792803822|] |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve take_rel_funct: f_rel_funct_db.

Theorem take_Zero_x_lem l take_Zero_x_lem_res:
  take_rel Zero_u l take_Zero_x_lem_res ↔ take_Zero_x_lem_res == Emp_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite take_Zero_x_lem: f_rel_back.

Theorem take_Suc_Emp_lem lq_anf7205759403792803823 take_Suc_Emp_lem_res:
  take_rel (Suc_u lq_anf7205759403792803823) Emp_u take_Suc_Emp_lem_res
  ↔ take_Suc_Emp_lem_res == Emp_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite take_Suc_Emp_lem: f_rel_back.

Theorem take_Suc_App_lem
  lq_anf7205759403792803821 lq_anf7205759403792803822 lq_anf7205759403792803823 take_Suc_App_lem_res:
  take_rel
  (Suc_u lq_anf7205759403792803823)
  (App_u lq_anf7205759403792803821 lq_anf7205759403792803822)
  take_Suc_App_lem_res
  ↔ ∃ take_res,
    take_rel lq_anf7205759403792803823 lq_anf7205759403792803822 take_res
    ∧ take_Suc_App_lem_res == App_u lq_anf7205759403792803821 take_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite take_Suc_App_lem: f_rel_back.

Theorem take_rel_ex (n : Nats_u) (n_p : Nats_wf n ∧ True) (l : L_u) (l_p : L_wf l ∧ True):
  take_rel n l ⌊ take (exist _ n n_p) (exist _ l l_p) -⌋.
Proof.
  Opaque take.
  existence_lemma_pre take;
  try revert l_p; generalize dependent l;
  induction n as [lq_anf7205759403792803823 IH_lq_anf7205759403792803823|];
  intros;
  [destruct l as [lq_anf7205759403792803821 lq_anf7205759403792803822|];
   [fix_notations;
    pose proof (IH_lq_anf7205759403792803823
                ltac:(try clear IH_lq_anf7205759403792803823; solver)
                lq_anf7205759403792803822
                ltac:(try clear IH_lq_anf7205759403792803823; solver)) as IH_13177556;
    try clear IH_lq_anf7205759403792803823 |
    fix_notations] |
   fix_notations];
  simpl in *.
  Transparent take.
  all: (existence_lemma_quicksolve take; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve take_rel_ex: rel_ax_db.

#[global] Opaque take.

Theorem take__take_rel_rw
  (n : Nats_u) (n_p : Nats_wf n ∧ True) (l : L_u) (l_p : L_wf l ∧ True) (VV : L_u):
  ⌊ take (exist _ n n_p) (exist _ l l_p) -⌋ = VV ↔ take_rel n l VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite take__take_rel_rw: f_rel_funct_db.

#[global] Hint Resolve take__take_rel_rw: rel_ax_db.

#[global] Instance take_lookup_rw: dictionary rwLem take := { lookup' := take__take_rel_rw }.

Theorem take__take_rel (n : Nats) (l : L) (VV : L_u): ⌊ take n l -⌋ = VV ↔ take_rel ⌊ n ⌋ ⌊ l ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite take__take_rel: f_rel_funct_db.

Theorem take__take_rel' (n_u : Nats_u) (l_u : L_u) (n : Nats) (l : L) (VV : L_u):
  n_u = ⌊ n ⌋ → (l_u = ⌊ l ⌋ → ⌊ take n l -⌋ = VV ↔ take_rel n_u l_u VV).
Proof.
  intros -> ->. refine (take__take_rel n l VV).
Qed.

#[global] Hint Resolve take__take_rel': f_rel_funct_db.

Theorem take_rel_mk (n : Nats_u) (n_p : Nats_wf n ∧ True) (l : L_u) (l_p : L_wf l ∧ True):
  {VV: _ | take_rel n l VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, take_rel n l VV) (take (exist _ n n_p) (exist _ l l_p)) _);
  rewrite <- take__take_rel';
  quicksolve.
Qed.

#[global] Hint Resolve take_rel_mk: f_rel_funct_db.

#[global] Instance take_pack:
  @Pack
  (Nats ::RT λ (n : Nats), L ::RT λ (l : L), nilRT)
  (Nats_u ::UT (L_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((Nats ::RT λ (n : Nats), L ::RT λ (l : L), nilRT)) ((Nats_u ::UT (L_u ::UT nilUT))))
  L_u
  (λ (x_24544461 : ArgList (Nats ::RT λ (n : Nats), L ::RT λ (l : L), nilRT)) (v_x_24544461 : L_u),
   ltac:(flattenP (λ (n : Nats) (l : L) (VV : L_u), L_wf VV ∧ True) x_24544461 v_x_24544461)).
Proof.
  buildPackG take take_rel take__take_rel take_rel_funct.
Defined.

#[global] Instance take_upack: @uPack (Nats_u ::UT (L_u ::UT nilUT)) L_u.
Proof.
  buildUPackG take_rel take_rel_funct.
Defined.

Definition take_all_spec
  (n : Nats)
  (l : {l: L_u | L_wf l
                 ∧ ∃ length_res,
                   length_rel l length_res ∧ ∃ geqN_res, geqN_rel ⌊ n ⌋ length_res geqN_res ∧ is_true geqN_res}):
  Type :=
  {{∃ take_res, take_rel ⌊ n ⌋ ⌊ l ⌋ take_res ∧ take_res == ⌊ l ⌋}}.

#[global] Hint Unfold take_all_spec: lia_unfold.

Theorem take_all
  (n : Nats)
  (l : {l: L_u | L_wf l
                 ∧ ∃ length_res,
                   length_rel l length_res ∧ ∃ geqN_res, geqN_rel ⌊ n ⌋ length_res geqN_res ∧ is_true geqN_res}):
  take_all_spec n l.
Proof.
  destruct n as [n n_p].
  destruct l as [l l_p].
  try revert l_p; generalize dependent l; induction n as [n IH_n|]; intros.
  - destruct l as [x xs|].
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit), ∃ take_res, take_rel n l take_res ∧ take_res == l)
              (IH_n ltac:(try clear IH_n; solver) xs ltac:(try clear IH_n; solver))
              ltac:(solver)).
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit), ∃ take_res, take_rel n l take_res ∧ take_res == l)
              (# unit)
              ltac:(solver)).
  - destruct l as [lq_anf7205759403792803872 lq_anf7205759403792803873|].
    + intros; exfalso; solver.
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit), ∃ take_res, take_rel n l take_res ∧ take_res == l)
              (# unit)
              ltac:(solver)).
Qed.

Definition zip_spec (lq_tmp0 lq_tmp1 : L): Type :=
  L2.

#[global] Hint Unfold zip_spec: lia_unfold.

Definition zip (lq_tmp0 lq_tmp1 : L): zip_spec lq_tmp0 lq_tmp1.
Proof.
  destruct lq_tmp0 as [lq_tmp0 lq_tmp0_p].
  destruct lq_tmp1 as [lq_tmp1 lq_tmp1_p].
  try revert lq_tmp1_p; generalize dependent lq_tmp1;
  induction lq_tmp0 as [lq_anf7205759403792803732 lq_anf7205759403792803733 IH_lq_anf7205759403792803733|];
  intros.
  - destruct lq_tmp1 as [lq_anf7205759403792803730 lq_anf7205759403792803731|].
    + refine (App2
              (MkPair (# lq_anf7205759403792803732) (# lq_anf7205759403792803730))
              (IH_lq_anf7205759403792803733
               ltac:(try clear IH_lq_anf7205759403792803733; solver)
               lq_anf7205759403792803731
               ltac:(try clear IH_lq_anf7205759403792803733; solver))).
    + refine Emp2.
  - refine Emp2.
Defined.

Inductive zip_rel: L_u → L_u → L2_u → Prop :=
  | zip_Emp_x: ∀ lq_tmp1, zip_rel Emp_u lq_tmp1 Emp2_u
  | zip_App_Emp: ∀ lq_anf7205759403792803732 lq_anf7205759403792803733,
                 zip_rel (App_u lq_anf7205759403792803732 lq_anf7205759403792803733) Emp_u Emp2_u
  | zip_App_App: ∀ lq_anf7205759403792803732 lq_anf7205759403792803733 lq_anf7205759403792803730 lq_anf7205759403792803731 zip_res,
                 zip_rel lq_anf7205759403792803733 lq_anf7205759403792803731 zip_res
                 → zip_rel
                   (App_u lq_anf7205759403792803732 lq_anf7205759403792803733)
                   (App_u lq_anf7205759403792803730 lq_anf7205759403792803731)
                   (App2_u (MkPair_u lq_anf7205759403792803732 lq_anf7205759403792803730) zip_res).

#[global] Hint Constructors zip_rel: core_hint_db.

#[global] Instance zip_lookup_rel: dictionary rel zip := { lookup' := zip_rel }.

#[global] Instance zip_getF: getFunc zip_rel := { getF' := zip }.

Theorem zip_rel_funct [lq_tmp0 lq_tmp1 : L_u]:
  ∀ (VV VV' : L2_u), zip_rel lq_tmp0 lq_tmp1 VV → (zip_rel lq_tmp0 lq_tmp1 VV' → VV = VV').
Proof.
  try revert lq_tmp1_p; generalize dependent lq_tmp1;
  induction lq_tmp0 as [lq_anf7205759403792803732 lq_anf7205759403792803733 IH_lq_anf7205759403792803733|];
  intros;
  [destruct lq_tmp1 as [lq_anf7205759403792803730 lq_anf7205759403792803731|] |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve zip_rel_funct: f_rel_funct_db.

Theorem zip_Emp_x_lem lq_tmp1 zip_Emp_x_lem_res:
  zip_rel Emp_u lq_tmp1 zip_Emp_x_lem_res ↔ zip_Emp_x_lem_res == Emp2_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite zip_Emp_x_lem: f_rel_back.

Theorem zip_App_Emp_lem lq_anf7205759403792803732 lq_anf7205759403792803733 zip_App_Emp_lem_res:
  zip_rel (App_u lq_anf7205759403792803732 lq_anf7205759403792803733) Emp_u zip_App_Emp_lem_res
  ↔ zip_App_Emp_lem_res == Emp2_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite zip_App_Emp_lem: f_rel_back.

Theorem zip_App_App_lem
  lq_anf7205759403792803730 lq_anf7205759403792803731 lq_anf7205759403792803732 lq_anf7205759403792803733 zip_App_App_lem_res:
  zip_rel
  (App_u lq_anf7205759403792803732 lq_anf7205759403792803733)
  (App_u lq_anf7205759403792803730 lq_anf7205759403792803731)
  zip_App_App_lem_res
  ↔ ∃ zip_res,
    zip_rel lq_anf7205759403792803733 lq_anf7205759403792803731 zip_res
    ∧ zip_App_App_lem_res
      == App2_u (MkPair_u lq_anf7205759403792803732 lq_anf7205759403792803730) zip_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite zip_App_App_lem: f_rel_back.

Theorem zip_rel_ex
  (lq_tmp0 : L_u) (lq_tmp0_p : L_wf lq_tmp0 ∧ True) (lq_tmp1 : L_u) (lq_tmp1_p : L_wf lq_tmp1 ∧ True):
  zip_rel lq_tmp0 lq_tmp1 ⌊ zip (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p) -⌋.
Proof.
  Opaque zip.
  existence_lemma_pre zip;
  try revert lq_tmp1_p; generalize dependent lq_tmp1;
  induction lq_tmp0 as [lq_anf7205759403792803732 lq_anf7205759403792803733 IH_lq_anf7205759403792803733|];
  intros;
  [destruct lq_tmp1 as [lq_anf7205759403792803730 lq_anf7205759403792803731|];
   [fix_notations;
    pose proof (IH_lq_anf7205759403792803733
                ltac:(try clear IH_lq_anf7205759403792803733; solver)
                lq_anf7205759403792803731
                ltac:(try clear IH_lq_anf7205759403792803733; solver)) as IH_90608459;
    try clear IH_lq_anf7205759403792803733 |
    fix_notations] |
   fix_notations];
  simpl in *.
  Transparent zip.
  all: (existence_lemma_quicksolve zip; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve zip_rel_ex: rel_ax_db.

#[global] Opaque zip.

Theorem zip__zip_rel_rw
  (lq_tmp0 : L_u)
  (lq_tmp0_p : L_wf lq_tmp0 ∧ True)
  (lq_tmp1 : L_u)
  (lq_tmp1_p : L_wf lq_tmp1 ∧ True)
  (VV : L2_u):
  ⌊ zip (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p) -⌋ = VV ↔ zip_rel lq_tmp0 lq_tmp1 VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite zip__zip_rel_rw: f_rel_funct_db.

#[global] Hint Resolve zip__zip_rel_rw: rel_ax_db.

#[global] Instance zip_lookup_rw: dictionary rwLem zip := { lookup' := zip__zip_rel_rw }.

Theorem zip__zip_rel (lq_tmp0 lq_tmp1 : L) (VV : L2_u):
  ⌊ zip lq_tmp0 lq_tmp1 -⌋ = VV ↔ zip_rel ⌊ lq_tmp0 ⌋ ⌊ lq_tmp1 ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite zip__zip_rel: f_rel_funct_db.

Theorem zip__zip_rel' (lq_tmp0_u lq_tmp1_u : L_u) (lq_tmp0 lq_tmp1 : L) (VV : L2_u):
  lq_tmp0_u = ⌊ lq_tmp0 ⌋
  → (lq_tmp1_u = ⌊ lq_tmp1 ⌋ → ⌊ zip lq_tmp0 lq_tmp1 -⌋ = VV ↔ zip_rel lq_tmp0_u lq_tmp1_u VV).
Proof.
  intros -> ->. refine (zip__zip_rel lq_tmp0 lq_tmp1 VV).
Qed.

#[global] Hint Resolve zip__zip_rel': f_rel_funct_db.

Theorem zip_rel_mk
  (lq_tmp0 : L_u) (lq_tmp0_p : L_wf lq_tmp0 ∧ True) (lq_tmp1 : L_u) (lq_tmp1_p : L_wf lq_tmp1 ∧ True):
  {VV: _ | zip_rel lq_tmp0 lq_tmp1 VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, zip_rel lq_tmp0 lq_tmp1 VV)
          (zip (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p))
          _);
  rewrite <- zip__zip_rel';
  quicksolve.
Qed.

#[global] Hint Resolve zip_rel_mk: f_rel_funct_db.

#[global] Instance zip_pack:
  @Pack
  (L ::RT λ (lq_tmp0 : L), L ::RT λ (lq_tmp1 : L), nilRT)
  (L_u ::UT (L_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((L ::RT λ (lq_tmp0 : L), L ::RT λ (lq_tmp1 : L), nilRT)) ((L_u ::UT (L_u ::UT nilUT))))
  L2_u
  (λ (x_59358093 : ArgList (L ::RT λ (lq_tmp0 : L), L ::RT λ (lq_tmp1 : L), nilRT))
     (v_x_59358093 : L2_u),
   ltac:(flattenP (λ (lq_tmp0 lq_tmp1 : L) (VV : L2_u), L2_wf VV ∧ True) x_59358093 v_x_59358093)).
Proof.
  buildPackG zip zip_rel zip__zip_rel zip_rel_funct.
Defined.

#[global] Instance zip_upack: @uPack (L_u ::UT (L_u ::UT nilUT)) L2_u.
Proof.
  buildUPackG zip_rel zip_rel_funct.
Defined.

Definition length_zip_spec
  (n : Nats)
  (l : {l: L_u | L_wf l ∧ ∃ length_res, length_rel l length_res ∧ length_res == ⌊ n ⌋})
  (m : {m: L_u | L_wf m ∧ ∃ length_res, length_rel m length_res ∧ length_res == ⌊ n ⌋}):
  Type :=
  {{∃ zip_res,
    zip_rel ⌊ l ⌋ ⌊ m ⌋ zip_res
    ∧ ∃ length2_res, length2_rel zip_res length2_res ∧ length2_res == ⌊ n ⌋}}.

#[global] Hint Unfold length_zip_spec: lia_unfold.

Theorem length_zip
  (n : Nats)
  (l : {l: L_u | L_wf l ∧ ∃ length_res, length_rel l length_res ∧ length_res == ⌊ n ⌋})
  (m : {m: L_u | L_wf m ∧ ∃ length_res, length_rel m length_res ∧ length_res == ⌊ n ⌋}):
  length_zip_spec n l m.
Proof.
  destruct n as [n n_p].
  destruct l as [l l_p].
  destruct m as [m m_p].
  try revert m_p; generalize dependent m; try revert l_p; generalize dependent l;
  induction n as [n IH_n|];
  intros.
  - destruct l as [x xs|].
    + destruct m as [y ys|].
      ** refine (subsumptionCast
                 Unit
                 (λ (VV : Unit),
                  ∃ zip_res, zip_rel l m zip_res ∧ ∃ length2_res, length2_rel zip_res length2_res ∧ length2_res == n)
                 (IH_n
                  ltac:(try clear IH_n; solver)
                  xs
                  ltac:(try clear IH_n; solver)
                  ys
                  ltac:(try clear IH_n; solver))
                 ltac:(solver)).
      ** intros; exfalso; solver.
    + intros; exfalso; solver.
  - destruct l as [lq_anf7205759403792803771 lq_anf7205759403792803772|].
    + intros; exfalso; solver.
    + destruct m as [lq_anf7205759403792803769 lq_anf7205759403792803770|].
      ** intros; exfalso; solver.
      ** refine (subsumptionCast
                 Unit
                 (λ (VV : Unit),
                  ∃ zip_res, zip_rel l m zip_res ∧ ∃ length2_res, length2_rel zip_res length2_res ∧ length2_res == n)
                 (# unit)
                 ltac:(solver)).
Qed.

Definition length_zipWith_spec
  (n : Nats)
  (f : @Pack
       ({VV: Z | True}
        ::RT λ (f : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({VV: Z | True}
  ::RT λ (f : {VV: Z | True}),
       {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_64625469 : ArgList ({VV: Z | True}
                                 ::RT λ (f : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_64625469 : Z),
        ltac:(flattenP (λ (f lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_64625469 v_x_64625469)))
  (l : {l: L_u | L_wf l ∧ ∃ length_res, length_rel l length_res ∧ length_res == ⌊ n ⌋})
  (m : {m: L_u | L_wf m ∧ ∃ length_res, length_rel m length_res ∧ length_res == ⌊ n ⌋}):
  Type :=
  {{∃ zip_res,
    zip_rel ⌊ l ⌋ ⌊ m ⌋ zip_res
    ∧ ∃ length2_res, length2_rel zip_res length2_res ∧ length2_res == ⌊ n ⌋}}.

#[global] Hint Unfold length_zipWith_spec: lia_unfold.

Theorem length_zipWith
  (n : Nats)
  (f : @Pack
       ({VV: Z | True}
        ::RT λ (f : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({VV: Z | True}
  ::RT λ (f : {VV: Z | True}),
       {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_64625469 : ArgList ({VV: Z | True}
                                 ::RT λ (f : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_64625469 : Z),
        ltac:(flattenP (λ (f lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_64625469 v_x_64625469)))
  (l : {l: L_u | L_wf l ∧ ∃ length_res, length_rel l length_res ∧ length_res == ⌊ n ⌋})
  (m : {m: L_u | L_wf m ∧ ∃ length_res, length_rel m length_res ∧ length_res == ⌊ n ⌋}):
  length_zipWith_spec n f l m.
Proof.
  destruct n as [n n_p].
  destruct l as [l l_p].
  destruct m as [m m_p].
  try revert m_p; generalize dependent m;
  try revert l_p; generalize dependent l;
  try revert f_p; generalize dependent f;
  induction n as [n IH_n|];
  intros.
  - destruct l as [x xs|].
    + destruct m as [y ys|].
      ** refine (subsumptionCast
                 Unit
                 (λ (VV : Unit),
                  ∃ zip_res, zip_rel l m zip_res ∧ ∃ length2_res, length2_rel zip_res length2_res ∧ length2_res == n)
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
  - destruct l as [lq_anf7205759403792803792 lq_anf7205759403792803793|].
    + intros; exfalso; solver.
    + destruct m as [lq_anf7205759403792803790 lq_anf7205759403792803791|].
      ** intros; exfalso; solver.
      ** refine (subsumptionCast
                 Unit
                 (λ (VV : Unit),
                  ∃ zip_res, zip_rel l m zip_res ∧ ∃ length2_res, length2_rel zip_res length2_res ∧ length2_res == n)
                 (# unit)
                 ltac:(solver)).
Qed.

Definition zipWith_spec
  (f : @Pack
       ({VV: Z | True}
        ::RT λ (f : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({VV: Z | True}
  ::RT λ (f : {VV: Z | True}),
       {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_64625469 : ArgList ({VV: Z | True}
                                 ::RT λ (f : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_64625469 : Z),
        ltac:(flattenP (λ (f lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_64625469 v_x_64625469)))
  (l m : L):
  Type :=
  L.

#[global] Hint Unfold zipWith_spec: lia_unfold.

Definition zipWith
  (f : @Pack
       ({VV: Z | True}
        ::RT λ (f : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({VV: Z | True}
  ::RT λ (f : {VV: Z | True}),
       {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_64625469 : ArgList ({VV: Z | True}
                                 ::RT λ (f : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_64625469 : Z),
        ltac:(flattenP (λ (f lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_64625469 v_x_64625469)))
  (l m : L):
  zipWith_spec f l m.
Proof.
  destruct l as [l l_p].
  destruct m as [m m_p].
  try revert m_p; generalize dependent m; try revert f_p; generalize dependent f;
  induction l as [lq_anf7205759403792803748 lq_anf7205759403792803749 IH_lq_anf7205759403792803749|];
  intros.
  - destruct m as [lq_anf7205759403792803746 lq_anf7205759403792803747|].
    + refine (App
              (getPackF f (# lq_anf7205759403792803748) (# lq_anf7205759403792803746))
              (IH_lq_anf7205759403792803749
               ltac:(try clear IH_lq_anf7205759403792803749; solver)
               f
               lq_anf7205759403792803747
               ltac:(try clear IH_lq_anf7205759403792803749; solver))).
    + refine Emp.
  - refine Emp.
Defined.

Inductive zipWith_rel: @uPack (Z ::UT (Z ::UT nilUT)) Z → L_u → L_u → L_u → Prop :=
  | zipWith_x_Emp_x: ∀ (f : @uPack (Z ::UT (Z ::UT nilUT)) Z) m, zipWith_rel f Emp_u m Emp_u
  | zipWith_x_App_Emp: ∀ (f : @uPack (Z ::UT (Z ::UT nilUT)) Z)
                         lq_anf7205759403792803748 lq_anf7205759403792803749,
                       zipWith_rel f (App_u lq_anf7205759403792803748 lq_anf7205759403792803749) Emp_u Emp_u
  | zipWith_x_App_App: ∀ (f : @uPack (Z ::UT (Z ::UT nilUT)) Z)
                         lq_anf7205759403792803748 lq_anf7205759403792803749 lq_anf7205759403792803746 lq_anf7205759403792803747 zipWith_res,
                       zipWith_rel f lq_anf7205759403792803749 lq_anf7205759403792803747 zipWith_res
                       → ∀ f_res,
                         getUPackRel f lq_anf7205759403792803748 lq_anf7205759403792803746 f_res
                         → zipWith_rel
                           f
                           (App_u lq_anf7205759403792803748 lq_anf7205759403792803749)
                           (App_u lq_anf7205759403792803746 lq_anf7205759403792803747)
                           (App_u f_res zipWith_res).

#[global] Hint Constructors zipWith_rel: core_hint_db.

#[global] Instance zipWith_lookup_rel: dictionary rel zipWith := { lookup' := zipWith_rel }.

#[global] Instance zipWith_getF: getFunc zipWith_rel := { getF' := zipWith }.

Theorem zipWith_rel_funct [f : @uPack (Z ::UT (Z ::UT nilUT)) Z] [l m : L_u]:
  ∀ (VV VV' : L_u), zipWith_rel f l m VV → (zipWith_rel f l m VV' → VV = VV').
Proof.
  try revert m_p; generalize dependent m; try revert f_p; generalize dependent f;
  induction l as [lq_anf7205759403792803748 lq_anf7205759403792803749 IH_lq_anf7205759403792803749|];
  intros;
  [destruct m as [lq_anf7205759403792803746 lq_anf7205759403792803747|] |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve zipWith_rel_funct: f_rel_funct_db.

Theorem zipWith_x_Emp_x_lem f m zipWith_x_Emp_x_lem_res:
  zipWith_rel f Emp_u m zipWith_x_Emp_x_lem_res ↔ zipWith_x_Emp_x_lem_res == Emp_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite zipWith_x_Emp_x_lem: f_rel_back.

Theorem zipWith_x_App_Emp_lem
  f lq_anf7205759403792803748 lq_anf7205759403792803749 zipWith_x_App_Emp_lem_res:
  zipWith_rel
  f
  (App_u lq_anf7205759403792803748 lq_anf7205759403792803749)
  Emp_u
  zipWith_x_App_Emp_lem_res
  ↔ zipWith_x_App_Emp_lem_res == Emp_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite zipWith_x_App_Emp_lem: f_rel_back.

Theorem zipWith_x_App_App_lem
  f lq_anf7205759403792803746 lq_anf7205759403792803747 lq_anf7205759403792803748 lq_anf7205759403792803749 zipWith_x_App_App_lem_res:
  zipWith_rel
  f
  (App_u lq_anf7205759403792803748 lq_anf7205759403792803749)
  (App_u lq_anf7205759403792803746 lq_anf7205759403792803747)
  zipWith_x_App_App_lem_res
  ↔ ∃ zipWith_res,
    zipWith_rel f lq_anf7205759403792803749 lq_anf7205759403792803747 zipWith_res
    ∧ ∃ f_res,
      getUPackRel f lq_anf7205759403792803748 lq_anf7205759403792803746 f_res
      ∧ zipWith_x_App_App_lem_res == App_u f_res zipWith_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite zipWith_x_App_App_lem: f_rel_back.

Theorem zipWith_rel_ex
  (f : @Pack
       ({f: Z | True}
        ::RT λ (f : {f: Z | True}), {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({f: Z | True}
  ::RT λ (f : {f: Z | True}),
       {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_66360476 : ArgList ({f: Z | True}
                                 ::RT λ (f : {f: Z | True}),
                                      {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_66360476 : Z),
        ltac:(flattenP (λ (f : {f: Z | True}) (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z),
 True) x_66360476 v_x_66360476)))
  (l : L_u)
  (l_p : L_wf l ∧ True)
  (m : L_u)
  (m_p : L_wf m ∧ True):
  zipWith_rel ⌊ f ⌋ l m ⌊ zipWith f (exist _ l l_p) (exist _ m m_p) -⌋.
Proof.
  Opaque zipWith.
  existence_lemma_pre zipWith;
  try revert m_p; generalize dependent m; try revert f_p; generalize dependent f;
  induction l as [lq_anf7205759403792803748 lq_anf7205759403792803749 IH_lq_anf7205759403792803749|];
  intros;
  [destruct m as [lq_anf7205759403792803746 lq_anf7205759403792803747|];
   [fix_notations;
    pose proof (IH_lq_anf7205759403792803749
                ltac:(try clear IH_lq_anf7205759403792803749; solver)
                f
                lq_anf7205759403792803747
                ltac:(try clear IH_lq_anf7205759403792803749; solver)) as IH_15814723;
    try clear IH_lq_anf7205759403792803749 |
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
       ({f: Z | True}
        ::RT λ (f : {f: Z | True}), {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({f: Z | True}
  ::RT λ (f : {f: Z | True}),
       {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_66360476 : ArgList ({f: Z | True}
                                 ::RT λ (f : {f: Z | True}),
                                      {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_66360476 : Z),
        ltac:(flattenP (λ (f : {f: Z | True}) (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z),
 True) x_66360476 v_x_66360476)))
  (l : L_u)
  (l_p : L_wf l ∧ True)
  (m : L_u)
  (m_p : L_wf m ∧ True)
  (VV : L_u):
  ⌊ zipWith f (exist _ l l_p) (exist _ m m_p) -⌋ = VV ↔ zipWith_rel ⌊ f ⌋ l m VV.
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
        ::RT λ (f : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({VV: Z | True}
  ::RT λ (f : {VV: Z | True}),
       {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_64625469 : ArgList ({VV: Z | True}
                                 ::RT λ (f : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_64625469 : Z),
        ltac:(flattenP (λ (f lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_64625469 v_x_64625469)))
  (l m : L)
  (VV : L_u):
  ⌊ zipWith f l m -⌋ = VV ↔ zipWith_rel ⌊ f ⌋ ⌊ l ⌋ ⌊ m ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite zipWith__zipWith_rel: f_rel_funct_db.

Theorem zipWith__zipWith_rel'
  (f_u : @uPack (Z ::UT (Z ::UT nilUT)) Z)
  (l_u m_u : L_u)
  (f : @Pack
       ({VV: Z | True}
        ::RT λ (f : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({VV: Z | True}
  ::RT λ (f : {VV: Z | True}),
       {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_64625469 : ArgList ({VV: Z | True}
                                 ::RT λ (f : {VV: Z | True}), {VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_64625469 : Z),
        ltac:(flattenP (λ (f lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_64625469 v_x_64625469)))
  (l m : L)
  (VV : L_u):
  f_u = ⌊ f ⌋ → (l_u = ⌊ l ⌋ → (m_u = ⌊ m ⌋ → ⌊ zipWith f l m -⌋ = VV ↔ zipWith_rel f_u l_u m_u VV)).
Proof.
  intros -> -> ->. refine (zipWith__zipWith_rel f l m VV).
Qed.

#[global] Hint Resolve zipWith__zipWith_rel': f_rel_funct_db.

Theorem zipWith_rel_mk
  (f : @Pack
       ({f: Z | True}
        ::RT λ (f : {f: Z | True}), {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT (Z ::UT nilUT))
       ltac:(mkProjectsArgListTG (({f: Z | True}
  ::RT λ (f : {f: Z | True}),
       {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT (Z ::UT nilUT))))
       Z
       (λ (x_66360476 : ArgList ({f: Z | True}
                                 ::RT λ (f : {f: Z | True}),
                                      {lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_66360476 : Z),
        ltac:(flattenP (λ (f : {f: Z | True}) (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z),
 True) x_66360476 v_x_66360476)))
  (l : L_u)
  (l_p : L_wf l ∧ True)
  (m : L_u)
  (m_p : L_wf m ∧ True):
  {VV: _ | zipWith_rel (packProj f) l m VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, zipWith_rel (packProj f) l m VV)
          (zipWith f (exist _ l l_p) (exist _ m m_p))
          _);
  rewrite <- zipWith__zipWith_rel';
  quicksolve.
Qed.

#[global] Hint Resolve zipWith_rel_mk: f_rel_funct_db.

Definition zip_take_spec (l m : L): Type :=
  {{∃ zip_res,
    zip_rel ⌊ l ⌋ ⌊ m ⌋ zip_res
    ∧ ∃ length_res,
      length_rel ⌊ l ⌋ length_res
      ∧ ∃ take_res,
        take_rel length_res ⌊ m ⌋ take_res
        ∧ ∃ length_res_2,
          length_rel ⌊ m ⌋ length_res_2
          ∧ ∃ take_res_2,
            take_rel length_res_2 ⌊ l ⌋ take_res_2
            ∧ ∃ zip_res_2, zip_rel take_res_2 take_res zip_res_2 ∧ zip_res == zip_res_2}}.

#[global] Hint Unfold zip_take_spec: lia_unfold.

Theorem zip_take (l m : L): zip_take_spec l m.
Proof.
  destruct l as [l l_p].
  destruct m as [m m_p].
  try revert m_p; generalize dependent m;
  induction l as [lq_anf7205759403792803854 lq_anf7205759403792803855 IH_lq_anf7205759403792803855|];
  intros.
  - destruct m as [lq_anf7205759403792803834 lq_anf7205759403792803835|].
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∃ zip_res,
               zip_rel l m zip_res
               ∧ ∃ length_res,
                 length_rel l length_res
                 ∧ ∃ take_res,
                   take_rel length_res m take_res
                   ∧ ∃ length_res_2,
                     length_rel m length_res_2
                     ∧ ∃ take_res_2,
                       take_rel length_res_2 l take_res_2
                       ∧ ∃ zip_res_2, zip_rel take_res_2 take_res zip_res_2 ∧ zip_res == zip_res_2)
              (IH_lq_anf7205759403792803855
               ltac:(try clear IH_lq_anf7205759403792803855; solver)
               lq_anf7205759403792803835
               ltac:(try clear IH_lq_anf7205759403792803855; solver))
              ltac:(solver)).
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∃ zip_res,
               zip_rel l m zip_res
               ∧ ∃ length_res,
                 length_rel l length_res
                 ∧ ∃ take_res,
                   take_rel length_res m take_res
                   ∧ ∃ length_res_2,
                     length_rel m length_res_2
                     ∧ ∃ take_res_2,
                       take_rel length_res_2 l take_res_2
                       ∧ ∃ zip_res_2, zip_rel take_res_2 take_res zip_res_2 ∧ zip_res == zip_res_2)
              (# unit)
              ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ zip_res,
             zip_rel l m zip_res
             ∧ ∃ length_res,
               length_rel l length_res
               ∧ ∃ take_res,
                 take_rel length_res m take_res
                 ∧ ∃ length_res_2,
                   length_rel m length_res_2
                   ∧ ∃ take_res_2,
                     take_rel length_res_2 l take_res_2
                     ∧ ∃ zip_res_2, zip_rel take_res_2 take_res zip_res_2 ∧ zip_res == zip_res_2)
            (let _: (True
                     ∧ VV
                       == ⌊ zip
                            (take (length (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) Emp)
                            (take Zero (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) ⌋)
                    ∧ VV == ⌊ zip Emp Emp ⌋ :=
             ⌈ let _: (True
                       ∧ VV
                         == ⌊ zip
                              (take (length (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) Emp)
                              (take (length Emp) (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) ⌋)
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
                  ∧ (True
                     ∧ VV == ⌊ zip (take (length (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) Emp) Emp ⌋))
                 (zip
                  (take (length (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) Emp)
                  (take (length Emp) (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))))
                 ltac:(solver) ⌉ in
               let _: (True
                       ∧ VV == ⌊ zip (take (length (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) Emp) Emp ⌋)
                      ∧ VV == ⌊ zip Emp Emp ⌋ :=
               ⌈ let _: ⌊ zip Emp Emp ⌋
                        == ⌊ zip (take (length (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) Emp) Emp ⌋ :=
                 ltac:(solver) in
                 subsumptionCast
                 L2_u
                 (λ (VV : L2_u), L2_wf VV ∧ (True ∧ VV == ⌊ zip Emp Emp ⌋))
                 (zip (take (length (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) Emp) Emp)
                 ltac:(solver) ⌉ in
               let _: (True ∧ VV == ⌊ zip Emp Emp ⌋)
                      ∧ VV == ⌊ zip Emp (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver)) ⌋ :=
               ⌈ let _: ⌊ zip Emp (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver)) ⌋ == ⌊ zip Emp Emp ⌋ :=
                 ltac:(solver) in
                 subsumptionCast
                 L2_u
                 (λ (VV : L2_u),
                  L2_wf VV ∧ (True ∧ VV == ⌊ zip Emp (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver)) ⌋))
                 (zip Emp Emp)
                 ltac:(solver) ⌉ in
               let _: ⌊ zip Emp Emp ⌋
                      == ⌊ zip
                           (take (length (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) Emp)
                           (take Zero (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) ⌋ :=
               ltac:(solver) in
               subsumptionCast
               L2_u
               (λ (VV : L2_u), L2_wf VV ∧ (True ∧ VV == ⌊ zip Emp Emp ⌋))
               (zip
                (take (length (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))) Emp)
                (take Zero (exist (λ (m : L_u), L_wf m ∧ True) m ltac:(solver))))
               ltac:(solver) ⌉ in
             # unit)
            ltac:(solver)).
Qed.
