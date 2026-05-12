From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Set Universe Polymorphism. 
From Coq Require Import Unicode.Utf8.

Inductive Identity_u: Type :=
  | Val_u: Z → Identity_u.

Fixpoint Identity_eq (x y : Identity_u): bool :=
  match (x, y) with | (Val_u n, Val_u n') => true && (n ==? n') end.

Theorem Identity_eq_refl : ∀ (x : Identity_u), is_true (Identity_eq x x).
Proof.
  eq_refl_rec.
Qed.

#[global] Hint Resolve Identity_eq_refl: eq_hint_db.

Theorem Identity_eqb_eq : ∀ (s t : Identity_u), is_true (Identity_eq s t) → s = t.
Proof.
  eqb_eq_lem.
Qed.

#[global] Hint Resolve Identity_eqb_eq: eq_hint_db.

#[global] Instance leibnitz_eq_Identity: LeibnitzEqB := {
    equalB' := Identity_eq;
    refl' := Identity_eq_refl;
    eqb_eq' := Identity_eqb_eq }.

Fixpoint Identity_wf (x : Identity_u): Prop :=
  match x with | Val_u n => True end.

Theorem Identity_wf_ref [p : Identity_u → Prop] (tm : {v: Identity_u | Identity_wf v ∧ p v}):
  Identity_wf ⌊ tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation Identity := {x: Identity_u | Identity_wf x ∧ True}.

Definition Val_lem (n : {n: Z | True}): Identity_wf (Val_u ⌊ n ⌋) ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Val (n : {n: Z | True}): Identity :=
  exist _ (Val_u ⌊ n ⌋) (Val_lem n).

#[global] Hint Resolve Identity_wf_ref: wf_constr_db.

#[global] Hint Unfold Identity_wf: wf_constr_db.

#[global] Hint Resolve Identity_eq: ref_constr_db.

#[global] Hint Unfold Val: ref_constr_db.

Definition compose_spec
  (ds_d3Ba : Identity)
  (f : @Pack
       ({VV: Z | True} ::RT λ (x : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (x : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Identity_u
       (λ (x_32508782 : ArgList ({VV: Z | True} ::RT λ (x : {VV: Z | True}), nilRT))
          (v_x_32508782 : Identity_u),
        ltac:(flattenP (λ (x : {VV: Z | True}) (VV : Identity_u), Identity_wf VV ∧ True) x_32508782 v_x_32508782))):
  Type :=
  Identity.

#[global] Hint Unfold compose_spec: lia_unfold.

Definition compose
  (ds_d3Ba : Identity)
  (f : @Pack
       ({VV: Z | True} ::RT λ (x : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (x : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Identity_u
       (λ (x_32508782 : ArgList ({VV: Z | True} ::RT λ (x : {VV: Z | True}), nilRT))
          (v_x_32508782 : Identity_u),
        ltac:(flattenP (λ (x : {VV: Z | True}) (VV : Identity_u), Identity_wf VV ∧ True) x_32508782 v_x_32508782))):
  compose_spec ds_d3Ba f.
Proof.
  destruct ds_d3Ba as [ds_d3Ba ds_d3Ba_p].
  destruct ds_d3Ba as [x].
  - refine (getPackF f (# x)).
Defined.

Inductive compose_rel: Identity_u → @uPack (Z ::UT nilUT) Identity_u → Identity_u → Prop :=
  | compose_Val_x: ∀ x (f : @uPack (Z ::UT nilUT) Identity_u) (f_res : Identity_u),
                   getUPackRel f x f_res → compose_rel (Val_u x) f f_res.

#[global] Hint Constructors compose_rel: core_hint_db.

#[global] Instance compose_lookup_rel: dictionary rel compose := { lookup' := compose_rel }.

#[global] Instance compose_getF: getFunc compose_rel := { getF' := compose }.

Theorem compose_rel_funct [ds_d3Ba : Identity_u] [f : @uPack (Z ::UT nilUT) Identity_u]:
  ∀ (VV VV' : Identity_u), compose_rel ds_d3Ba f VV → (compose_rel ds_d3Ba f VV' → VV = VV').
Proof.
  destruct ds_d3Ba as [x]; rel_functionhood_body.
Qed.

#[global] Hint Resolve compose_rel_funct: f_rel_funct_db.

Theorem compose_Val_x_lem f x compose_Val_x_lem_res:
  compose_rel (Val_u x) f compose_Val_x_lem_res
  ↔ ∃ (f_res : Identity_u), getUPackRel f x f_res ∧ compose_Val_x_lem_res == f_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite compose_Val_x_lem: f_rel_back.

Theorem compose_rel_ex
  (ds_d3Ba : Identity_u)
  (ds_d3Ba_p : Identity_wf ds_d3Ba ∧ True)
  (f : @Pack
       ({x: Z | True} ::RT λ (x : {x: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({x: Z | True} ::RT λ (x : {x: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Identity_u
       (λ (x_11473763 : ArgList ({x: Z | True} ::RT λ (x : {x: Z | True}), nilRT))
          (v_x_11473763 : Identity_u),
        ltac:(flattenP (λ (x : {x: Z | True}) (VV : Identity_u), Identity_wf VV ∧ True) x_11473763 v_x_11473763))):
  compose_rel ds_d3Ba ⌊ f ⌋ ⌊ compose (exist _ ds_d3Ba ds_d3Ba_p) f -⌋.
Proof.
  Opaque compose.
  existence_lemma_pre compose;
  destruct ds_d3Ba as [x];
  [fix_notations];
  simpl in *.
  Transparent compose.
  all: (existence_lemma_quicksolve compose; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve compose_rel_ex: rel_ax_db.

#[global] Opaque compose.

Theorem compose__compose_rel_rw
  (ds_d3Ba : Identity_u)
  (ds_d3Ba_p : Identity_wf ds_d3Ba ∧ True)
  (f : @Pack
       ({x: Z | True} ::RT λ (x : {x: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({x: Z | True} ::RT λ (x : {x: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Identity_u
       (λ (x_11473763 : ArgList ({x: Z | True} ::RT λ (x : {x: Z | True}), nilRT))
          (v_x_11473763 : Identity_u),
        ltac:(flattenP (λ (x : {x: Z | True}) (VV : Identity_u), Identity_wf VV ∧ True) x_11473763 v_x_11473763)))
  (VV : Identity_u):
  ⌊ compose (exist _ ds_d3Ba ds_d3Ba_p) f -⌋ = VV ↔ compose_rel ds_d3Ba ⌊ f ⌋ VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite compose__compose_rel_rw: f_rel_funct_db.

#[global] Hint Resolve compose__compose_rel_rw: rel_ax_db.

#[global] Instance compose_lookup_rw: dictionary rwLem compose := {
    lookup' := compose__compose_rel_rw }.

Theorem compose__compose_rel
  (ds_d3Ba : Identity)
  (f : @Pack
       ({VV: Z | True} ::RT λ (x : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (x : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Identity_u
       (λ (x_32508782 : ArgList ({VV: Z | True} ::RT λ (x : {VV: Z | True}), nilRT))
          (v_x_32508782 : Identity_u),
        ltac:(flattenP (λ (x : {VV: Z | True}) (VV : Identity_u), Identity_wf VV ∧ True) x_32508782 v_x_32508782)))
  (VV : Identity_u):
  ⌊ compose ds_d3Ba f -⌋ = VV ↔ compose_rel ⌊ ds_d3Ba ⌋ ⌊ f ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite compose__compose_rel: f_rel_funct_db.

Theorem compose__compose_rel'
  (ds_d3Ba_u : Identity_u)
  (f_u : @uPack (Z ::UT nilUT) Identity_u)
  (ds_d3Ba : Identity)
  (f : @Pack
       ({VV: Z | True} ::RT λ (x : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (x : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Identity_u
       (λ (x_32508782 : ArgList ({VV: Z | True} ::RT λ (x : {VV: Z | True}), nilRT))
          (v_x_32508782 : Identity_u),
        ltac:(flattenP (λ (x : {VV: Z | True}) (VV : Identity_u), Identity_wf VV ∧ True) x_32508782 v_x_32508782)))
  (VV : Identity_u):
  ds_d3Ba_u = ⌊ ds_d3Ba ⌋
  → (f_u = ⌊ f ⌋ → ⌊ compose ds_d3Ba f -⌋ = VV ↔ compose_rel ds_d3Ba_u f_u VV).
Proof.
  intros -> ->. refine (compose__compose_rel ds_d3Ba f VV).
Qed.

#[global] Hint Resolve compose__compose_rel': f_rel_funct_db.

Theorem compose_rel_mk
  (ds_d3Ba : Identity_u)
  (ds_d3Ba_p : Identity_wf ds_d3Ba ∧ True)
  (f : @Pack
       ({x: Z | True} ::RT λ (x : {x: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({x: Z | True} ::RT λ (x : {x: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Identity_u
       (λ (x_11473763 : ArgList ({x: Z | True} ::RT λ (x : {x: Z | True}), nilRT))
          (v_x_11473763 : Identity_u),
        ltac:(flattenP (λ (x : {x: Z | True}) (VV : Identity_u), Identity_wf VV ∧ True) x_11473763 v_x_11473763))):
  {VV: _ | compose_rel ds_d3Ba (packProj f) VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, compose_rel ds_d3Ba (packProj f) VV)
          (compose (exist _ ds_d3Ba ds_d3Ba_p) f)
          _);
  rewrite <- compose__compose_rel';
  quicksolve.
Qed.

#[global] Hint Resolve compose_rel_mk: f_rel_funct_db.

Definition retrn_spec (v : {v: Z | True}): Type :=
  Identity.

#[global] Hint Unfold retrn_spec: lia_unfold.

Definition retrn (v : {v: Z | True}): retrn_spec v.
Proof.
  destruct v as [v v_p]. refine (Val (# v)).
Defined.

Inductive retrn_rel: Z → Identity_u → Prop :=
  | retrn_Constr: ∀ v, retrn_rel v (Val_u v).

#[global] Hint Constructors retrn_rel: core_hint_db.

#[global] Instance retrn_lookup_rel: dictionary rel retrn := { lookup' := retrn_rel }.

#[global] Instance retrn_getF: getFunc retrn_rel := { getF' := retrn }.

Theorem retrn_rel_funct [v : Z]:
  ∀ (VV VV' : Identity_u), retrn_rel v VV → (retrn_rel v VV' → VV = VV').
Proof.
  rel_functionhood_body.
Qed.

#[global] Hint Resolve retrn_rel_funct: f_rel_funct_db.

Theorem retrn_inv_lem v retrn_inv_lem_res:
  retrn_rel v retrn_inv_lem_res ↔ retrn_inv_lem_res == Val_u v.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite retrn_inv_lem: f_rel_back.

Theorem retrn_rel_ex (v : Z) (v_p : True): retrn_rel v ⌊ retrn (exist _ v v_p) -⌋.
Proof.
  Opaque retrn.
  existence_lemma_pre retrn; fix_notations; simpl in *.
  Transparent retrn.
  all: (existence_lemma_quicksolve retrn; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve retrn_rel_ex: rel_ax_db.

#[global] Opaque retrn.

Theorem retrn__retrn_rel_rw (v : Z) (v_p : True) (VV : Identity_u):
  ⌊ retrn (exist _ v v_p) -⌋ = VV ↔ retrn_rel v VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite retrn__retrn_rel_rw: f_rel_funct_db.

#[global] Hint Resolve retrn__retrn_rel_rw: rel_ax_db.

#[global] Instance retrn_lookup_rw: dictionary rwLem retrn := { lookup' := retrn__retrn_rel_rw }.

Theorem retrn__retrn_rel (v : {v: Z | True}) (VV : Identity_u):
  ⌊ retrn v -⌋ = VV ↔ retrn_rel ⌊ v ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite retrn__retrn_rel: f_rel_funct_db.

Theorem retrn__retrn_rel' (v_u : Z) (v : {v: Z | True}) (VV : Identity_u):
  v_u = ⌊ v ⌋ → ⌊ retrn v -⌋ = VV ↔ retrn_rel v_u VV.
Proof.
  intros ->. refine (retrn__retrn_rel v VV).
Qed.

#[global] Hint Resolve retrn__retrn_rel': f_rel_funct_db.

Theorem retrn_rel_mk (v : Z) (v_p : True): {VV: _ | retrn_rel v VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, retrn_rel v VV) (retrn (exist _ v v_p)) _);
  rewrite <- retrn__retrn_rel';
  quicksolve.
Qed.

#[global] Hint Resolve retrn_rel_mk: f_rel_funct_db.

#[global] Instance retrn_pack:
  @Pack
  ({v: Z | True} ::RT λ (v : {v: Z | True}), nilRT)
  (Z ::UT nilUT)
  ltac:(mkProjectsArgListTG (({v: Z | True} ::RT λ (v : {v: Z | True}), nilRT)) ((Z ::UT nilUT)))
  Identity_u
  (λ (x_82100618 : ArgList ({v: Z | True} ::RT λ (v : {v: Z | True}), nilRT))
     (v_x_82100618 : Identity_u),
   ltac:(flattenP (λ (v : {v: Z | True}) (VV : Identity_u), Identity_wf VV ∧ True) x_82100618 v_x_82100618)).
Proof.
  buildPackG retrn retrn_rel retrn__retrn_rel retrn_rel_funct.
Defined.

#[global] Instance retrn_upack: @uPack (Z ::UT nilUT) Identity_u.
Proof.
  buildUPackG retrn_rel retrn_rel_funct.
Defined.

Definition leftIdentity_spec
  (x : {x: Z | True})
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Identity_u
       (λ (x_44453395 : ArgList ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT))
          (v_x_44453395 : Identity_u),
        ltac:(flattenP (λ (lq_tmp0 : {VV: Z | True}) (VV : Identity_u),
 Identity_wf VV ∧ True) x_44453395 v_x_44453395))):
  Type :=
  {{∃ (retrn_res : Identity_u),
    retrn_rel ⌊ x ⌋ retrn_res
    ∧ ∃ (compose_res : Identity_u),
      compose_rel retrn_res ⌊ f ⌋ compose_res
      ∧ ∃ (f_res : Identity_u), getPackRel f ⌊ x ⌋ f_res ∧ compose_res == f_res}}.

#[global] Hint Unfold leftIdentity_spec: lia_unfold.

Theorem leftIdentity
  (x : {x: Z | True})
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Identity_u
       (λ (x_44453395 : ArgList ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT))
          (v_x_44453395 : Identity_u),
        ltac:(flattenP (λ (lq_tmp0 : {VV: Z | True}) (VV : Identity_u),
 Identity_wf VV ∧ True) x_44453395 v_x_44453395))):
  leftIdentity_spec x f.
Proof.
  destruct x as [x x_p].
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (retrn_res : Identity_u),
           retrn_rel x retrn_res
           ∧ ∃ (compose_res : Identity_u),
             compose_rel retrn_res ⌊ f ⌋ compose_res
             ∧ ∃ (f_res : Identity_u), getPackRel f x f_res ∧ compose_res == f_res)
          (# unit)
          ltac:(solver)).
Qed.

Definition rightIdentity_spec (ds_d3B9 : Identity): Type :=
  {{∃ (compose_res : Identity_u),
    compose_rel ⌊ ds_d3B9 ⌋ retrn_upack compose_res ∧ compose_res == ⌊ ds_d3B9 ⌋}}.

#[global] Hint Unfold rightIdentity_spec: lia_unfold.

Theorem rightIdentity (ds_d3B9 : Identity): rightIdentity_spec ds_d3B9.
Proof.
  destruct ds_d3B9 as [ds_d3B9 ds_d3B9_p].
  destruct ds_d3B9 as [x].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (compose_res : Identity_u), compose_rel ds_d3B9 retrn_upack compose_res ∧ compose_res == ds_d3B9)
            (# unit)
            ltac:(solver)).
Qed.
