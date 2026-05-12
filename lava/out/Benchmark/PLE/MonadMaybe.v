From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Set Universe Polymorphism. 
From Coq Require Import Unicode.Utf8.

Inductive MaybeInt_u: Type :=
  | Just_u: Z → MaybeInt_u | Nothing_u: MaybeInt_u.

Fixpoint MaybeInt_eq (x y : MaybeInt_u): bool :=
  match (x, y) with
  | (Just_u VV, Just_u VV') => true && (VV ==? VV')
  | (Nothing_u, Nothing_u) => true
  | (_, _) => false
  end.

Theorem MaybeInt_eq_refl : ∀ (x : MaybeInt_u), is_true (MaybeInt_eq x x).
Proof.
  eq_refl_rec.
Qed.

#[global] Hint Resolve MaybeInt_eq_refl: eq_hint_db.

Theorem MaybeInt_eqb_eq : ∀ (s t : MaybeInt_u), is_true (MaybeInt_eq s t) → s = t.
Proof.
  eqb_eq_lem.
Qed.

#[global] Hint Resolve MaybeInt_eqb_eq: eq_hint_db.

#[global] Instance leibnitz_eq_MaybeInt: LeibnitzEqB := {
    equalB' := MaybeInt_eq;
    refl' := MaybeInt_eq_refl;
    eqb_eq' := MaybeInt_eqb_eq }.

Fixpoint MaybeInt_wf (x : MaybeInt_u): Prop :=
  match x with | Just_u VV => True | Nothing_u => True end.

Theorem MaybeInt_wf_ref [p : MaybeInt_u → Prop] (tm : {v: MaybeInt_u | MaybeInt_wf v ∧ p v}):
  MaybeInt_wf ⌊ tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation MaybeInt := {x: MaybeInt_u | MaybeInt_wf x ∧ True}.

Definition Just_lem (VV : {VV: Z | True}): MaybeInt_wf (Just_u ⌊ VV ⌋) ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Just (VV : {VV: Z | True}): MaybeInt :=
  exist _ (Just_u ⌊ VV ⌋) (Just_lem VV).

Definition Nothing_lem : MaybeInt_wf Nothing_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Nothing : MaybeInt :=
  exist _ Nothing_u Nothing_lem.

#[global] Hint Resolve MaybeInt_wf_ref: wf_constr_db.

#[global] Hint Unfold MaybeInt_wf: wf_constr_db.

#[global] Hint Resolve MaybeInt_eq: ref_constr_db.

#[global] Hint Unfold Just: ref_constr_db.

#[global] Hint Unfold Nothing: ref_constr_db.

Definition bind_spec
  (ds_d3S7 : MaybeInt)
  (ds_d3S8 : @Pack
             ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
             MaybeInt_u
             (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
                (v_x_10329927 : MaybeInt_u),
              ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : MaybeInt_u),
 MaybeInt_wf VV ∧ True) x_10329927 v_x_10329927))):
  Type :=
  MaybeInt.

#[global] Hint Unfold bind_spec: lia_unfold.

Definition bind
  (ds_d3S7 : MaybeInt)
  (ds_d3S8 : @Pack
             ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
             MaybeInt_u
             (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
                (v_x_10329927 : MaybeInt_u),
              ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : MaybeInt_u),
 MaybeInt_wf VV ∧ True) x_10329927 v_x_10329927))):
  bind_spec ds_d3S7 ds_d3S8.
Proof.
  destruct ds_d3S7 as [ds_d3S7 ds_d3S7_p].
  destruct ds_d3S7 as [m|].
  - refine (getPackF ds_d3S8 (# m)).
  - refine Nothing.
Defined.

Inductive bind_rel: MaybeInt_u → @uPack (Z ::UT nilUT) MaybeInt_u → MaybeInt_u → Prop :=
  | bind_Nothing_x: ∀ (ds_d3S8 : @uPack (Z ::UT nilUT) MaybeInt_u),
                    bind_rel Nothing_u ds_d3S8 Nothing_u
  | bind_Just_x: ∀ m (ds_d3S8 : @uPack (Z ::UT nilUT) MaybeInt_u) (ds_d3S8_res : MaybeInt_u),
                 getUPackRel ds_d3S8 m ds_d3S8_res → bind_rel (Just_u m) ds_d3S8 ds_d3S8_res.

#[global] Hint Constructors bind_rel: core_hint_db.

#[global] Instance bind_lookup_rel: dictionary rel bind := { lookup' := bind_rel }.

#[global] Instance bind_getF: getFunc bind_rel := { getF' := bind }.

Theorem bind_rel_funct [ds_d3S7 : MaybeInt_u] [ds_d3S8 : @uPack (Z ::UT nilUT) MaybeInt_u]:
  ∀ (VV VV' : MaybeInt_u), bind_rel ds_d3S7 ds_d3S8 VV → (bind_rel ds_d3S7 ds_d3S8 VV' → VV = VV').
Proof.
  destruct ds_d3S7 as [m|]; rel_functionhood_body.
Qed.

#[global] Hint Resolve bind_rel_funct: f_rel_funct_db.

Theorem bind_Nothing_x_lem ds_d3S8 bind_Nothing_x_lem_res:
  bind_rel Nothing_u ds_d3S8 bind_Nothing_x_lem_res ↔ bind_Nothing_x_lem_res == Nothing_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite bind_Nothing_x_lem: f_rel_back.

Theorem bind_Just_x_lem ds_d3S8 m bind_Just_x_lem_res:
  bind_rel (Just_u m) ds_d3S8 bind_Just_x_lem_res
  ↔ ∃ (ds_d3S8_res : MaybeInt_u),
    getUPackRel ds_d3S8 m ds_d3S8_res ∧ bind_Just_x_lem_res == ds_d3S8_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite bind_Just_x_lem: f_rel_back.

Theorem bind_rel_ex
  (ds_d3S7 : MaybeInt_u)
  (ds_d3S7_p : MaybeInt_wf ds_d3S7 ∧ True)
  (ds_d3S8 : @Pack
             ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
             MaybeInt_u
             (λ (x_82647028 : ArgList ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
                (v_x_82647028 : MaybeInt_u),
              ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : MaybeInt_u),
 MaybeInt_wf VV ∧ True) x_82647028 v_x_82647028))):
  bind_rel ds_d3S7 ⌊ ds_d3S8 ⌋ ⌊ bind (exist _ ds_d3S7 ds_d3S7_p) ds_d3S8 -⌋.
Proof.
  Opaque bind.
  existence_lemma_pre bind;
  destruct ds_d3S7 as [m|];
  [fix_notations | fix_notations];
  simpl in *.
  Transparent bind.
  all: (existence_lemma_quicksolve bind; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve bind_rel_ex: rel_ax_db.

#[global] Opaque bind.

Theorem bind__bind_rel_rw
  (ds_d3S7 : MaybeInt_u)
  (ds_d3S7_p : MaybeInt_wf ds_d3S7 ∧ True)
  (ds_d3S8 : @Pack
             ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
             MaybeInt_u
             (λ (x_82647028 : ArgList ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
                (v_x_82647028 : MaybeInt_u),
              ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : MaybeInt_u),
 MaybeInt_wf VV ∧ True) x_82647028 v_x_82647028)))
  (VV : MaybeInt_u):
  ⌊ bind (exist _ ds_d3S7 ds_d3S7_p) ds_d3S8 -⌋ = VV ↔ bind_rel ds_d3S7 ⌊ ds_d3S8 ⌋ VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite bind__bind_rel_rw: f_rel_funct_db.

#[global] Hint Resolve bind__bind_rel_rw: rel_ax_db.

#[global] Instance bind_lookup_rw: dictionary rwLem bind := { lookup' := bind__bind_rel_rw }.

Theorem bind__bind_rel
  (ds_d3S7 : MaybeInt)
  (ds_d3S8 : @Pack
             ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
             MaybeInt_u
             (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
                (v_x_10329927 : MaybeInt_u),
              ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : MaybeInt_u),
 MaybeInt_wf VV ∧ True) x_10329927 v_x_10329927)))
  (VV : MaybeInt_u):
  ⌊ bind ds_d3S7 ds_d3S8 -⌋ = VV ↔ bind_rel ⌊ ds_d3S7 ⌋ ⌊ ds_d3S8 ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite bind__bind_rel: f_rel_funct_db.

Theorem bind__bind_rel'
  (ds_d3S7_u : MaybeInt_u)
  (ds_d3S8_u : @uPack (Z ::UT nilUT) MaybeInt_u)
  (ds_d3S7 : MaybeInt)
  (ds_d3S8 : @Pack
             ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
             MaybeInt_u
             (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
                (v_x_10329927 : MaybeInt_u),
              ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : MaybeInt_u),
 MaybeInt_wf VV ∧ True) x_10329927 v_x_10329927)))
  (VV : MaybeInt_u):
  ds_d3S7_u = ⌊ ds_d3S7 ⌋
  → (ds_d3S8_u = ⌊ ds_d3S8 ⌋ → ⌊ bind ds_d3S7 ds_d3S8 -⌋ = VV ↔ bind_rel ds_d3S7_u ds_d3S8_u VV).
Proof.
  intros -> ->. refine (bind__bind_rel ds_d3S7 ds_d3S8 VV).
Qed.

#[global] Hint Resolve bind__bind_rel': f_rel_funct_db.

Theorem bind_rel_mk
  (ds_d3S7 : MaybeInt_u)
  (ds_d3S7_p : MaybeInt_wf ds_d3S7 ∧ True)
  (ds_d3S8 : @Pack
             ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
             (Z ::UT nilUT)
             ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
             MaybeInt_u
             (λ (x_82647028 : ArgList ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
                (v_x_82647028 : MaybeInt_u),
              ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : MaybeInt_u),
 MaybeInt_wf VV ∧ True) x_82647028 v_x_82647028))):
  {VV: _ | bind_rel ds_d3S7 (packProj ds_d3S8) VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, bind_rel ds_d3S7 (packProj ds_d3S8) VV)
          (bind (exist _ ds_d3S7 ds_d3S7_p) ds_d3S8)
          _);
  rewrite <- bind__bind_rel';
  quicksolve.
Qed.

#[global] Hint Resolve bind_rel_mk: f_rel_funct_db.

Definition retrn_spec (x : {x: Z | True}): Type :=
  MaybeInt.

#[global] Hint Unfold retrn_spec: lia_unfold.

Definition retrn (x : {x: Z | True}): retrn_spec x.
Proof.
  destruct x as [x x_p]. refine (Just (# x)).
Defined.

Inductive retrn_rel: Z → MaybeInt_u → Prop :=
  | retrn_Constr: ∀ x, retrn_rel x (Just_u x).

#[global] Hint Constructors retrn_rel: core_hint_db.

#[global] Instance retrn_lookup_rel: dictionary rel retrn := { lookup' := retrn_rel }.

#[global] Instance retrn_getF: getFunc retrn_rel := { getF' := retrn }.

Theorem retrn_rel_funct [x : Z]:
  ∀ (VV VV' : MaybeInt_u), retrn_rel x VV → (retrn_rel x VV' → VV = VV').
Proof.
  rel_functionhood_body.
Qed.

#[global] Hint Resolve retrn_rel_funct: f_rel_funct_db.

Theorem retrn_inv_lem x retrn_inv_lem_res:
  retrn_rel x retrn_inv_lem_res ↔ retrn_inv_lem_res == Just_u x.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite retrn_inv_lem: f_rel_back.

Theorem retrn_rel_ex (x : Z) (x_p : True): retrn_rel x ⌊ retrn (exist _ x x_p) -⌋.
Proof.
  Opaque retrn.
  existence_lemma_pre retrn; fix_notations; simpl in *.
  Transparent retrn.
  all: (existence_lemma_quicksolve retrn; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve retrn_rel_ex: rel_ax_db.

#[global] Opaque retrn.

Theorem retrn__retrn_rel_rw (x : Z) (x_p : True) (VV : MaybeInt_u):
  ⌊ retrn (exist _ x x_p) -⌋ = VV ↔ retrn_rel x VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite retrn__retrn_rel_rw: f_rel_funct_db.

#[global] Hint Resolve retrn__retrn_rel_rw: rel_ax_db.

#[global] Instance retrn_lookup_rw: dictionary rwLem retrn := { lookup' := retrn__retrn_rel_rw }.

Theorem retrn__retrn_rel (x : {x: Z | True}) (VV : MaybeInt_u):
  ⌊ retrn x -⌋ = VV ↔ retrn_rel ⌊ x ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite retrn__retrn_rel: f_rel_funct_db.

Theorem retrn__retrn_rel' (x_u : Z) (x : {x: Z | True}) (VV : MaybeInt_u):
  x_u = ⌊ x ⌋ → ⌊ retrn x -⌋ = VV ↔ retrn_rel x_u VV.
Proof.
  intros ->. refine (retrn__retrn_rel x VV).
Qed.

#[global] Hint Resolve retrn__retrn_rel': f_rel_funct_db.

Theorem retrn_rel_mk (x : Z) (x_p : True): {VV: _ | retrn_rel x VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, retrn_rel x VV) (retrn (exist _ x x_p)) _);
  rewrite <- retrn__retrn_rel';
  quicksolve.
Qed.

#[global] Hint Resolve retrn_rel_mk: f_rel_funct_db.

#[global] Instance retrn_pack:
  @Pack
  ({x: Z | True} ::RT λ (x : {x: Z | True}), nilRT)
  (Z ::UT nilUT)
  ltac:(mkProjectsArgListTG (({x: Z | True} ::RT λ (x : {x: Z | True}), nilRT)) ((Z ::UT nilUT)))
  MaybeInt_u
  (λ (x_11473763 : ArgList ({x: Z | True} ::RT λ (x : {x: Z | True}), nilRT))
     (v_x_11473763 : MaybeInt_u),
   ltac:(flattenP (λ (x : {x: Z | True}) (VV : MaybeInt_u), MaybeInt_wf VV ∧ True) x_11473763 v_x_11473763)).
Proof.
  buildPackG retrn retrn_rel retrn__retrn_rel retrn_rel_funct.
Defined.

#[global] Instance retrn_upack: @uPack (Z ::UT nilUT) MaybeInt_u.
Proof.
  buildUPackG retrn_rel retrn_rel_funct.
Defined.

Definition left_identity_spec
  (x : {x: Z | True})
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       MaybeInt_u
       (λ (x_44453395 : ArgList ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT))
          (v_x_44453395 : MaybeInt_u),
        ltac:(flattenP (λ (lq_tmp0 : {VV: Z | True}) (VV : MaybeInt_u),
 MaybeInt_wf VV ∧ True) x_44453395 v_x_44453395))):
  Type :=
  {{∃ (retrn_res : MaybeInt_u),
    retrn_rel ⌊ x ⌋ retrn_res
    ∧ ∃ (bind_res : MaybeInt_u),
      bind_rel retrn_res ⌊ f ⌋ bind_res
      ∧ ∃ (f_res : MaybeInt_u), getPackRel f ⌊ x ⌋ f_res ∧ bind_res == f_res}}.

#[global] Hint Unfold left_identity_spec: lia_unfold.

Theorem left_identity
  (x : {x: Z | True})
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       MaybeInt_u
       (λ (x_44453395 : ArgList ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT))
          (v_x_44453395 : MaybeInt_u),
        ltac:(flattenP (λ (lq_tmp0 : {VV: Z | True}) (VV : MaybeInt_u),
 MaybeInt_wf VV ∧ True) x_44453395 v_x_44453395))):
  left_identity_spec x f.
Proof.
  destruct x as [x x_p].
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (retrn_res : MaybeInt_u),
           retrn_rel x retrn_res
           ∧ ∃ (bind_res : MaybeInt_u),
             bind_rel retrn_res ⌊ f ⌋ bind_res
             ∧ ∃ (f_res : MaybeInt_u), getPackRel f x f_res ∧ bind_res == f_res)
          (# unit)
          ltac:(solver)).
Qed.

Definition right_identity_spec (ds_d3S6 : MaybeInt): Type :=
  {{∃ (bind_res : MaybeInt_u), bind_rel ⌊ ds_d3S6 ⌋ retrn_upack bind_res ∧ bind_res == ⌊ ds_d3S6 ⌋}}.

#[global] Hint Unfold right_identity_spec: lia_unfold.

Theorem right_identity (ds_d3S6 : MaybeInt): right_identity_spec ds_d3S6.
Proof.
  destruct ds_d3S6 as [ds_d3S6 ds_d3S6_p].
  destruct ds_d3S6 as [x|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (bind_res : MaybeInt_u), bind_rel ds_d3S6 retrn_upack bind_res ∧ bind_res == ds_d3S6)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (bind_res : MaybeInt_u), bind_rel ds_d3S6 retrn_upack bind_res ∧ bind_res == ds_d3S6)
            (# unit)
            ltac:(solver)).
Qed.
