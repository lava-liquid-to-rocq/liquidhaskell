From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Set Universe Polymorphism. 
From Coq Require Import Unicode.Utf8.

Definition id_spec (x : {x: Z | True}): Type :=
  {VV: Z | True}.

#[global] Hint Unfold id_spec: lia_unfold.

Definition id (x : {x: Z | True}): id_spec x.
Proof.
  destruct x as [x x_p]. refine (# x).
Defined.

Inductive id_rel: Z → Z → Prop :=
  | id_Constr: ∀ x, id_rel x x.

#[global] Hint Constructors id_rel: core_hint_db.

#[global] Instance id_lookup_rel: dictionary rel id := { lookup' := id_rel }.

#[global] Instance id_getF: getFunc id_rel := { getF' := id }.

Theorem id_rel_funct [x : Z]: ∀ (VV VV' : Z), id_rel x VV → (id_rel x VV' → VV = VV').
Proof.
  rel_functionhood_body.
Qed.

#[global] Hint Resolve id_rel_funct: f_rel_funct_db.

Theorem id_inv_lem x id_inv_lem_res: id_rel x id_inv_lem_res ↔ id_inv_lem_res == x.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite id_inv_lem: f_rel_back.

Theorem id_rel_ex (x : Z) (x_p : True): id_rel x ⌊ id (exist _ x x_p) -⌋.
Proof.
  Opaque id.
  existence_lemma_pre id; fix_notations; simpl in *.
  Transparent id.
  all: (existence_lemma_quicksolve id; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve id_rel_ex: rel_ax_db.

#[global] Opaque id.

Theorem id__id_rel_rw (x : Z) (x_p : True) (VV : Z): ⌊ id (exist _ x x_p) -⌋ = VV ↔ id_rel x VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite id__id_rel_rw: f_rel_funct_db.

#[global] Hint Resolve id__id_rel_rw: rel_ax_db.

#[global] Instance id_lookup_rw: dictionary rwLem id := { lookup' := id__id_rel_rw }.

Theorem id__id_rel (x : {x: Z | True}) (VV : Z): ⌊ id x -⌋ = VV ↔ id_rel ⌊ x ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite id__id_rel: f_rel_funct_db.

Theorem id__id_rel' (x_u : Z) (x : {x: Z | True}) (VV : Z):
  x_u = ⌊ x ⌋ → ⌊ id x -⌋ = VV ↔ id_rel x_u VV.
Proof.
  intros ->. refine (id__id_rel x VV).
Qed.

#[global] Hint Resolve id__id_rel': f_rel_funct_db.

Theorem id_rel_mk (x : Z) (x_p : True): {VV: _ | id_rel x VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, id_rel x VV) (id (exist _ x x_p)) _);
  rewrite <- id__id_rel';
  quicksolve.
Qed.

#[global] Hint Resolve id_rel_mk: f_rel_funct_db.

#[global] Instance id_pack:
  @Pack
  ({x: Z | True} ::RT λ (x : {x: Z | True}), nilRT)
  (Z ::UT nilUT)
  ltac:(mkProjectsArgListTG (({x: Z | True} ::RT λ (x : {x: Z | True}), nilRT)) ((Z ::UT nilUT)))
  Z
  (λ (x_11473763 : ArgList ({x: Z | True} ::RT λ (x : {x: Z | True}), nilRT)) (v_x_11473763 : Z),
   ltac:(flattenP (λ (x : {x: Z | True}) (VV : Z), True) x_11473763 v_x_11473763)).
Proof.
  buildPackG id id_rel id__id_rel id_rel_funct.
Defined.

#[global] Instance id_upack: @uPack (Z ::UT nilUT) Z.
Proof.
  buildUPackG id_rel id_rel_funct.
Defined.

Definition compose_spec
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513)))
  (g : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp4 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp4 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_53075754 : ArgList ({VV: Z | True} ::RT λ (lq_tmp4 : {VV: Z | True}), nilRT))
          (v_x_53075754 : Z),
        ltac:(flattenP (λ (lq_tmp4 : {VV: Z | True}) (VV : Z), True) x_53075754 v_x_53075754)))
  (x : {x: Z | True}):
  Type :=
  {VV: Z | True}.

#[global] Hint Unfold compose_spec: lia_unfold.

Definition compose
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513)))
  (g : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp4 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp4 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_53075754 : ArgList ({VV: Z | True} ::RT λ (lq_tmp4 : {VV: Z | True}), nilRT))
          (v_x_53075754 : Z),
        ltac:(flattenP (λ (lq_tmp4 : {VV: Z | True}) (VV : Z), True) x_53075754 v_x_53075754)))
  (x : {x: Z | True}):
  compose_spec f g x.
Proof.
  destruct x as [x x_p]. refine (getPackF f (getPackF g (# x))).
Defined.

Inductive compose_rel: @uPack (Z ::UT nilUT) Z → @uPack (Z ::UT nilUT) Z → Z → Z → Prop :=
  | compose_Constr: ∀ (f g : @uPack (Z ::UT nilUT) Z) x (g_res : Z),
                    getUPackRel g x g_res → ∀ (f_res : Z), getUPackRel f g_res f_res → compose_rel f g x f_res.

#[global] Hint Constructors compose_rel: core_hint_db.

#[global] Instance compose_lookup_rel: dictionary rel compose := { lookup' := compose_rel }.

#[global] Instance compose_getF: getFunc compose_rel := { getF' := compose }.

Theorem compose_rel_funct [f g : @uPack (Z ::UT nilUT) Z] [x : Z]:
  ∀ (VV VV' : Z), compose_rel f g x VV → (compose_rel f g x VV' → VV = VV').
Proof.
  rel_functionhood_body.
Qed.

#[global] Hint Resolve compose_rel_funct: f_rel_funct_db.

Theorem compose_inv_lem f g x compose_inv_lem_res:
  compose_rel f g x compose_inv_lem_res
  ↔ ∃ (g_res : Z),
    getUPackRel g x g_res ∧ ∃ (f_res : Z), getUPackRel f g_res f_res ∧ compose_inv_lem_res == f_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite compose_inv_lem: f_rel_back.

Theorem compose_rel_ex
  (f : @Pack
       ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp1: Z | True}
  ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_86795196 : ArgList ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_86795196 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z), True) x_86795196 v_x_86795196)))
  (g : @Pack
       ({lq_tmp4: Z | True} ::RT λ (lq_tmp4 : {lq_tmp4: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp4: Z | True}
  ::RT λ (lq_tmp4 : {lq_tmp4: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_39852563 : ArgList ({lq_tmp4: Z | True} ::RT λ (lq_tmp4 : {lq_tmp4: Z | True}), nilRT))
          (v_x_39852563 : Z),
        ltac:(flattenP (λ (lq_tmp4 : {lq_tmp4: Z | True}) (VV : Z), True) x_39852563 v_x_39852563)))
  (x : Z)
  (x_p : True):
  compose_rel ⌊ f ⌋ ⌊ g ⌋ x ⌊ compose f g (exist _ x x_p) -⌋.
Proof.
  Opaque compose.
  existence_lemma_pre compose; fix_notations; simpl in *.
  Transparent compose.
  all: (existence_lemma_quicksolve compose; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve compose_rel_ex: rel_ax_db.

#[global] Opaque compose.

Theorem compose__compose_rel_rw
  (f : @Pack
       ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp1: Z | True}
  ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_86795196 : ArgList ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_86795196 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z), True) x_86795196 v_x_86795196)))
  (g : @Pack
       ({lq_tmp4: Z | True} ::RT λ (lq_tmp4 : {lq_tmp4: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp4: Z | True}
  ::RT λ (lq_tmp4 : {lq_tmp4: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_39852563 : ArgList ({lq_tmp4: Z | True} ::RT λ (lq_tmp4 : {lq_tmp4: Z | True}), nilRT))
          (v_x_39852563 : Z),
        ltac:(flattenP (λ (lq_tmp4 : {lq_tmp4: Z | True}) (VV : Z), True) x_39852563 v_x_39852563)))
  (x : Z)
  (x_p : True)
  (VV : Z):
  ⌊ compose f g (exist _ x x_p) -⌋ = VV ↔ compose_rel ⌊ f ⌋ ⌊ g ⌋ x VV.
Proof.
  f__f_rel_rw.
  set ⌊ f ⌋ as fu in *; set ⌊ g ⌋ as gu in *.
  clearbody fu gu z. clear f g x_p.
  (* 1 goal
  x, VV, z : Z
  fu, gu : uPack (Z ::UT nilUT) Z
  H : compose_rel fu gu x z
  H0 : compose_rel fu gu x VV
  ______________________________________(1/1)
  z = VV
  *)
  assert_succeeds (apply (compose_rel_funct _ _ H H0)).
  assert_succeeds (exact (compose_rel_funct z VV H H0)).
  refine (_ z VV H H0).
  assert_fails (exact compose_rel_funct).
  Undo. Undo. exact (compose_rel_funct z VV H H0).
Qed.

#[global] Hint Rewrite compose__compose_rel_rw: f_rel_funct_db.

#[global] Hint Resolve compose__compose_rel_rw: rel_ax_db.

#[global] Instance compose_lookup_rw: dictionary rwLem compose := {
    lookup' := compose__compose_rel_rw }.

Theorem compose__compose_rel
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513)))
  (g : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp4 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp4 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_53075754 : ArgList ({VV: Z | True} ::RT λ (lq_tmp4 : {VV: Z | True}), nilRT))
          (v_x_53075754 : Z),
        ltac:(flattenP (λ (lq_tmp4 : {VV: Z | True}) (VV : Z), True) x_53075754 v_x_53075754)))
  (x : {x: Z | True})
  (VV : Z):
  ⌊ compose f g x -⌋ = VV ↔ compose_rel ⌊ f ⌋ ⌊ g ⌋ ⌊ x ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite compose__compose_rel: f_rel_funct_db.

Theorem compose__compose_rel'
  (f_u g_u : @uPack (Z ::UT nilUT) Z)
  (x_u : Z)
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513)))
  (g : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp4 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp4 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_53075754 : ArgList ({VV: Z | True} ::RT λ (lq_tmp4 : {VV: Z | True}), nilRT))
          (v_x_53075754 : Z),
        ltac:(flattenP (λ (lq_tmp4 : {VV: Z | True}) (VV : Z), True) x_53075754 v_x_53075754)))
  (x : {x: Z | True})
  (VV : Z):
  f_u = ⌊ f ⌋ → (g_u = ⌊ g ⌋ → (x_u = ⌊ x ⌋ → ⌊ compose f g x -⌋ = VV ↔ compose_rel f_u g_u x_u VV)).
Proof.
  intros -> -> ->. refine (compose__compose_rel f g x VV).
Qed.

#[global] Hint Resolve compose__compose_rel': f_rel_funct_db.

Theorem compose_rel_mk
  (f : @Pack
       ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp1: Z | True}
  ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_86795196 : ArgList ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_86795196 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z), True) x_86795196 v_x_86795196)))
  (g : @Pack
       ({lq_tmp4: Z | True} ::RT λ (lq_tmp4 : {lq_tmp4: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp4: Z | True}
  ::RT λ (lq_tmp4 : {lq_tmp4: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_39852563 : ArgList ({lq_tmp4: Z | True} ::RT λ (lq_tmp4 : {lq_tmp4: Z | True}), nilRT))
          (v_x_39852563 : Z),
        ltac:(flattenP (λ (lq_tmp4 : {lq_tmp4: Z | True}) (VV : Z), True) x_39852563 v_x_39852563)))
  (x : Z)
  (x_p : True):
  {VV: _ | compose_rel (packProj f) (packProj g) x VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, compose_rel (packProj f) (packProj g) x VV)
          (compose f g (exist _ x x_p))
          _);
  rewrite <- compose__compose_rel';
  quicksolve.
Qed.

#[global] Hint Resolve compose_rel_mk: f_rel_funct_db.

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

Definition composeI_spec
  (f : @Pack
       (Identity ::RT λ (lq_tmp1 : Identity), nilRT)
       (Identity_u ::UT nilUT)
       ltac:(mkProjectsArgListTG ((Identity ::RT λ (lq_tmp1 : Identity), nilRT)) ((Identity_u ::UT nilUT)))
       Identity_u
       (λ (x_30084888 : ArgList (Identity ::RT λ (lq_tmp1 : Identity), nilRT)) (v_x_30084888 : Identity_u),
        ltac:(flattenP (λ (lq_tmp1 : Identity) (VV : Identity_u), Identity_wf VV ∧ True) x_30084888 v_x_30084888)))
  (g : @Pack
       (Identity ::RT λ (lq_tmp4 : Identity), nilRT)
       (Identity_u ::UT nilUT)
       ltac:(mkProjectsArgListTG ((Identity ::RT λ (lq_tmp4 : Identity), nilRT)) ((Identity_u ::UT nilUT)))
       Identity_u
       (λ (x_17975261 : ArgList (Identity ::RT λ (lq_tmp4 : Identity), nilRT)) (v_x_17975261 : Identity_u),
        ltac:(flattenP (λ (lq_tmp4 : Identity) (VV : Identity_u), Identity_wf VV ∧ True) x_17975261 v_x_17975261)))
  (x : Identity):
  Type :=
  Identity.

#[global] Hint Unfold composeI_spec: lia_unfold.

Definition composeI
  (f : @Pack
       (Identity ::RT λ (lq_tmp1 : Identity), nilRT)
       (Identity_u ::UT nilUT)
       ltac:(mkProjectsArgListTG ((Identity ::RT λ (lq_tmp1 : Identity), nilRT)) ((Identity_u ::UT nilUT)))
       Identity_u
       (λ (x_30084888 : ArgList (Identity ::RT λ (lq_tmp1 : Identity), nilRT)) (v_x_30084888 : Identity_u),
        ltac:(flattenP (λ (lq_tmp1 : Identity) (VV : Identity_u), Identity_wf VV ∧ True) x_30084888 v_x_30084888)))
  (g : @Pack
       (Identity ::RT λ (lq_tmp4 : Identity), nilRT)
       (Identity_u ::UT nilUT)
       ltac:(mkProjectsArgListTG ((Identity ::RT λ (lq_tmp4 : Identity), nilRT)) ((Identity_u ::UT nilUT)))
       Identity_u
       (λ (x_17975261 : ArgList (Identity ::RT λ (lq_tmp4 : Identity), nilRT)) (v_x_17975261 : Identity_u),
        ltac:(flattenP (λ (lq_tmp4 : Identity) (VV : Identity_u), Identity_wf VV ∧ True) x_17975261 v_x_17975261)))
  (x : Identity):
  composeI_spec f g x.
Proof.
  destruct x as [x x_p].
  refine (getPackF f (getPackF g (exist (λ (x : Identity_u), Identity_wf x ∧ True) x ltac:(solver)))).
Defined.

Inductive composeI_rel:
  @uPack (Identity_u ::UT nilUT) Identity_u
  → @uPack (Identity_u ::UT nilUT) Identity_u → Identity_u → Identity_u → Prop :=
  | composeI_Constr: ∀ (f g : @uPack (Identity_u ::UT nilUT) Identity_u) x (g_res : Identity_u),
                     getUPackRel g x g_res
                     → ∀ (f_res : Identity_u), getUPackRel f g_res f_res → composeI_rel f g x f_res.

#[global] Hint Constructors composeI_rel: core_hint_db.

#[global] Instance composeI_lookup_rel: dictionary rel composeI := { lookup' := composeI_rel }.

#[global] Instance composeI_getF: getFunc composeI_rel := { getF' := composeI }.

Theorem composeI_rel_funct [f g : @uPack (Identity_u ::UT nilUT) Identity_u] [x : Identity_u]:
  ∀ (VV VV' : Identity_u), composeI_rel f g x VV → (composeI_rel f g x VV' → VV = VV').
Proof.
  rel_functionhood_body.
Qed.

#[global] Hint Resolve composeI_rel_funct: f_rel_funct_db.

Theorem composeI_inv_lem f g x composeI_inv_lem_res:
  composeI_rel f g x composeI_inv_lem_res
  ↔ ∃ (g_res : Identity_u),
    getUPackRel g x g_res
    ∧ ∃ (f_res : Identity_u), getUPackRel f g_res f_res ∧ composeI_inv_lem_res == f_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite composeI_inv_lem: f_rel_back.

Theorem composeI_rel_ex
  (f : @Pack
       (Identity ::RT λ (lq_tmp1 : Identity), nilRT)
       (Identity_u ::UT nilUT)
       ltac:(mkProjectsArgListTG ((Identity ::RT λ (lq_tmp1 : Identity), nilRT)) ((Identity_u ::UT nilUT)))
       Identity_u
       (λ (x_30084888 : ArgList (Identity ::RT λ (lq_tmp1 : Identity), nilRT)) (v_x_30084888 : Identity_u),
        ltac:(flattenP (λ (lq_tmp1 : Identity) (VV : Identity_u), Identity_wf VV ∧ True) x_30084888 v_x_30084888)))
  (g : @Pack
       (Identity ::RT λ (lq_tmp4 : Identity), nilRT)
       (Identity_u ::UT nilUT)
       ltac:(mkProjectsArgListTG ((Identity ::RT λ (lq_tmp4 : Identity), nilRT)) ((Identity_u ::UT nilUT)))
       Identity_u
       (λ (x_17975261 : ArgList (Identity ::RT λ (lq_tmp4 : Identity), nilRT)) (v_x_17975261 : Identity_u),
        ltac:(flattenP (λ (lq_tmp4 : Identity) (VV : Identity_u), Identity_wf VV ∧ True) x_17975261 v_x_17975261)))
  (x : Identity_u)
  (x_p : Identity_wf x ∧ True):
  composeI_rel ⌊ f ⌋ ⌊ g ⌋ x ⌊ composeI f g (exist _ x x_p) -⌋.
Proof.
  Opaque composeI.
  existence_lemma_pre composeI; fix_notations; simpl in *.
  Transparent composeI.
  all: (existence_lemma_quicksolve composeI; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve composeI_rel_ex: rel_ax_db.

#[global] Opaque composeI.

Theorem composeI__composeI_rel_rw
  (f : @Pack
       (Identity ::RT λ (lq_tmp1 : Identity), nilRT)
       (Identity_u ::UT nilUT)
       ltac:(mkProjectsArgListTG ((Identity ::RT λ (lq_tmp1 : Identity), nilRT)) ((Identity_u ::UT nilUT)))
       Identity_u
       (λ (x_30084888 : ArgList (Identity ::RT λ (lq_tmp1 : Identity), nilRT)) (v_x_30084888 : Identity_u),
        ltac:(flattenP (λ (lq_tmp1 : Identity) (VV : Identity_u), Identity_wf VV ∧ True) x_30084888 v_x_30084888)))
  (g : @Pack
       (Identity ::RT λ (lq_tmp4 : Identity), nilRT)
       (Identity_u ::UT nilUT)
       ltac:(mkProjectsArgListTG ((Identity ::RT λ (lq_tmp4 : Identity), nilRT)) ((Identity_u ::UT nilUT)))
       Identity_u
       (λ (x_17975261 : ArgList (Identity ::RT λ (lq_tmp4 : Identity), nilRT)) (v_x_17975261 : Identity_u),
        ltac:(flattenP (λ (lq_tmp4 : Identity) (VV : Identity_u), Identity_wf VV ∧ True) x_17975261 v_x_17975261)))
  (x : Identity_u)
  (x_p : Identity_wf x ∧ True)
  (VV : Identity_u):
  ⌊ composeI f g (exist _ x x_p) -⌋ = VV ↔ composeI_rel ⌊ f ⌋ ⌊ g ⌋ x VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite composeI__composeI_rel_rw: f_rel_funct_db.

#[global] Hint Resolve composeI__composeI_rel_rw: rel_ax_db.

#[global] Instance composeI_lookup_rw: dictionary rwLem composeI := {
    lookup' := composeI__composeI_rel_rw }.

Theorem composeI__composeI_rel
  (f : @Pack
       (Identity ::RT λ (lq_tmp1 : Identity), nilRT)
       (Identity_u ::UT nilUT)
       ltac:(mkProjectsArgListTG ((Identity ::RT λ (lq_tmp1 : Identity), nilRT)) ((Identity_u ::UT nilUT)))
       Identity_u
       (λ (x_30084888 : ArgList (Identity ::RT λ (lq_tmp1 : Identity), nilRT)) (v_x_30084888 : Identity_u),
        ltac:(flattenP (λ (lq_tmp1 : Identity) (VV : Identity_u), Identity_wf VV ∧ True) x_30084888 v_x_30084888)))
  (g : @Pack
       (Identity ::RT λ (lq_tmp4 : Identity), nilRT)
       (Identity_u ::UT nilUT)
       ltac:(mkProjectsArgListTG ((Identity ::RT λ (lq_tmp4 : Identity), nilRT)) ((Identity_u ::UT nilUT)))
       Identity_u
       (λ (x_17975261 : ArgList (Identity ::RT λ (lq_tmp4 : Identity), nilRT)) (v_x_17975261 : Identity_u),
        ltac:(flattenP (λ (lq_tmp4 : Identity) (VV : Identity_u), Identity_wf VV ∧ True) x_17975261 v_x_17975261)))
  (x : Identity)
  (VV : Identity_u):
  ⌊ composeI f g x -⌋ = VV ↔ composeI_rel ⌊ f ⌋ ⌊ g ⌋ ⌊ x ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite composeI__composeI_rel: f_rel_funct_db.

Theorem composeI__composeI_rel'
  (f_u g_u : @uPack (Identity_u ::UT nilUT) Identity_u)
  (x_u : Identity_u)
  (f : @Pack
       (Identity ::RT λ (lq_tmp1 : Identity), nilRT)
       (Identity_u ::UT nilUT)
       ltac:(mkProjectsArgListTG ((Identity ::RT λ (lq_tmp1 : Identity), nilRT)) ((Identity_u ::UT nilUT)))
       Identity_u
       (λ (x_30084888 : ArgList (Identity ::RT λ (lq_tmp1 : Identity), nilRT)) (v_x_30084888 : Identity_u),
        ltac:(flattenP (λ (lq_tmp1 : Identity) (VV : Identity_u), Identity_wf VV ∧ True) x_30084888 v_x_30084888)))
  (g : @Pack
       (Identity ::RT λ (lq_tmp4 : Identity), nilRT)
       (Identity_u ::UT nilUT)
       ltac:(mkProjectsArgListTG ((Identity ::RT λ (lq_tmp4 : Identity), nilRT)) ((Identity_u ::UT nilUT)))
       Identity_u
       (λ (x_17975261 : ArgList (Identity ::RT λ (lq_tmp4 : Identity), nilRT)) (v_x_17975261 : Identity_u),
        ltac:(flattenP (λ (lq_tmp4 : Identity) (VV : Identity_u), Identity_wf VV ∧ True) x_17975261 v_x_17975261)))
  (x : Identity)
  (VV : Identity_u):
  f_u = ⌊ f ⌋
  → (g_u = ⌊ g ⌋ → (x_u = ⌊ x ⌋ → ⌊ composeI f g x -⌋ = VV ↔ composeI_rel f_u g_u x_u VV)).
Proof.
  intros -> -> ->. refine (composeI__composeI_rel f g x VV).
Qed.

#[global] Hint Resolve composeI__composeI_rel': f_rel_funct_db.

Theorem composeI_rel_mk
  (f : @Pack
       (Identity ::RT λ (lq_tmp1 : Identity), nilRT)
       (Identity_u ::UT nilUT)
       ltac:(mkProjectsArgListTG ((Identity ::RT λ (lq_tmp1 : Identity), nilRT)) ((Identity_u ::UT nilUT)))
       Identity_u
       (λ (x_30084888 : ArgList (Identity ::RT λ (lq_tmp1 : Identity), nilRT)) (v_x_30084888 : Identity_u),
        ltac:(flattenP (λ (lq_tmp1 : Identity) (VV : Identity_u), Identity_wf VV ∧ True) x_30084888 v_x_30084888)))
  (g : @Pack
       (Identity ::RT λ (lq_tmp4 : Identity), nilRT)
       (Identity_u ::UT nilUT)
       ltac:(mkProjectsArgListTG ((Identity ::RT λ (lq_tmp4 : Identity), nilRT)) ((Identity_u ::UT nilUT)))
       Identity_u
       (λ (x_17975261 : ArgList (Identity ::RT λ (lq_tmp4 : Identity), nilRT)) (v_x_17975261 : Identity_u),
        ltac:(flattenP (λ (lq_tmp4 : Identity) (VV : Identity_u), Identity_wf VV ∧ True) x_17975261 v_x_17975261)))
  (x : Identity_u)
  (x_p : Identity_wf x ∧ True):
  {VV: _ | composeI_rel (packProj f) (packProj g) x VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, composeI_rel (packProj f) (packProj g) x VV)
          (composeI f g (exist _ x x_p))
          _);
  rewrite <- composeI__composeI_rel';
  quicksolve.
Qed.

#[global] Hint Resolve composeI_rel_mk: f_rel_funct_db.

Definition fmap_spec
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513)))
  (ds_dbPV : Identity):
  Type :=
  Identity.

#[global] Hint Unfold fmap_spec: lia_unfold.

Definition fmap
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513)))
  (ds_dbPV : Identity):
  fmap_spec f ds_dbPV.
Proof.
  destruct ds_dbPV as [ds_dbPV ds_dbPV_p].
  destruct ds_dbPV as [x].
  - refine (Val (getPackF f (# x))).
Defined.

Inductive fmap_rel: @uPack (Z ::UT nilUT) Z → Identity_u → Identity_u → Prop :=
  | fmap_x_Val: ∀ (f : @uPack (Z ::UT nilUT) Z) x (f_res : Z),
                getUPackRel f x f_res → fmap_rel f (Val_u x) (Val_u f_res).

#[global] Hint Constructors fmap_rel: core_hint_db.

#[global] Instance fmap_lookup_rel: dictionary rel fmap := { lookup' := fmap_rel }.

#[global] Instance fmap_getF: getFunc fmap_rel := { getF' := fmap }.

Theorem fmap_rel_funct [f : @uPack (Z ::UT nilUT) Z] [ds_dbPV : Identity_u]:
  ∀ (VV VV' : Identity_u), fmap_rel f ds_dbPV VV → (fmap_rel f ds_dbPV VV' → VV = VV').
Proof.
  destruct ds_dbPV as [x]; rel_functionhood_body.
Qed.

#[global] Hint Resolve fmap_rel_funct: f_rel_funct_db.

Theorem fmap_x_Val_lem f x fmap_x_Val_lem_res:
  fmap_rel f (Val_u x) fmap_x_Val_lem_res
  ↔ ∃ (f_res : Z), getUPackRel f x f_res ∧ fmap_x_Val_lem_res == Val_u f_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite fmap_x_Val_lem: f_rel_back.

Theorem fmap_rel_ex
  (f : @Pack
       ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp1: Z | True}
  ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_86795196 : ArgList ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_86795196 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z), True) x_86795196 v_x_86795196)))
  (ds_dbPV : Identity_u)
  (ds_dbPV_p : Identity_wf ds_dbPV ∧ True):
  fmap_rel ⌊ f ⌋ ds_dbPV ⌊ fmap f (exist _ ds_dbPV ds_dbPV_p) -⌋.
Proof.
  Opaque fmap.
  existence_lemma_pre fmap;
  destruct ds_dbPV as [x];
  [fix_notations];
  simpl in *.
  Transparent fmap.
  all: (existence_lemma_quicksolve fmap; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve fmap_rel_ex: rel_ax_db.

#[global] Opaque fmap.

Theorem fmap__fmap_rel_rw
  (f : @Pack
       ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp1: Z | True}
  ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_86795196 : ArgList ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_86795196 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z), True) x_86795196 v_x_86795196)))
  (ds_dbPV : Identity_u)
  (ds_dbPV_p : Identity_wf ds_dbPV ∧ True)
  (VV : Identity_u):
  ⌊ fmap f (exist _ ds_dbPV ds_dbPV_p) -⌋ = VV ↔ fmap_rel ⌊ f ⌋ ds_dbPV VV.
Proof.
  f__f_rel_rw.
  set ⌊ f ⌋ as fu in *.
  now unify_vars.
Qed.

#[global] Hint Rewrite fmap__fmap_rel_rw: f_rel_funct_db.

#[global] Hint Resolve fmap__fmap_rel_rw: rel_ax_db.

#[global] Instance fmap_lookup_rw: dictionary rwLem fmap := { lookup' := fmap__fmap_rel_rw }.

Theorem fmap__fmap_rel
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513)))
  (ds_dbPV : Identity)
  (VV : Identity_u):
  ⌊ fmap f ds_dbPV -⌋ = VV ↔ fmap_rel ⌊ f ⌋ ⌊ ds_dbPV ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite fmap__fmap_rel: f_rel_funct_db.

Theorem fmap__fmap_rel'
  (f_u : @uPack (Z ::UT nilUT) Z)
  (ds_dbPV_u : Identity_u)
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_40877513 : ArgList ({VV: Z | True} ::RT λ (lq_tmp1 : {VV: Z | True}), nilRT))
          (v_x_40877513 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {VV: Z | True}) (VV : Z), True) x_40877513 v_x_40877513)))
  (ds_dbPV : Identity)
  (VV : Identity_u):
  f_u = ⌊ f ⌋ → (ds_dbPV_u = ⌊ ds_dbPV ⌋ → ⌊ fmap f ds_dbPV -⌋ = VV ↔ fmap_rel f_u ds_dbPV_u VV).
Proof.
  intros -> ->. refine (fmap__fmap_rel f ds_dbPV VV).
Qed.

#[global] Hint Resolve fmap__fmap_rel': f_rel_funct_db.

Theorem fmap_rel_mk
  (f : @Pack
       ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp1: Z | True}
  ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_86795196 : ArgList ({lq_tmp1: Z | True} ::RT λ (lq_tmp1 : {lq_tmp1: Z | True}), nilRT))
          (v_x_86795196 : Z),
        ltac:(flattenP (λ (lq_tmp1 : {lq_tmp1: Z | True}) (VV : Z), True) x_86795196 v_x_86795196)))
  (ds_dbPV : Identity_u)
  (ds_dbPV_p : Identity_wf ds_dbPV ∧ True):
  {VV: _ | fmap_rel (packProj f) ds_dbPV VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, fmap_rel (packProj f) ds_dbPV VV)
          (fmap f (exist _ ds_dbPV ds_dbPV_p))
          _);
  rewrite <- fmap__fmap_rel';
  quicksolve.
Qed.

#[global] Hint Resolve fmap_rel_mk: f_rel_funct_db.

Definition distrib_left_hand_spec
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_44453395 : ArgList ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT))
          (v_x_44453395 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {VV: Z | True}) (VV : Z), True) x_44453395 v_x_44453395)))
  (g : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
          (v_x_10329927 : Z),
        ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927)))
  (xs : Identity):
  Type :=
  Identity.

#[global] Hint Unfold distrib_left_hand_spec: lia_unfold.

Definition distrib_left_hand
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_44453395 : ArgList ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT))
          (v_x_44453395 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {VV: Z | True}) (VV : Z), True) x_44453395 v_x_44453395)))
  (g : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
          (v_x_10329927 : Z),
        ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927)))
  (xs : Identity):
  distrib_left_hand_spec f g xs.
Proof.
  destruct xs as [xs xs_p].
  refine (fmap (compose f g) (exist (λ (xs : Identity_u), Identity_wf xs ∧ True) xs ltac:(solver))).
Defined.

Inductive distrib_left_hand_rel:
  @uPack (Z ::UT nilUT) Z → @uPack (Z ::UT nilUT) Z → Identity_u → Identity_u → Prop :=
  | distrib_left_hand_Constr: ∀ (f g : @uPack (Z ::UT nilUT) Z) xs (compose_res : Z),
                              compose_rel f g compose_res
                              → ∀ (fmap_res : Identity_u),
                                fmap_rel compose_res xs fmap_res → distrib_left_hand_rel f g xs fmap_res.

#[global] Hint Constructors distrib_left_hand_rel: core_hint_db.

#[global] Instance distrib_left_hand_lookup_rel: dictionary rel distrib_left_hand := {
    lookup' := distrib_left_hand_rel }.

#[global] Instance distrib_left_hand_getF: getFunc distrib_left_hand_rel := {
    getF' := distrib_left_hand }.

Theorem distrib_left_hand_rel_funct [f g : @uPack (Z ::UT nilUT) Z] [xs : Identity_u]:
  ∀ (VV VV' : Identity_u),
  distrib_left_hand_rel f g xs VV → (distrib_left_hand_rel f g xs VV' → VV = VV').
Proof.
  rel_functionhood_body.
Qed.

#[global] Hint Resolve distrib_left_hand_rel_funct: f_rel_funct_db.

Theorem distrib_left_hand_inv_lem f g xs distrib_left_hand_inv_lem_res:
  distrib_left_hand_rel f g xs distrib_left_hand_inv_lem_res
  ↔ ∃ (compose_res : Z),
    compose_rel f g compose_res
    ∧ ∃ (fmap_res : Identity_u),
      fmap_rel compose_res xs fmap_res ∧ distrib_left_hand_inv_lem_res == fmap_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite distrib_left_hand_inv_lem: f_rel_back.

Theorem distrib_left_hand_rel_ex
  (f : @Pack
       ({lq_tmp0: Z | True} ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp0: Z | True}
  ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_49697850 : ArgList ({lq_tmp0: Z | True} ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT))
          (v_x_49697850 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {lq_tmp0: Z | True}) (VV : Z), True) x_49697850 v_x_49697850)))
  (g : @Pack
       ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_82647028 : ArgList ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
          (v_x_82647028 : Z),
        ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : Z), True) x_82647028 v_x_82647028)))
  (xs : Identity_u)
  (xs_p : Identity_wf xs ∧ True):
  distrib_left_hand_rel ⌊ f ⌋ ⌊ g ⌋ xs ⌊ distrib_left_hand f g (exist _ xs xs_p) -⌋.
Proof.
  Opaque distrib_left_hand.
  existence_lemma_pre distrib_left_hand; fix_notations; simpl in *.
  Transparent distrib_left_hand.
  all: (existence_lemma_quicksolve distrib_left_hand; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve distrib_left_hand_rel_ex: rel_ax_db.

#[global] Opaque distrib_left_hand.

Theorem distrib_left_hand__distrib_left_hand_rel_rw
  (f : @Pack
       ({lq_tmp0: Z | True} ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp0: Z | True}
  ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_49697850 : ArgList ({lq_tmp0: Z | True} ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT))
          (v_x_49697850 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {lq_tmp0: Z | True}) (VV : Z), True) x_49697850 v_x_49697850)))
  (g : @Pack
       ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_82647028 : ArgList ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
          (v_x_82647028 : Z),
        ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : Z), True) x_82647028 v_x_82647028)))
  (xs : Identity_u)
  (xs_p : Identity_wf xs ∧ True)
  (VV : Identity_u):
  ⌊ distrib_left_hand f g (exist _ xs xs_p) -⌋ = VV ↔ distrib_left_hand_rel ⌊ f ⌋ ⌊ g ⌋ xs VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite distrib_left_hand__distrib_left_hand_rel_rw: f_rel_funct_db.

#[global] Hint Resolve distrib_left_hand__distrib_left_hand_rel_rw: rel_ax_db.

#[global] Instance distrib_left_hand_lookup_rw: dictionary rwLem distrib_left_hand := {
    lookup' := distrib_left_hand__distrib_left_hand_rel_rw }.

Theorem distrib_left_hand__distrib_left_hand_rel
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_44453395 : ArgList ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT))
          (v_x_44453395 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {VV: Z | True}) (VV : Z), True) x_44453395 v_x_44453395)))
  (g : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
          (v_x_10329927 : Z),
        ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927)))
  (xs : Identity)
  (VV : Identity_u):
  ⌊ distrib_left_hand f g xs -⌋ = VV ↔ distrib_left_hand_rel ⌊ f ⌋ ⌊ g ⌋ ⌊ xs ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite distrib_left_hand__distrib_left_hand_rel: f_rel_funct_db.

Theorem distrib_left_hand__distrib_left_hand_rel'
  (f_u g_u : @uPack (Z ::UT nilUT) Z)
  (xs_u : Identity_u)
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_44453395 : ArgList ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT))
          (v_x_44453395 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {VV: Z | True}) (VV : Z), True) x_44453395 v_x_44453395)))
  (g : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
          (v_x_10329927 : Z),
        ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927)))
  (xs : Identity)
  (VV : Identity_u):
  f_u = ⌊ f ⌋
  → (g_u = ⌊ g ⌋
     → (xs_u = ⌊ xs ⌋ → ⌊ distrib_left_hand f g xs -⌋ = VV ↔ distrib_left_hand_rel f_u g_u xs_u VV)).
Proof.
  intros -> -> ->. refine (distrib_left_hand__distrib_left_hand_rel f g xs VV).
Qed.

#[global] Hint Resolve distrib_left_hand__distrib_left_hand_rel': f_rel_funct_db.

Theorem distrib_left_hand_rel_mk
  (f : @Pack
       ({lq_tmp0: Z | True} ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp0: Z | True}
  ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_49697850 : ArgList ({lq_tmp0: Z | True} ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT))
          (v_x_49697850 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {lq_tmp0: Z | True}) (VV : Z), True) x_49697850 v_x_49697850)))
  (g : @Pack
       ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_82647028 : ArgList ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
          (v_x_82647028 : Z),
        ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : Z), True) x_82647028 v_x_82647028)))
  (xs : Identity_u)
  (xs_p : Identity_wf xs ∧ True):
  {VV: _ | distrib_left_hand_rel (packProj f) (packProj g) xs VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, distrib_left_hand_rel (packProj f) (packProj g) xs VV)
          (distrib_left_hand f g (exist _ xs xs_p))
          _);
  rewrite <- distrib_left_hand__distrib_left_hand_rel';
  quicksolve.
Qed.

#[global] Hint Resolve distrib_left_hand_rel_mk: f_rel_funct_db.

Definition distrib_right_hand_spec
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_44453395 : ArgList ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT))
          (v_x_44453395 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {VV: Z | True}) (VV : Z), True) x_44453395 v_x_44453395)))
  (g : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
          (v_x_10329927 : Z),
        ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927)))
  (xs : Identity):
  Type :=
  Identity.

#[global] Hint Unfold distrib_right_hand_spec: lia_unfold.

Definition distrib_right_hand
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_44453395 : ArgList ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT))
          (v_x_44453395 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {VV: Z | True}) (VV : Z), True) x_44453395 v_x_44453395)))
  (g : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
          (v_x_10329927 : Z),
        ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927)))
  (xs : Identity):
  distrib_right_hand_spec f g xs.
Proof.
  destruct xs as [xs xs_p].
  refine (composeI
          (fmap f)
          (fmap g)
          (exist (λ (xs : Identity_u), Identity_wf xs ∧ True) xs ltac:(solver))).
Defined.

Inductive distrib_right_hand_rel:
  @uPack (Z ::UT nilUT) Z → @uPack (Z ::UT nilUT) Z → Identity_u → Identity_u → Prop :=
  | distrib_right_hand_Constr: ∀ (f g : @uPack (Z ::UT nilUT) Z) xs (fmap_res : Identity_u),
                               fmap_rel g fmap_res
                               → ∀ (fmap_res_2 : Identity_u),
                                 fmap_rel f fmap_res_2
                                 → ∀ (composeI_res : Identity_u),
                                   composeI_rel fmap_res_2 fmap_res xs composeI_res
                                   → distrib_right_hand_rel f g xs composeI_res.

#[global] Hint Constructors distrib_right_hand_rel: core_hint_db.

#[global] Instance distrib_right_hand_lookup_rel: dictionary rel distrib_right_hand := {
    lookup' := distrib_right_hand_rel }.

#[global] Instance distrib_right_hand_getF: getFunc distrib_right_hand_rel := {
    getF' := distrib_right_hand }.

Theorem distrib_right_hand_rel_funct [f g : @uPack (Z ::UT nilUT) Z] [xs : Identity_u]:
  ∀ (VV VV' : Identity_u),
  distrib_right_hand_rel f g xs VV → (distrib_right_hand_rel f g xs VV' → VV = VV').
Proof.
  rel_functionhood_body.
Qed.

#[global] Hint Resolve distrib_right_hand_rel_funct: f_rel_funct_db.

Theorem distrib_right_hand_inv_lem f g xs distrib_right_hand_inv_lem_res:
  distrib_right_hand_rel f g xs distrib_right_hand_inv_lem_res
  ↔ ∃ (fmap_res : Identity_u),
    fmap_rel g fmap_res
    ∧ ∃ (fmap_res_2 : Identity_u),
      fmap_rel f fmap_res_2
      ∧ ∃ (composeI_res : Identity_u),
        composeI_rel fmap_res_2 fmap_res xs composeI_res ∧ distrib_right_hand_inv_lem_res == composeI_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite distrib_right_hand_inv_lem: f_rel_back.

Theorem distrib_right_hand_rel_ex
  (f : @Pack
       ({lq_tmp0: Z | True} ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp0: Z | True}
  ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_49697850 : ArgList ({lq_tmp0: Z | True} ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT))
          (v_x_49697850 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {lq_tmp0: Z | True}) (VV : Z), True) x_49697850 v_x_49697850)))
  (g : @Pack
       ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_82647028 : ArgList ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
          (v_x_82647028 : Z),
        ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : Z), True) x_82647028 v_x_82647028)))
  (xs : Identity_u)
  (xs_p : Identity_wf xs ∧ True):
  distrib_right_hand_rel ⌊ f ⌋ ⌊ g ⌋ xs ⌊ distrib_right_hand f g (exist _ xs xs_p) -⌋.
Proof.
  Opaque distrib_right_hand.
  existence_lemma_pre distrib_right_hand; fix_notations; simpl in *.
  Transparent distrib_right_hand.
  all: (existence_lemma_quicksolve distrib_right_hand; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve distrib_right_hand_rel_ex: rel_ax_db.

#[global] Opaque distrib_right_hand.

Theorem distrib_right_hand__distrib_right_hand_rel_rw
  (f : @Pack
       ({lq_tmp0: Z | True} ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp0: Z | True}
  ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_49697850 : ArgList ({lq_tmp0: Z | True} ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT))
          (v_x_49697850 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {lq_tmp0: Z | True}) (VV : Z), True) x_49697850 v_x_49697850)))
  (g : @Pack
       ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_82647028 : ArgList ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
          (v_x_82647028 : Z),
        ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : Z), True) x_82647028 v_x_82647028)))
  (xs : Identity_u)
  (xs_p : Identity_wf xs ∧ True)
  (VV : Identity_u):
  ⌊ distrib_right_hand f g (exist _ xs xs_p) -⌋ = VV ↔ distrib_right_hand_rel ⌊ f ⌋ ⌊ g ⌋ xs VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite distrib_right_hand__distrib_right_hand_rel_rw: f_rel_funct_db.

#[global] Hint Resolve distrib_right_hand__distrib_right_hand_rel_rw: rel_ax_db.

#[global] Instance distrib_right_hand_lookup_rw: dictionary rwLem distrib_right_hand := {
    lookup' := distrib_right_hand__distrib_right_hand_rel_rw }.

Theorem distrib_right_hand__distrib_right_hand_rel
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_44453395 : ArgList ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT))
          (v_x_44453395 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {VV: Z | True}) (VV : Z), True) x_44453395 v_x_44453395)))
  (g : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
          (v_x_10329927 : Z),
        ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927)))
  (xs : Identity)
  (VV : Identity_u):
  ⌊ distrib_right_hand f g xs -⌋ = VV ↔ distrib_right_hand_rel ⌊ f ⌋ ⌊ g ⌋ ⌊ xs ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite distrib_right_hand__distrib_right_hand_rel: f_rel_funct_db.

Theorem distrib_right_hand__distrib_right_hand_rel'
  (f_u g_u : @uPack (Z ::UT nilUT) Z)
  (xs_u : Identity_u)
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_44453395 : ArgList ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT))
          (v_x_44453395 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {VV: Z | True}) (VV : Z), True) x_44453395 v_x_44453395)))
  (g : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
          (v_x_10329927 : Z),
        ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927)))
  (xs : Identity)
  (VV : Identity_u):
  f_u = ⌊ f ⌋
  → (g_u = ⌊ g ⌋
     → (xs_u = ⌊ xs ⌋ → ⌊ distrib_right_hand f g xs -⌋ = VV ↔ distrib_right_hand_rel f_u g_u xs_u VV)).
Proof.
  intros -> -> ->. refine (distrib_right_hand__distrib_right_hand_rel f g xs VV).
Qed.

#[global] Hint Resolve distrib_right_hand__distrib_right_hand_rel': f_rel_funct_db.

Theorem distrib_right_hand_rel_mk
  (f : @Pack
       ({lq_tmp0: Z | True} ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp0: Z | True}
  ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_49697850 : ArgList ({lq_tmp0: Z | True} ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT))
          (v_x_49697850 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {lq_tmp0: Z | True}) (VV : Z), True) x_49697850 v_x_49697850)))
  (g : @Pack
       ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_82647028 : ArgList ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
          (v_x_82647028 : Z),
        ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : Z), True) x_82647028 v_x_82647028)))
  (xs : Identity_u)
  (xs_p : Identity_wf xs ∧ True):
  {VV: _ | distrib_right_hand_rel (packProj f) (packProj g) xs VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, distrib_right_hand_rel (packProj f) (packProj g) xs VV)
          (distrib_right_hand f g (exist _ xs xs_p))
          _);
  rewrite <- distrib_right_hand__distrib_right_hand_rel';
  quicksolve.
Qed.

#[global] Hint Resolve distrib_right_hand_rel_mk: f_rel_funct_db.

Definition fmap_distrib_spec
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_44453395 : ArgList ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT))
          (v_x_44453395 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {VV: Z | True}) (VV : Z), True) x_44453395 v_x_44453395)))
  (g : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
          (v_x_10329927 : Z),
        ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927)))
  (ds_dbPT : Identity):
  Type :=
  {{∃ (distrib_left_hand_res : Identity_u),
    distrib_left_hand_rel ⌊ f ⌋ ⌊ g ⌋ ⌊ ds_dbPT ⌋ distrib_left_hand_res
    ∧ ∃ (distrib_right_hand_res : Identity_u),
      distrib_right_hand_rel ⌊ f ⌋ ⌊ g ⌋ ⌊ ds_dbPT ⌋ distrib_right_hand_res
      ∧ distrib_left_hand_res == distrib_right_hand_res}}.

#[global] Hint Unfold fmap_distrib_spec: lia_unfold.

Theorem fmap_distrib
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_44453395 : ArgList ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT))
          (v_x_44453395 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {VV: Z | True}) (VV : Z), True) x_44453395 v_x_44453395)))
  (g : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
          (v_x_10329927 : Z),
        ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : Z), True) x_10329927 v_x_10329927)))
  (ds_dbPT : Identity):
  fmap_distrib_spec f g ds_dbPT.
Proof.
  destruct ds_dbPT as [ds_dbPT ds_dbPT_p].
  destruct ds_dbPT as [x].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (distrib_left_hand_res : Identity_u),
             distrib_left_hand_rel ⌊ f ⌋ ⌊ g ⌋ (Val_u x) distrib_left_hand_res
             ∧ ∃ (distrib_right_hand_res : Identity_u),
               distrib_right_hand_rel ⌊ f ⌋ ⌊ g ⌋ (Val_u x) distrib_right_hand_res
               ∧ distrib_left_hand_res == distrib_right_hand_res)
            (# unit)
            ltac:(solver)).
Qed.

Definition idI_spec (x : Identity): Type :=
  Identity.

#[global] Hint Unfold idI_spec: lia_unfold.

Definition idI (x : Identity): idI_spec x.
Proof.
  destruct x as [x x_p]. refine (exist (λ (x : Identity_u), Identity_wf x ∧ True) x ltac:(solver)).
Defined.

Inductive idI_rel: Identity_u → Identity_u → Prop :=
  | idI_Constr: ∀ x, idI_rel x x.

#[global] Hint Constructors idI_rel: core_hint_db.

#[global] Instance idI_lookup_rel: dictionary rel idI := { lookup' := idI_rel }.

#[global] Instance idI_getF: getFunc idI_rel := { getF' := idI }.

Theorem idI_rel_funct [x : Identity_u]:
  ∀ (VV VV' : Identity_u), idI_rel x VV → (idI_rel x VV' → VV = VV').
Proof.
  rel_functionhood_body.
Qed.

#[global] Hint Resolve idI_rel_funct: f_rel_funct_db.

Theorem idI_inv_lem x idI_inv_lem_res: idI_rel x idI_inv_lem_res ↔ idI_inv_lem_res == x.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite idI_inv_lem: f_rel_back.

Theorem idI_rel_ex (x : Identity_u) (x_p : Identity_wf x ∧ True):
  idI_rel x ⌊ idI (exist _ x x_p) -⌋.
Proof.
  Opaque idI.
  existence_lemma_pre idI; fix_notations; simpl in *.
  Transparent idI.
  all: (existence_lemma_quicksolve idI; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve idI_rel_ex: rel_ax_db.

#[global] Opaque idI.

Theorem idI__idI_rel_rw (x : Identity_u) (x_p : Identity_wf x ∧ True) (VV : Identity_u):
  ⌊ idI (exist _ x x_p) -⌋ = VV ↔ idI_rel x VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite idI__idI_rel_rw: f_rel_funct_db.

#[global] Hint Resolve idI__idI_rel_rw: rel_ax_db.

#[global] Instance idI_lookup_rw: dictionary rwLem idI := { lookup' := idI__idI_rel_rw }.

Theorem idI__idI_rel (x : Identity) (VV : Identity_u): ⌊ idI x -⌋ = VV ↔ idI_rel ⌊ x ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite idI__idI_rel: f_rel_funct_db.

Theorem idI__idI_rel' (x_u : Identity_u) (x : Identity) (VV : Identity_u):
  x_u = ⌊ x ⌋ → ⌊ idI x -⌋ = VV ↔ idI_rel x_u VV.
Proof.
  intros ->. refine (idI__idI_rel x VV).
Qed.

#[global] Hint Resolve idI__idI_rel': f_rel_funct_db.

Theorem idI_rel_mk (x : Identity_u) (x_p : Identity_wf x ∧ True): {VV: _ | idI_rel x VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, idI_rel x VV) (idI (exist _ x x_p)) _);
  rewrite <- idI__idI_rel';
  quicksolve.
Qed.

#[global] Hint Resolve idI_rel_mk: f_rel_funct_db.

#[global] Instance idI_pack:
  @Pack
  (Identity ::RT λ (x : Identity), nilRT)
  (Identity_u ::UT nilUT)
  ltac:(mkProjectsArgListTG ((Identity ::RT λ (x : Identity), nilRT)) ((Identity_u ::UT nilUT)))
  Identity_u
  (λ (x_27420000 : ArgList (Identity ::RT λ (x : Identity), nilRT)) (v_x_27420000 : Identity_u),
   ltac:(flattenP (λ (x : Identity) (VV : Identity_u), Identity_wf VV ∧ True) x_27420000 v_x_27420000)).
Proof.
  buildPackG idI idI_rel idI__idI_rel idI_rel_funct.
Defined.

#[global] Instance idI_upack: @uPack (Identity_u ::UT nilUT) Identity_u.
Proof.
  buildUPackG idI_rel idI_rel_funct.
Defined.

Definition fmap_id_spec (ds_dbPU : Identity): Type :=
  {{∃ (fmap_res : Identity_u),
    fmap_rel id_upack ⌊ ds_dbPU ⌋ fmap_res
    ∧ ∃ (idI_res : Identity_u), idI_rel ⌊ ds_dbPU ⌋ idI_res ∧ fmap_res == idI_res}}.

#[global] Hint Unfold fmap_id_spec: lia_unfold.

Theorem fmap_id (ds_dbPU : Identity): fmap_id_spec ds_dbPU.
Proof.
  destruct ds_dbPU as [ds_dbPU ds_dbPU_p].
  destruct ds_dbPU as [x].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (fmap_res : Identity_u),
             fmap_rel id_upack (Val_u x) fmap_res
             ∧ ∃ (idI_res : Identity_u), idI_rel (Val_u x) idI_res ∧ fmap_res == idI_res)
            (# unit)
            ltac:(solver)).
Qed.
