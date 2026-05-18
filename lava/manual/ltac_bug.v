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
Qed.