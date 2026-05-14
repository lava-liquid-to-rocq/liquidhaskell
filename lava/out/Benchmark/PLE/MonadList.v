From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Set Universe Polymorphism. 
From Coq Require Import Unicode.Utf8.

Inductive L_u: Type :=
  | C_u: Z → L_u → L_u | Emp_u: L_u.

Fixpoint L_eq (x y : L_u): bool :=
  match (x, y) with
  | (C_u VV VV_, C_u VV' VV_') => (true && (VV ==? VV')) && L_eq VV_ VV_'
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
  match x with | C_u VV VV_ => L_wf VV_ ∧ True | Emp_u => True end.

Theorem L_wf_ref [p : L_u → Prop] (tm : {v: L_u | L_wf v ∧ p v}): L_wf ⌊ tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation L := {x: L_u | L_wf x ∧ True}.

Definition C_lem (VV : {VV: Z | True}) (VV_ : L): L_wf (C_u ⌊ VV ⌋ ⌊ VV_ ⌋) ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition C (VV : {VV: Z | True}) (VV_ : L): L :=
  exist _ (C_u ⌊ VV ⌋ ⌊ VV_ ⌋) (C_lem VV VV_).

Definition Emp_lem : L_wf Emp_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Emp : L :=
  exist _ Emp_u Emp_lem.

Definition wf_C_VV_ [VV : Z] [VV_ : L_u] (p : L_wf (C_u VV VV_)): L_wf VV_.
Proof.
  quicksolve.
Defined.

#[global] Hint Resolve wf_C_VV_: ref_constr_db.

#[global] Hint Resolve L_wf_ref: wf_constr_db.

#[global] Hint Unfold L_wf: wf_constr_db.

#[global] Hint Resolve L_eq: ref_constr_db.

#[global] Hint Unfold C: ref_constr_db.

#[global] Hint Unfold Emp: ref_constr_db.

Definition append_spec (ds_d3Io ys : L): Type :=
  L.

#[global] Hint Unfold append_spec: lia_unfold.

Definition append (ds_d3Io ys : L): append_spec ds_d3Io ys.
Proof.
  destruct ds_d3Io as [ds_d3Io ds_d3Io_p].
  destruct ys as [ys ys_p].
  try revert ys_p; generalize dependent ys; induction ds_d3Io as [x xs IH_xs|]; intros.
  - refine (C (# x) (IH_xs ltac:(try clear IH_xs; solver) ys ltac:(try clear IH_xs; solver))).
  - refine (exist (λ (ys : L_u), L_wf ys ∧ True) ys ltac:(solver)).
Defined.

Inductive append_rel: L_u → L_u → L_u → Prop :=
  | append_C_x: ∀ x xs ys (append_res : L_u),
                append_rel xs ys append_res → append_rel (C_u x xs) ys (C_u x append_res)
  | append_Emp_x: ∀ ys, append_rel Emp_u ys ys.

#[global] Hint Constructors append_rel: core_hint_db.

#[global] Instance append_lookup_rel: dictionary rel append := { lookup' := append_rel }.

#[global] Instance append_getF: getFunc append_rel := { getF' := append }.

Theorem append_rel_funct [ds_d3Io ys : L_u]:
  ∀ (VV VV' : L_u), append_rel ds_d3Io ys VV → (append_rel ds_d3Io ys VV' → VV = VV').
Proof.
  try revert ys_p; generalize dependent ys; induction ds_d3Io as [x xs IH_xs|]; intros;
  rel_functionhood_body.
Qed.

#[global] Hint Resolve append_rel_funct: f_rel_funct_db.

Theorem append_C_x_lem x xs ys append_C_x_lem_res:
  append_rel (C_u x xs) ys append_C_x_lem_res
  ↔ ∃ (append_res : L_u), append_rel xs ys append_res ∧ append_C_x_lem_res == C_u x append_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite append_C_x_lem: f_rel_back.

Theorem append_Emp_x_lem ys append_Emp_x_lem_res:
  append_rel Emp_u ys append_Emp_x_lem_res ↔ append_Emp_x_lem_res == ys.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite append_Emp_x_lem: f_rel_back.

Theorem append_rel_ex
  (ds_d3Io : L_u) (ds_d3Io_p : L_wf ds_d3Io ∧ True) (ys : L_u) (ys_p : L_wf ys ∧ True):
  append_rel ds_d3Io ys ⌊ append (exist _ ds_d3Io ds_d3Io_p) (exist _ ys ys_p) -⌋.
Proof.
  Opaque append.
  existence_lemma_pre append;
  try revert ys_p; generalize dependent ys; induction ds_d3Io as [x xs IH_xs|]; intros;
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
  (ds_d3Io : L_u) (ds_d3Io_p : L_wf ds_d3Io ∧ True) (ys : L_u) (ys_p : L_wf ys ∧ True) (VV : L_u):
  ⌊ append (exist _ ds_d3Io ds_d3Io_p) (exist _ ys ys_p) -⌋ = VV ↔ append_rel ds_d3Io ys VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite append__append_rel_rw: f_rel_funct_db.

#[global] Hint Resolve append__append_rel_rw: rel_ax_db.

#[global] Instance append_lookup_rw: dictionary rwLem append := {
    lookup' := append__append_rel_rw }.

Theorem append__append_rel (ds_d3Io ys : L) (VV : L_u):
  ⌊ append ds_d3Io ys -⌋ = VV ↔ append_rel ⌊ ds_d3Io ⌋ ⌊ ys ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite append__append_rel: f_rel_funct_db.

Theorem append__append_rel' (ds_d3Io_u ys_u : L_u) (ds_d3Io ys : L) (VV : L_u):
  ds_d3Io_u = ⌊ ds_d3Io ⌋
  → (ys_u = ⌊ ys ⌋ → ⌊ append ds_d3Io ys -⌋ = VV ↔ append_rel ds_d3Io_u ys_u VV).
Proof.
  intros -> ->. refine (append__append_rel ds_d3Io ys VV).
Qed.

#[global] Hint Resolve append__append_rel': f_rel_funct_db.

Theorem append_rel_mk
  (ds_d3Io : L_u) (ds_d3Io_p : L_wf ds_d3Io ∧ True) (ys : L_u) (ys_p : L_wf ys ∧ True):
  {VV: _ | append_rel ds_d3Io ys VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, append_rel ds_d3Io ys VV)
          (append (exist _ ds_d3Io ds_d3Io_p) (exist _ ys ys_p))
          _);
  rewrite <- append__append_rel';
  quicksolve.
Qed.

#[global] Hint Resolve append_rel_mk: f_rel_funct_db.

#[global] Instance append_pack:
  @Pack
  (L ::RT λ (ds_d3Io : L), L ::RT λ (ys : L), nilRT)
  (L_u ::UT (L_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((L ::RT λ (ds_d3Io : L), L ::RT λ (ys : L), nilRT)) ((L_u ::UT (L_u ::UT nilUT))))
  L_u
  (λ (x_84885443 : ArgList (L ::RT λ (ds_d3Io : L), L ::RT λ (ys : L), nilRT)) (v_x_84885443 : L_u),
   ltac:(flattenP (λ (ds_d3Io ys : L) (VV : L_u), L_wf VV ∧ True) x_84885443 v_x_84885443)).
Proof.
  buildPackG append append_rel append__append_rel append_rel_funct.
Defined.

#[global] Instance append_upack: @uPack (L_u ::UT (L_u ::UT nilUT)) L_u.
Proof.
  buildUPackG append_rel append_rel_funct.
Defined.

Definition bind_spec
  (ds_d3Ir : L)
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       L_u
       (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
          (v_x_10329927 : L_u),
        ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : L_u), L_wf VV ∧ True) x_10329927 v_x_10329927))):
  Type :=
  L.

#[global] Hint Unfold bind_spec: lia_unfold.

Definition bind
  (ds_d3Ir : L)
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       L_u
       (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
          (v_x_10329927 : L_u),
        ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : L_u), L_wf VV ∧ True) x_10329927 v_x_10329927))):
  bind_spec ds_d3Ir f.
Proof.
  destruct ds_d3Ir as [ds_d3Ir ds_d3Ir_p].
  try revert f_p; generalize dependent f; induction ds_d3Ir as [x xs IH_xs|]; intros.
  - refine (append (getPackF f (# x)) (IH_xs ltac:(try clear IH_xs; solver) f)).
  - refine Emp.
Defined.

Inductive bind_rel: L_u → @uPack (Z ::UT nilUT) L_u → L_u → Prop :=
  | bind_C_x: ∀ x xs (f : @uPack (Z ::UT nilUT) L_u) (bind_res : L_u),
              bind_rel xs f bind_res
              → ∀ (f_res : L_u),
                getUPackRel f x f_res
                → ∀ (append_res : L_u), append_rel f_res bind_res append_res → bind_rel (C_u x xs) f append_res
  | bind_Emp_x: ∀ (f : @uPack (Z ::UT nilUT) L_u), bind_rel Emp_u f Emp_u.

#[global] Hint Constructors bind_rel: core_hint_db.

#[global] Instance bind_lookup_rel: dictionary rel bind := { lookup' := bind_rel }.

#[global] Instance bind_getF: getFunc bind_rel := { getF' := bind }.

Theorem bind_rel_funct [ds_d3Ir : L_u] [f : @uPack (Z ::UT nilUT) L_u]:
  ∀ (VV VV' : L_u), bind_rel ds_d3Ir f VV → (bind_rel ds_d3Ir f VV' → VV = VV').
Proof.
  try revert f_p; generalize dependent f; induction ds_d3Ir as [x xs IH_xs|]; intros;
  rel_functionhood_body.
Qed.

#[global] Hint Resolve bind_rel_funct: f_rel_funct_db.

Theorem bind_C_x_lem f x xs bind_C_x_lem_res:
  bind_rel (C_u x xs) f bind_C_x_lem_res
  ↔ ∃ (bind_res : L_u),
    bind_rel xs f bind_res
    ∧ ∃ (f_res : L_u),
      getUPackRel f x f_res
      ∧ ∃ (append_res : L_u), append_rel f_res bind_res append_res ∧ bind_C_x_lem_res == append_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite bind_C_x_lem: f_rel_back.

Theorem bind_Emp_x_lem f bind_Emp_x_lem_res:
  bind_rel Emp_u f bind_Emp_x_lem_res ↔ bind_Emp_x_lem_res == Emp_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite bind_Emp_x_lem: f_rel_back.

Theorem bind_rel_ex
  (ds_d3Ir : L_u)
  (ds_d3Ir_p : L_wf ds_d3Ir ∧ True)
  (f : @Pack
       ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
       L_u
       (λ (x_82647028 : ArgList ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
          (v_x_82647028 : L_u),
        ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : L_u), L_wf VV ∧ True) x_82647028 v_x_82647028))):
  bind_rel ds_d3Ir ⌊ f ⌋ ⌊ bind (exist _ ds_d3Ir ds_d3Ir_p) f -⌋.
Proof.
  Opaque bind.
  existence_lemma_pre bind;
  try revert f_p; generalize dependent f; induction ds_d3Ir as [x xs IH_xs|]; intros;
  [fix_notations;
   pose proof (IH_xs ltac:(try clear IH_xs; solver) f) as IH_29745491;
   try clear IH_xs |
   fix_notations];
  simpl in *.
  Transparent bind.
  all: (existence_lemma_quicksolve bind; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve bind_rel_ex: rel_ax_db.

#[global] Opaque bind.

Theorem bind__bind_rel_rw
  (ds_d3Ir : L_u)
  (ds_d3Ir_p : L_wf ds_d3Ir ∧ True)
  (f : @Pack
       ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
       L_u
       (λ (x_82647028 : ArgList ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
          (v_x_82647028 : L_u),
        ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : L_u), L_wf VV ∧ True) x_82647028 v_x_82647028)))
  (VV : L_u):
  ⌊ bind (exist _ ds_d3Ir ds_d3Ir_p) f -⌋ = VV ↔ bind_rel ds_d3Ir ⌊ f ⌋ VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite bind__bind_rel_rw: f_rel_funct_db.

#[global] Hint Resolve bind__bind_rel_rw: rel_ax_db.

#[global] Instance bind_lookup_rw: dictionary rwLem bind := { lookup' := bind__bind_rel_rw }.

Theorem bind__bind_rel
  (ds_d3Ir : L)
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       L_u
       (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
          (v_x_10329927 : L_u),
        ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : L_u), L_wf VV ∧ True) x_10329927 v_x_10329927)))
  (VV : L_u):
  ⌊ bind ds_d3Ir f -⌋ = VV ↔ bind_rel ⌊ ds_d3Ir ⌋ ⌊ f ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite bind__bind_rel: f_rel_funct_db.

Theorem bind__bind_rel'
  (ds_d3Ir_u : L_u)
  (f_u : @uPack (Z ::UT nilUT) L_u)
  (ds_d3Ir : L)
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       L_u
       (λ (x_10329927 : ArgList ({VV: Z | True} ::RT λ (lq_tmp2 : {VV: Z | True}), nilRT))
          (v_x_10329927 : L_u),
        ltac:(flattenP (λ (lq_tmp2 : {VV: Z | True}) (VV : L_u), L_wf VV ∧ True) x_10329927 v_x_10329927)))
  (VV : L_u):
  ds_d3Ir_u = ⌊ ds_d3Ir ⌋ → (f_u = ⌊ f ⌋ → ⌊ bind ds_d3Ir f -⌋ = VV ↔ bind_rel ds_d3Ir_u f_u VV).
Proof.
  intros -> ->. refine (bind__bind_rel ds_d3Ir f VV).
Qed.

#[global] Hint Resolve bind__bind_rel': f_rel_funct_db.

Theorem bind_rel_mk
  (ds_d3Ir : L_u)
  (ds_d3Ir_p : L_wf ds_d3Ir ∧ True)
  (f : @Pack
       ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp2: Z | True}
  ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT)) ((Z ::UT nilUT)))
       L_u
       (λ (x_82647028 : ArgList ({lq_tmp2: Z | True} ::RT λ (lq_tmp2 : {lq_tmp2: Z | True}), nilRT))
          (v_x_82647028 : L_u),
        ltac:(flattenP (λ (lq_tmp2 : {lq_tmp2: Z | True}) (VV : L_u), L_wf VV ∧ True) x_82647028 v_x_82647028))):
  {VV: _ | bind_rel ds_d3Ir (packProj f) VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, bind_rel ds_d3Ir (packProj f) VV)
          (bind (exist _ ds_d3Ir ds_d3Ir_p) f)
          _);
  rewrite <- bind__bind_rel';
  quicksolve.
Qed.

#[global] Hint Resolve bind_rel_mk: f_rel_funct_db.

Definition prop_append_neutral_spec (ds_d3Im : L): Type :=
  {{∃ (append_res : L_u), append_rel ⌊ ds_d3Im ⌋ Emp_u append_res ∧ append_res == ⌊ ds_d3Im ⌋}}.

#[global] Hint Unfold prop_append_neutral_spec: lia_unfold.

Theorem prop_append_neutral (ds_d3Im : L): prop_append_neutral_spec ds_d3Im.
Proof.
  destruct ds_d3Im as [ds_d3Im ds_d3Im_p].
  induction ds_d3Im as [x xs IH_xs|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (append_res : L_u), append_rel (C_u x xs) Emp_u append_res ∧ append_res == C_u x xs)
            (IH_xs ltac:(try clear IH_xs; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (append_res : L_u), append_rel Emp_u Emp_u append_res ∧ append_res == Emp_u)
            (# unit)
            ltac:(solver)).
Qed.

Definition retrn_spec (x : {x: Z | True}): Type :=
  L.

#[global] Hint Unfold retrn_spec: lia_unfold.

Definition retrn (x : {x: Z | True}): retrn_spec x.
Proof.
  destruct x as [x x_p]. refine (C (# x) Emp).
Defined.

Inductive retrn_rel: Z → L_u → Prop :=
  | retrn_Constr: ∀ x, retrn_rel x (C_u x Emp_u).

#[global] Hint Constructors retrn_rel: core_hint_db.

#[global] Instance retrn_lookup_rel: dictionary rel retrn := { lookup' := retrn_rel }.

#[global] Instance retrn_getF: getFunc retrn_rel := { getF' := retrn }.

Theorem retrn_rel_funct [x : Z]: ∀ (VV VV' : L_u), retrn_rel x VV → (retrn_rel x VV' → VV = VV').
Proof.
  rel_functionhood_body.
Qed.

#[global] Hint Resolve retrn_rel_funct: f_rel_funct_db.

Theorem retrn_inv_lem x retrn_inv_lem_res:
  retrn_rel x retrn_inv_lem_res ↔ retrn_inv_lem_res == C_u x Emp_u.
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

Theorem retrn__retrn_rel_rw (x : Z) (x_p : True) (VV : L_u):
  ⌊ retrn (exist _ x x_p) -⌋ = VV ↔ retrn_rel x VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite retrn__retrn_rel_rw: f_rel_funct_db.

#[global] Hint Resolve retrn__retrn_rel_rw: rel_ax_db.

#[global] Instance retrn_lookup_rw: dictionary rwLem retrn := { lookup' := retrn__retrn_rel_rw }.

Theorem retrn__retrn_rel (x : {x: Z | True}) (VV : L_u): ⌊ retrn x -⌋ = VV ↔ retrn_rel ⌊ x ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite retrn__retrn_rel: f_rel_funct_db.

Theorem retrn__retrn_rel' (x_u : Z) (x : {x: Z | True}) (VV : L_u):
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
  L_u
  (λ (x_11473763 : ArgList ({x: Z | True} ::RT λ (x : {x: Z | True}), nilRT)) (v_x_11473763 : L_u),
   ltac:(flattenP (λ (x : {x: Z | True}) (VV : L_u), L_wf VV ∧ True) x_11473763 v_x_11473763)).
Proof.
  buildPackG retrn retrn_rel retrn__retrn_rel retrn_rel_funct.
Defined.

#[global] Instance retrn_upack: @uPack (Z ::UT nilUT) L_u.
Proof.
  buildUPackG retrn_rel retrn_rel_funct.
Defined.

Definition left_identity_spec
  (x : {x: Z | True})
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       L_u
       (λ (x_44453395 : ArgList ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT))
          (v_x_44453395 : L_u),
        ltac:(flattenP (λ (lq_tmp0 : {VV: Z | True}) (VV : L_u), L_wf VV ∧ True) x_44453395 v_x_44453395))):
  Type :=
  {{∃ (retrn_res : L_u),
    retrn_rel ⌊ x ⌋ retrn_res
    ∧ ∃ (bind_res : L_u),
      bind_rel retrn_res ⌊ f ⌋ bind_res
      ∧ ∃ (f_res : L_u), getPackRel f ⌊ x ⌋ f_res ∧ bind_res == f_res}}.

#[global] Hint Unfold left_identity_spec: lia_unfold.

Theorem left_identity
  (x : {x: Z | True})
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       L_u
       (λ (x_44453395 : ArgList ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT))
          (v_x_44453395 : L_u),
        ltac:(flattenP (λ (lq_tmp0 : {VV: Z | True}) (VV : L_u), L_wf VV ∧ True) x_44453395 v_x_44453395))):
  left_identity_spec x f.
Proof.
  destruct x as [x x_p].
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (retrn_res : L_u),
           retrn_rel x retrn_res
           ∧ ∃ (bind_res : L_u),
             bind_rel retrn_res ⌊ f ⌋ bind_res ∧ ∃ (f_res : L_u), getPackRel f x f_res ∧ bind_res == f_res)
          (prop_append_neutral (getPackF f (# x)))
          ltac:(solver)).
Qed.

Definition right_identity_spec (ds_d3In : L): Type :=
  {{∃ (bind_res : L_u), bind_rel ⌊ ds_d3In ⌋ retrn_upack bind_res ∧ bind_res == ⌊ ds_d3In ⌋}}.

#[global] Hint Unfold right_identity_spec: lia_unfold.

Theorem right_identity (ds_d3In : L): right_identity_spec ds_d3In.
Proof.
  destruct ds_d3In as [ds_d3In ds_d3In_p].
  induction ds_d3In as [x xs IH_xs|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (bind_res : L_u), bind_rel (C_u x xs) retrn_upack bind_res ∧ bind_res == C_u x xs)
            (IH_xs ltac:(try clear IH_xs; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (bind_res : L_u), bind_rel Emp_u retrn_upack bind_res ∧ bind_res == Emp_u)
            (# unit)
            ltac:(solver)).
Qed.
