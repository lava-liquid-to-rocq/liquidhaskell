From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Set Universe Polymorphism. 
From Coq Require Import Unicode.Utf8.

Inductive IList_u: Type :=
  | Cons_u: Z → IList_u → IList_u | Nil_u: IList_u.

Fixpoint IList_eq (x y : IList_u): bool :=
  match (x, y) with
  | (Cons_u n l, Cons_u n' l') => (true && (n ==? n')) && IList_eq l l'
  | (Nil_u, Nil_u) => true
  | (_, _) => false
  end.

Theorem IList_eq_refl : ∀ (x : IList_u), is_true (IList_eq x x).
Proof.
  eq_refl_rec.
Qed.

#[global] Hint Resolve IList_eq_refl: eq_hint_db.

Theorem IList_eqb_eq : ∀ (s t : IList_u), is_true (IList_eq s t) → s = t.
Proof.
  eqb_eq_lem.
Qed.

#[global] Hint Resolve IList_eqb_eq: eq_hint_db.

#[global] Instance leibnitz_eq_IList: LeibnitzEqB := {
    equalB' := IList_eq;
    refl' := IList_eq_refl;
    eqb_eq' := IList_eqb_eq }.

Fixpoint IList_wf (x : IList_u): Prop :=
  match x with | Cons_u n l => ltbZ_rel 5 n true ∧ (IList_wf l ∧ True) | Nil_u => True end.

Theorem IList_wf_ref [p : IList_u → Prop] (tm : {v: IList_u | IList_wf v ∧ p v}): IList_wf ⌊ tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation IList := {x: IList_u | IList_wf x ∧ True}.

Definition Cons_lem (n : {n: Z | ltbZ_rel 5 n true}) (l : IList):
  IList_wf (Cons_u ⌊ n ⌋ ⌊ l ⌋) ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Cons (n : {n: Z | ltbZ_rel 5 n true}) (l : IList): IList :=
  exist _ (Cons_u ⌊ n ⌋ ⌊ l ⌋) (Cons_lem n l).

Definition Nil_lem : IList_wf Nil_u ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Nil : IList :=
  exist _ Nil_u Nil_lem.

Definition wf_Cons_l [n : Z] [l : IList_u] (p : IList_wf (Cons_u n l)): IList_wf l.
Proof.
  quicksolve.
Defined.

#[global] Hint Resolve wf_Cons_l: ref_constr_db.

#[global] Hint Resolve IList_wf_ref: wf_constr_db.

#[global] Hint Unfold IList_wf: wf_constr_db.

#[global] Hint Resolve IList_eq: ref_constr_db.

#[global] Hint Unfold Cons: ref_constr_db.

#[global] Hint Unfold Nil: ref_constr_db.

Definition llen_spec (ds_d4QY : IList): Type :=
  {v: Z | gebZ_rel v 0 true}.

#[global] Hint Unfold llen_spec: lia_unfold.

Definition llen (ds_d4QY : IList): llen_spec ds_d4QY.
Proof.
  destruct ds_d4QY as [ds_d4QY ds_d4QY_p].
  induction ds_d4QY as [ds_d4QZ l' IH_l'|].
  - refine (subsumptionCast
            Z
            (λ (v : Z), gebZ_rel v 0 true)
            (subsumptionCast Z (λ (x_1 : Z), True) (IH_l' ltac:(try clear IH_l'; solver)) ltac:(solver)
             +Z subsumptionCast
                Z
                (λ (x_2 : Z), True)
                (exist (λ (VV : Z), VV == 1) 1 ltac:(solver))
                ltac:(solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Z
            (λ (v : Z), gebZ_rel v 0 true)
            (exist (λ (VV : Z), VV == 0) 0 ltac:(solver))
            ltac:(solver)).
Defined.

Inductive llen_rel: IList_u → Z → Prop :=
  | llen_Cons: ∀ ds_d4QZ l' (llen_res : Z),
               llen_rel l' llen_res
               → ∀ (addZ_res : Z), addZ_rel llen_res 1 addZ_res → llen_rel (Cons_u ds_d4QZ l') addZ_res
  | llen_Nil: llen_rel Nil_u 0.

#[global] Hint Constructors llen_rel: core_hint_db.

#[global] Instance llen_lookup_rel: dictionary rel llen := { lookup' := llen_rel }.

#[global] Instance llen_getF: getFunc llen_rel := { getF' := llen }.

Theorem llen_rel_funct [ds_d4QY : IList_u]:
  ∀ (v v' : Z), llen_rel ds_d4QY v → (llen_rel ds_d4QY v' → v = v').
Proof.
  induction ds_d4QY as [ds_d4QZ l' IH_l'|]; rel_functionhood_body.
Qed.

#[global] Hint Resolve llen_rel_funct: f_rel_funct_db.

Theorem llen_Cons_lem ds_d4QZ l' llen_Cons_lem_res:
  llen_rel (Cons_u ds_d4QZ l') llen_Cons_lem_res
  ↔ ∃ (llen_res : Z),
    llen_rel l' llen_res
    ∧ ∃ (addZ_res : Z), addZ_rel llen_res 1 addZ_res ∧ llen_Cons_lem_res == addZ_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite llen_Cons_lem: f_rel_back.

Theorem llen_Nil_lem llen_Nil_lem_res: llen_rel Nil_u llen_Nil_lem_res ↔ llen_Nil_lem_res == 0.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite llen_Nil_lem: f_rel_back.

Theorem llen_rel_ex (ds_d4QY : IList_u) (ds_d4QY_p : IList_wf ds_d4QY ∧ True):
  llen_rel ds_d4QY ⌊ llen (exist _ ds_d4QY ds_d4QY_p) -⌋.
Proof.
  Opaque llen.
  existence_lemma_pre llen;
  induction ds_d4QY as [ds_d4QZ l' IH_l'|];
  [fix_notations; pose proof (IH_l' ltac:(try clear IH_l'; solver)) as IH_91252151; try clear IH_l' |
   fix_notations];
  simpl in *.
  Transparent llen.
  all: (existence_lemma_quicksolve llen; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve llen_rel_ex: rel_ax_db.

#[global] Opaque llen.

Theorem llen__llen_rel_rw (ds_d4QY : IList_u) (ds_d4QY_p : IList_wf ds_d4QY ∧ True) (v : Z):
  ⌊ llen (exist _ ds_d4QY ds_d4QY_p) -⌋ = v ↔ llen_rel ds_d4QY v.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite llen__llen_rel_rw: f_rel_funct_db.

#[global] Hint Resolve llen__llen_rel_rw: rel_ax_db.

#[global] Instance llen_lookup_rw: dictionary rwLem llen := { lookup' := llen__llen_rel_rw }.

Theorem llen__llen_rel (ds_d4QY : IList) (v : Z): ⌊ llen ds_d4QY -⌋ = v ↔ llen_rel ⌊ ds_d4QY ⌋ v.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite llen__llen_rel: f_rel_funct_db.

Theorem llen__llen_rel' (ds_d4QY_u : IList_u) (ds_d4QY : IList) (v : Z):
  ds_d4QY_u = ⌊ ds_d4QY ⌋ → ⌊ llen ds_d4QY -⌋ = v ↔ llen_rel ds_d4QY_u v.
Proof.
  intros ->. refine (llen__llen_rel ds_d4QY v).
Qed.

#[global] Hint Resolve llen__llen_rel': f_rel_funct_db.

Theorem llen_rel_mk (ds_d4QY : IList_u) (ds_d4QY_p : IList_wf ds_d4QY ∧ True):
  {v: _ | llen_rel ds_d4QY v}.
Proof.
  intros;
  refine (subsumptionCast _ (λ v, llen_rel ds_d4QY v) (llen (exist _ ds_d4QY ds_d4QY_p)) _);
  rewrite <- llen__llen_rel';
  quicksolve.
Qed.

#[global] Hint Resolve llen_rel_mk: f_rel_funct_db.

#[global] Instance llen_pack:
  @Pack
  (IList ::RT λ (ds_d4QY : IList), nilRT)
  (IList_u ::UT nilUT)
  ltac:(mkProjectsArgListTG (IList ::RT λ (ds_d4QY : IList), nilRT) ((IList_u ::UT nilUT)))
  Z
  (λ (x_21409491 : ArgList (IList ::RT λ (ds_d4QY : IList), nilRT)) (v_x_21409491 : Z),
   ltac:(flattenP (λ (ds_d4QY : IList) (v : Z), gebZ_rel v 0 true) x_21409491 v_x_21409491)).
Proof.
  buildPackG llen llen_rel llen__llen_rel llen_rel_funct.
Defined.

#[global] Instance llen_upack: @uPack (IList_u ::UT nilUT) Z.
Proof.
  buildUPackG llen_rel llen_rel_funct.
Defined.

Definition get_spec
  (ds_d4QV : IList)
  (i' : {i': Z | lebZ_rel 0 i' true
                 ∧ ∃ (llen_res : Z), llen_rel ⌊ ds_d4QV ⌋ llen_res ∧ ltbZ_rel i' llen_res true}):
  Type :=
  {v: Z | ltbZ_rel 5 v true}.

#[global] Hint Unfold get_spec: lia_unfold.

Definition get
  (ds_d4QV : IList)
  (i' : {i': Z | lebZ_rel 0 i' true
                 ∧ ∃ (llen_res : Z), llen_rel ⌊ ds_d4QV ⌋ llen_res ∧ ltbZ_rel i' llen_res true}):
  get_spec ds_d4QV i'.
Proof.
  destruct ds_d4QV as [ds_d4QV ds_d4QV_p].
  destruct i' as [i' i'_p].
  try revert i'_p; generalize dependent i'; induction ds_d4QV as [x xs' IH_xs'|]; intros.
  - let E := fresh "E" in destruct (i' ==? 0) as [|] eqn:E;
    [refine (exist (λ (n : Z), ltbZ_rel 5 n true) x ltac:(solver)) |
     refine (IH_xs' ltac:(try clear IH_xs'; solver) (i' - 1) ltac:(try clear IH_xs'; solver))].
  - intros; exfalso; solver.
Defined.

Inductive get_rel: IList_u → Z → Z → Prop :=
  | get_Cons_x_True: ∀ x xs' i', (i' ==? 0) == true → get_rel (Cons_u x xs') i' x
  | get_Cons_x_False: ∀ x xs' i',
                      (i' ==? 0) == false
                      → ∀ (subZ_res : Z),
                        subZ_rel i' 1 subZ_res
                        → ∀ (get_res : Z), get_rel xs' subZ_res get_res → get_rel (Cons_u x xs') i' get_res.

#[global] Hint Constructors get_rel: core_hint_db.

#[global] Instance get_lookup_rel: dictionary rel get := { lookup' := get_rel }.

#[global] Instance get_getF: getFunc get_rel := { getF' := get }.

Theorem get_rel_funct [ds_d4QV : IList_u] [i' : Z]:
  ∀ (v v' : Z), get_rel ds_d4QV i' v → (get_rel ds_d4QV i' v' → v = v').
Proof.
  try revert i'_p; generalize dependent i'; induction ds_d4QV as [x xs' IH_xs'|]; intros;
  [let E := fresh "E" in destruct (i' ==? 0) as [|] eqn:E |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve get_rel_funct: f_rel_funct_db.

Theorem get_Cons_x_lem i' x xs' get_Cons_x_lem_res:
  get_rel (Cons_u x xs') i' get_Cons_x_lem_res
  ↔ (i' ==? 0) == true ∧ get_Cons_x_lem_res == x
    ∨ (i' ==? 0) == false
      ∧ ∃ (subZ_res : Z),
        subZ_rel i' 1 subZ_res
        ∧ ∃ (get_res : Z), get_rel xs' subZ_res get_res ∧ get_Cons_x_lem_res == get_res.
Proof.
  rel_back' ((i' ==? 0) _::_ _nil).
Qed.

#[global] Hint Rewrite get_Cons_x_lem: f_rel_back.

Theorem get_rel_ex
  (ds_d4QV : IList_u)
  (ds_d4QV_p : IList_wf ds_d4QV ∧ True)
  (i' : Z)
  (i'_p : lebZ_rel 0 i' true
          ∧ ∃ (llen_res : Z), llen_rel ds_d4QV llen_res ∧ ltbZ_rel i' llen_res true):
  get_rel ds_d4QV i' ⌊ get (exist _ ds_d4QV ds_d4QV_p) (exist _ i' i'_p) -⌋.
Proof.
  Opaque get.
  existence_lemma_pre get;
  try revert i'_p; generalize dependent i'; induction ds_d4QV as [x xs' IH_xs'|]; intros;
  [let E := fresh "E" in destruct (i' ==? 0) as [|] eqn:E;
   [fix_notations |
    fix_notations;
    pose proof (IH_xs'
                ltac:(try clear IH_xs'; solver)
                (i' - 1)
                ltac:(try clear IH_xs'; solver)) as IH_21013558;
    try clear IH_xs'] |];
  simpl in *.
  Transparent get.
  all: (existence_lemma_quicksolve get; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve get_rel_ex: rel_ax_db.

#[global] Opaque get.

Theorem get__get_rel_rw
  (ds_d4QV : IList_u)
  (ds_d4QV_p : IList_wf ds_d4QV ∧ True)
  (i' : Z)
  (i'_p : lebZ_rel 0 i' true
          ∧ ∃ (llen_res : Z), llen_rel ds_d4QV llen_res ∧ ltbZ_rel i' llen_res true)
  (v : Z):
  ⌊ get (exist _ ds_d4QV ds_d4QV_p) (exist _ i' i'_p) -⌋ = v ↔ get_rel ds_d4QV i' v.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite get__get_rel_rw: f_rel_funct_db.

#[global] Hint Resolve get__get_rel_rw: rel_ax_db.

#[global] Instance get_lookup_rw: dictionary rwLem get := { lookup' := get__get_rel_rw }.

Theorem get__get_rel
  (ds_d4QV : IList)
  (i' : {i': Z | lebZ_rel 0 i' true
                 ∧ ∃ (llen_res : Z), llen_rel ⌊ ds_d4QV ⌋ llen_res ∧ ltbZ_rel i' llen_res true})
  (v : Z):
  ⌊ get ds_d4QV i' -⌋ = v ↔ get_rel ⌊ ds_d4QV ⌋ ⌊ i' ⌋ v.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite get__get_rel: f_rel_funct_db.

Theorem get__get_rel'
  (ds_d4QV_u : IList_u)
  (i'_u : Z)
  (ds_d4QV : IList)
  (i' : {i': Z | lebZ_rel 0 i' true
                 ∧ ∃ (llen_res : Z), llen_rel ⌊ ds_d4QV ⌋ llen_res ∧ ltbZ_rel i' llen_res true})
  (v : Z):
  ds_d4QV_u = ⌊ ds_d4QV ⌋ → (i'_u = ⌊ i' ⌋ → ⌊ get ds_d4QV i' -⌋ = v ↔ get_rel ds_d4QV_u i'_u v).
Proof.
  intros -> ->. refine (get__get_rel ds_d4QV i' v).
Qed.

#[global] Hint Resolve get__get_rel': f_rel_funct_db.

Theorem get_rel_mk
  (ds_d4QV : IList_u)
  (ds_d4QV_p : IList_wf ds_d4QV ∧ True)
  (i' : Z)
  (i'_p : lebZ_rel 0 i' true
          ∧ ∃ (llen_res : Z), llen_rel ds_d4QV llen_res ∧ ltbZ_rel i' llen_res true):
  {v: _ | get_rel ds_d4QV i' v}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ v, get_rel ds_d4QV i' v)
          (get (exist _ ds_d4QV ds_d4QV_p) (exist _ i' i'_p))
          _);
  rewrite <- get__get_rel';
  quicksolve.
Qed.

#[global] Hint Resolve get_rel_mk: f_rel_funct_db.

#[global] Instance get_pack:
  @Pack
  (IList
   ::RT λ (ds_d4QV : IList),
        {i': Z | lebZ_rel 0 i' true
                 ∧ ∃ (llen_res : Z), llen_rel ⌊ ds_d4QV ⌋ llen_res ∧ ltbZ_rel i' llen_res true}
        ::RT λ (i' : {i': Z | lebZ_rel 0 i' true
                              ∧ ∃ (llen_res : Z), llen_rel ⌊ ds_d4QV ⌋ llen_res ∧ ltbZ_rel i' llen_res true}),
             nilRT)
  (IList_u ::UT (Z ::UT nilUT))
  ltac:(mkProjectsArgListTG (IList
 ::RT λ (ds_d4QV : IList),
      {i': Z | lebZ_rel 0 i' true
               ∧ ∃ (llen_res : Z),
                 llen_rel ⌊ ds_d4QV ⌋ llen_res ∧ ltbZ_rel i' llen_res true}
      ::RT λ (i' : {i': Z | lebZ_rel 0 i' true
                            ∧ ∃ (llen_res : Z),
                              llen_rel ⌊ ds_d4QV ⌋ llen_res ∧ ltbZ_rel i' llen_res true}),
           nilRT) ((IList_u ::UT (Z ::UT nilUT))))
  Z
  (λ (x_59913007 : ArgList (IList
                            ::RT λ (ds_d4QV : IList),
                                 {i': Z | lebZ_rel 0 i' true
                                          ∧ ∃ (llen_res : Z), llen_rel ⌊ ds_d4QV ⌋ llen_res ∧ ltbZ_rel i' llen_res true}
                                 ::RT λ (i' : {i': Z | lebZ_rel 0 i' true
                                                       ∧ ∃ (llen_res : Z),
                                                         llen_rel ⌊ ds_d4QV ⌋ llen_res ∧ ltbZ_rel i' llen_res true}),
                                      nilRT))
     (v_x_59913007 : Z),
   ltac:(flattenP (λ (ds_d4QV : IList)
   (i' : {i': Z | lebZ_rel 0 i' true
                  ∧ ∃ (llen_res : Z),
                    llen_rel ⌊ ds_d4QV ⌋ llen_res ∧ ltbZ_rel i' llen_res true})
   (v : Z),
 ltbZ_rel 5 v true) x_59913007 v_x_59913007)).
Proof.
  buildPackG get get_rel get__get_rel get_rel_funct.
Defined.

#[global] Instance get_upack: @uPack (IList_u ::UT (Z ::UT nilUT)) Z.
Proof.
  buildUPackG get_rel get_rel_funct.
Defined.

Definition surprise_spec (ds_d4QT : {ds_d4QT: Z | True}) (ds_d4QU : IList): Type :=
  {{∃ (get_res : Z), get_rel Nil_u 4 get_res ∧ get_res == 10}}.

#[global] Hint Unfold surprise_spec: lia_unfold.

Theorem surprise (ds_d4QT : {ds_d4QT: Z | True}) (ds_d4QU : IList): surprise_spec ds_d4QT ds_d4QU.
Proof.
  destruct ds_d4QT as [ds_d4QT ds_d4QT_p].
  destruct ds_d4QU as [ds_d4QU ds_d4QU_p].
  refine (subsumptionCast
          Unit
          (λ (u : Unit), ∃ (get_res : Z), get_rel Nil_u 4 get_res ∧ get_res == 10)
          (# unit)
          ltac:(solver)).
Qed.
