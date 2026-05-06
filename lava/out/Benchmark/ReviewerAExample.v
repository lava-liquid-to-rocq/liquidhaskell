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

Theorem IList_wf_ref [p : IList_u → Prop] (tm : {v: IList_u | IList_wf v ∧ p v}): IList_wf ⌊ tm ⌋.
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

Definition llen_spec (l : IList): Type :=
  {v: Z | gebZ_rel v 0 true}.

#[global] Hint Unfold llen_spec: lia_unfold.

Definition llen (l : IList): llen_spec l.
Proof.
  destruct l as [l l_p].
  induction l as [ds_d4QZ l' IH_l'|].
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
  | llen_Cons: ∀ ds_d4QZ l' llen_res,
               llen_rel l' llen_res
               → ∀ addZ_res, addZ_rel llen_res 1 addZ_res → llen_rel (Cons_u ds_d4QZ l') addZ_res
  | llen_Nil: llen_rel Nil_u 0.

#[global] Hint Constructors llen_rel: core_hint_db.

#[global] Instance llen_lookup_rel: dictionary rel llen := { lookup' := llen_rel }.

#[global] Instance llen_getF: getFunc llen_rel := { getF' := llen }.

Theorem llen_rel_funct [l : IList_u]: ∀ (v v' : Z), llen_rel l v → (llen_rel l v' → v = v').
Proof.
  induction l as [ds_d4QZ l' IH_l'|]; rel_functionhood_body.
Qed.

#[global] Hint Resolve llen_rel_funct: f_rel_funct_db.

Theorem llen_Cons_lem ds_d4QZ l' llen_Cons_lem_res:
  llen_rel (Cons_u ds_d4QZ l') llen_Cons_lem_res
  ↔ ∃ llen_res,
    llen_rel l' llen_res ∧ ∃ addZ_res, addZ_rel llen_res 1 addZ_res ∧ llen_Cons_lem_res == addZ_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite llen_Cons_lem: f_rel_back.

Theorem llen_Nil_lem llen_Nil_lem_res: llen_rel Nil_u llen_Nil_lem_res ↔ llen_Nil_lem_res == 0.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite llen_Nil_lem: f_rel_back.

Theorem llen_rel_ex (l : IList_u) (l_p : IList_wf l ∧ True): llen_rel l ⌊ llen (exist _ l l_p) ⌋.
Proof.
  Opaque llen.
  existence_lemma_pre llen;
  induction l as [ds_d4QZ l' IH_l'|];
  [fix_notations; pose proof (IH_l' ltac:(try clear IH_l'; solver)) as IH_91252151; try clear IH_l' |
   fix_notations];
  simpl in *.
  Transparent llen.
  all: existence_lemma_quicksolve llen; f__f_rel_ex_body; f_rel_finish.
Qed.

#[global] Hint Resolve llen_rel_ex: rel_ax_db.

#[global] Opaque llen.

Theorem llen__llen_rel_rw (l : IList_u) (l_p : IList_wf l ∧ True) (v : Z):
  ⌊ llen (exist _ l l_p) ⌋ = v ↔ llen_rel l v.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite llen__llen_rel_rw: f_rel_funct_db.

#[global] Hint Resolve llen__llen_rel_rw: rel_ax_db.

#[global] Instance llen_lookup_rw: dictionary rwLem llen := { lookup' := llen__llen_rel_rw }.

Theorem llen__llen_rel (l : IList) (v : Z): ⌊ llen l ⌋ = v ↔ llen_rel ⌊ l ⌋ v.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite llen__llen_rel: f_rel_funct_db.

Theorem llen__llen_rel' (l_u : IList_u) (l : IList) (v : Z):
  l_u = ⌊ l ⌋ → ⌊ llen l ⌋ = v ↔ llen_rel l_u v.
Proof.
  intros ->. refine (llen__llen_rel l v).
Qed.

#[global] Hint Resolve llen__llen_rel': f_rel_funct_db.

Theorem llen_rel_mk (l : IList_u) (l_p : IList_wf l ∧ True): {v: _ | llen_rel l v}.
Proof.
  intros;
  refine (subsumptionCast _ (λ v, llen_rel l v) (llen (exist _ l l_p)) _);
  rewrite <- llen__llen_rel';
  quicksolve.
Qed.

#[global] Hint Resolve llen_rel_mk: f_rel_funct_db.

#[global] Instance llen_pack:
  @Pack
  (IList ::RT λ (l : IList), nilRT)
  (IList_u ::UT nilUT)
  ltac:(mkProjectsArgListTG ((IList ::RT λ (l : IList), nilRT)) ((IList_u ::UT nilUT)))
  Z
  (λ (x_87895698 : ArgList (IList ::RT λ (l : IList), nilRT)) (v_x_87895698 : Z),
   ltac:(flattenP (λ (l : IList) (v : Z), gebZ_rel v 0 true) x_87895698 v_x_87895698)).
Proof.
  buildPackG llen llen_rel llen__llen_rel llen_rel_funct.
Defined.

#[global] Instance llen_upack: @uPack (IList_u ::UT nilUT) Z.
Proof.
  buildUPackG llen_rel llen_rel_funct.
Defined.

Definition get_spec
  (xs : IList)
  (i : {i: Z | ∀ llen_res, llen_rel ⌊ xs ⌋ llen_res → lebZ_rel 0 i true ∧ ltbZ_rel i llen_res true}):
  Type :=
  {v: Z | ltbZ_rel 5 v true}.

#[global] Hint Unfold get_spec: lia_unfold.

Definition get
  (xs : IList)
  (i : {i: Z | ∀ llen_res, llen_rel ⌊ xs ⌋ llen_res → lebZ_rel 0 i true ∧ ltbZ_rel i llen_res true}):
  get_spec xs i.
Proof.
  destruct xs as [xs xs_p].
  destruct i as [i i_p].
  try revert i_p; generalize dependent i; induction xs as [x xs' IH_xs'|]; intros.
  - let E := fresh "E" in destruct (i ==? 0) as [|] eqn:E;
    [refine (IH_xs' ltac:(try clear IH_xs'; solver) (i - 1) ltac:(try clear IH_xs'; solver)) |
     refine (exist (λ (n : Z), ltbZ_rel 5 n true) x ltac:(solver))].
  - intros; exfalso; solver.
Defined.

Inductive get_rel: IList_u → Z → Z → Prop :=
  | get_Cons_x_False: ∀ x xs' i,
                      (i ==? 0) == false
                      → ∀ subZ_res,
                        subZ_rel i 1 subZ_res
                        → ∀ get_res, get_rel xs' subZ_res get_res → get_rel (Cons_u x xs') i get_res
  | get_Cons_x_True: ∀ x xs' i, (i ==? 0) == true → get_rel (Cons_u x xs') i x.

#[global] Hint Constructors get_rel: core_hint_db.

#[global] Instance get_lookup_rel: dictionary rel get := { lookup' := get_rel }.

#[global] Instance get_getF: getFunc get_rel := { getF' := get }.

Theorem get_rel_funct [xs : IList_u] [i : Z]:
  ∀ (v v' : Z), get_rel xs i v → (get_rel xs i v' → v = v').
Proof.
  try revert i_p; generalize dependent i; induction xs as [x xs' IH_xs'|]; intros;
  [let E := fresh "E" in destruct (i ==? 0) as [|] eqn:E |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve get_rel_funct: f_rel_funct_db.

Theorem get_Cons_x_lem i x xs' get_Cons_x_lem_res:
  get_rel (Cons_u x xs') i get_Cons_x_lem_res
  ↔ ((i ==? 0) == false
     → ∃ subZ_res,
       subZ_rel i 1 subZ_res ∧ ∃ get_res, get_rel xs' subZ_res get_res ∧ get_Cons_x_lem_res == get_res)
    ∨ ((i ==? 0) == true → get_Cons_x_lem_res == x).
Proof.
  rel_back' ((i ==? 0) _::_ _nil).
Qed.

#[global] Hint Rewrite get_Cons_x_lem: f_rel_back.

Theorem get_rel_ex
  (xs : IList_u)
  (xs_p : IList_wf xs ∧ True)
  (i : Z)
  (i_p : ∀ llen_res, llen_rel xs llen_res → lebZ_rel 0 i true ∧ ltbZ_rel i llen_res true):
  get_rel xs i ⌊ get (exist _ xs xs_p) (exist _ i i_p) ⌋.
Proof.
  Opaque get.
  existence_lemma_pre get;
  try revert i_p; generalize dependent i; induction xs as [x xs' IH_xs'|]; intros;
  [let E := fresh "E" in destruct (i ==? 0) as [|] eqn:E;
   [fix_notations;
    pose proof (IH_xs'
                ltac:(try clear IH_xs'; solver)
                (i - 1)
                ltac:(try clear IH_xs'; solver)) as IH_79916954;
    try clear IH_xs' |
    fix_notations] |];
  simpl in *.
  Transparent get.
  all: existence_lemma_quicksolve get; f__f_rel_ex_body; f_rel_finish.
Qed.

#[global] Hint Resolve get_rel_ex: rel_ax_db.

#[global] Opaque get.

Theorem get__get_rel_rw
  (xs : IList_u)
  (xs_p : IList_wf xs ∧ True)
  (i : Z)
  (i_p : ∀ llen_res, llen_rel xs llen_res → lebZ_rel 0 i true ∧ ltbZ_rel i llen_res true)
  (v : Z):
  ⌊ get (exist _ xs xs_p) (exist _ i i_p) ⌋ = v ↔ get_rel xs i v.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite get__get_rel_rw: f_rel_funct_db.

#[global] Hint Resolve get__get_rel_rw: rel_ax_db.

#[global] Instance get_lookup_rw: dictionary rwLem get := { lookup' := get__get_rel_rw }.

Theorem get__get_rel
  (xs : IList)
  (i : {i: Z | ∀ llen_res, llen_rel ⌊ xs ⌋ llen_res → lebZ_rel 0 i true ∧ ltbZ_rel i llen_res true})
  (v : Z):
  ⌊ get xs i ⌋ = v ↔ get_rel ⌊ xs ⌋ ⌊ i ⌋ v.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite get__get_rel: f_rel_funct_db.

Theorem get__get_rel'
  (xs_u : IList_u)
  (i_u : Z)
  (xs : IList)
  (i : {i: Z | ∀ llen_res, llen_rel ⌊ xs ⌋ llen_res → lebZ_rel 0 i true ∧ ltbZ_rel i llen_res true})
  (v : Z):
  xs_u = ⌊ xs ⌋ → (i_u = ⌊ i ⌋ → ⌊ get xs i ⌋ = v ↔ get_rel xs_u i_u v).
Proof.
  intros -> ->. refine (get__get_rel xs i v).
Qed.

#[global] Hint Resolve get__get_rel': f_rel_funct_db.

Theorem get_rel_mk
  (xs : IList_u)
  (xs_p : IList_wf xs ∧ True)
  (i : Z)
  (i_p : ∀ llen_res, llen_rel xs llen_res → lebZ_rel 0 i true ∧ ltbZ_rel i llen_res true):
  {v: _ | get_rel xs i v}.
Proof.
  intros;
  refine (subsumptionCast _ (λ v, get_rel xs i v) (get (exist _ xs xs_p) (exist _ i i_p)) _);
  rewrite <- get__get_rel';
  quicksolve.
Qed.

#[global] Hint Resolve get_rel_mk: f_rel_funct_db.

#[global] Instance get_pack:
  @Pack
  (IList
   ::RT λ (xs : IList),
        {i: Z | ∀ llen_res, llen_rel ⌊ xs ⌋ llen_res → lebZ_rel 0 i true ∧ ltbZ_rel i llen_res true}
        ::RT λ (i : {i: Z | ∀ llen_res,
                            llen_rel ⌊ xs ⌋ llen_res → lebZ_rel 0 i true ∧ ltbZ_rel i llen_res true}),
             nilRT)
  (IList_u ::UT (Z ::UT nilUT))
  ltac:(mkProjectsArgListTG ((IList
  ::RT λ (xs : IList),
       {i: Z | ∀ llen_res,
               llen_rel ⌊ xs ⌋ llen_res
               → lebZ_rel 0 i true ∧ ltbZ_rel i llen_res true}
       ::RT λ (i : {i: Z | ∀ llen_res,
                           llen_rel ⌊ xs ⌋ llen_res
                           → lebZ_rel 0 i true ∧ ltbZ_rel i llen_res true}),
            nilRT)) ((IList_u ::UT (Z ::UT nilUT))))
  Z
  (λ (x_35545252 : ArgList (IList
                            ::RT λ (xs : IList),
                                 {i: Z | ∀ llen_res,
                                         llen_rel ⌊ xs ⌋ llen_res → lebZ_rel 0 i true ∧ ltbZ_rel i llen_res true}
                                 ::RT λ (i : {i: Z | ∀ llen_res,
                                                     llen_rel ⌊ xs ⌋ llen_res
                                                     → lebZ_rel 0 i true ∧ ltbZ_rel i llen_res true}),
                                      nilRT))
     (v_x_35545252 : Z),
   ltac:(flattenP (λ (xs : IList)
   (i : {i: Z | ∀ llen_res,
                llen_rel ⌊ xs ⌋ llen_res
                → lebZ_rel 0 i true ∧ ltbZ_rel i llen_res true})
   (v : Z),
 ltbZ_rel 5 v true) x_35545252 v_x_35545252)).
Proof.
  buildPackG get get_rel get__get_rel get_rel_funct.
Defined.

#[global] Instance get_upack: @uPack (IList_u ::UT (Z ::UT nilUT)) Z.
Proof.
  buildUPackG get_rel get_rel_funct.
Defined.

Definition surprise_spec (x : {x: Z | True}) (l : IList): Type :=
  {{∀ get_res, get_rel Nil_u 4 get_res → get_res == 10}}.

#[global] Hint Unfold surprise_spec: lia_unfold.

Theorem surprise (x : {x: Z | True}) (l : IList): surprise_spec x l.
Proof.
  destruct x as [x x_p].
  destruct l as [l l_p].
  refine (subsumptionCast
          Unit
          (λ (u : Unit), ∀ get_res, get_rel Nil_u 4 get_res → get_res == 10)
          (# unit)
          ltac:(solver)).
Qed.
