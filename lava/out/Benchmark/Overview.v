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

Definition llen_spec (ds_d27K : IList): Type :=
  {v: Z | gebZ_rel v 0 true}.

#[global] Hint Unfold llen_spec: lia_unfold.

Definition llen (ds_d27K : IList): llen_spec ds_d27K.
Proof.
  destruct ds_d27K as [ds_d27K ds_d27K_p].
  induction ds_d27K as [ds_d27L l' IH_l'|].
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
  | llen_Cons: ∀ ds_d27L l' (llen_res : Z),
               llen_rel l' llen_res
               → ∀ (addZ_res : Z), addZ_rel llen_res 1 addZ_res → llen_rel (Cons_u ds_d27L l') addZ_res
  | llen_Nil: llen_rel Nil_u 0.

#[global] Hint Constructors llen_rel: core_hint_db.

#[global] Instance llen_lookup_rel: dictionary rel llen := { lookup' := llen_rel }.

#[global] Instance llen_getF: getFunc llen_rel := { getF' := llen }.

Theorem llen_rel_funct [ds_d27K : IList_u]:
  ∀ (v v' : Z), llen_rel ds_d27K v → (llen_rel ds_d27K v' → v = v').
Proof.
  induction ds_d27K as [ds_d27L l' IH_l'|]; rel_functionhood_body.
Qed.

#[global] Hint Resolve llen_rel_funct: f_rel_funct_db.

Theorem llen_Cons_lem ds_d27L l' llen_Cons_lem_res:
  llen_rel (Cons_u ds_d27L l') llen_Cons_lem_res
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

Theorem llen_rel_ex (ds_d27K : IList_u) (ds_d27K_p : IList_wf ds_d27K ∧ True):
  llen_rel ds_d27K ⌊ llen (exist _ ds_d27K ds_d27K_p) -⌋.
Proof.
  Opaque llen.
  existence_lemma_pre llen;
  induction ds_d27K as [ds_d27L l' IH_l'|];
  [fix_notations; pose proof (IH_l' ltac:(try clear IH_l'; solver)) as IH_91252151; try clear IH_l' |
   fix_notations];
  simpl in *.
  Transparent llen.
  all: (existence_lemma_quicksolve llen; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve llen_rel_ex: rel_ax_db.

#[global] Opaque llen.

Theorem llen__llen_rel_rw (ds_d27K : IList_u) (ds_d27K_p : IList_wf ds_d27K ∧ True) (v : Z):
  ⌊ llen (exist _ ds_d27K ds_d27K_p) -⌋ = v ↔ llen_rel ds_d27K v.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite llen__llen_rel_rw: f_rel_funct_db.

#[global] Hint Resolve llen__llen_rel_rw: rel_ax_db.

#[global] Instance llen_lookup_rw: dictionary rwLem llen := { lookup' := llen__llen_rel_rw }.

Theorem llen__llen_rel (ds_d27K : IList) (v : Z): ⌊ llen ds_d27K -⌋ = v ↔ llen_rel ⌊ ds_d27K ⌋ v.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite llen__llen_rel: f_rel_funct_db.

Theorem llen__llen_rel' (ds_d27K_u : IList_u) (ds_d27K : IList) (v : Z):
  ds_d27K_u = ⌊ ds_d27K ⌋ → ⌊ llen ds_d27K -⌋ = v ↔ llen_rel ds_d27K_u v.
Proof.
  intros ->. refine (llen__llen_rel ds_d27K v).
Qed.

#[global] Hint Resolve llen__llen_rel': f_rel_funct_db.

Theorem llen_rel_mk (ds_d27K : IList_u) (ds_d27K_p : IList_wf ds_d27K ∧ True):
  {v: _ | llen_rel ds_d27K v}.
Proof.
  intros;
  refine (subsumptionCast _ (λ v, llen_rel ds_d27K v) (llen (exist _ ds_d27K ds_d27K_p)) _);
  rewrite <- llen__llen_rel';
  quicksolve.
Qed.

#[global] Hint Resolve llen_rel_mk: f_rel_funct_db.

#[global] Instance llen_pack:
  @Pack
  (IList ::RT λ (ds_d27K : IList), nilRT)
  (IList_u ::UT nilUT)
  ltac:(mkProjectsArgListTG ((IList ::RT λ (ds_d27K : IList), nilRT)) ((IList_u ::UT nilUT)))
  Z
  (λ (x_41325663 : ArgList (IList ::RT λ (ds_d27K : IList), nilRT)) (v_x_41325663 : Z),
   ltac:(flattenP (λ (ds_d27K : IList) (v : Z), gebZ_rel v 0 true) x_41325663 v_x_41325663)).
Proof.
  buildPackG llen llen_rel llen__llen_rel llen_rel_funct.
Defined.

#[global] Instance llen_upack: @uPack (IList_u ::UT nilUT) Z.
Proof.
  buildUPackG llen_rel llen_rel_funct.
Defined.

Definition append_spec (ds_d27C ys : IList): Type :=
  {v: IList_u | IList_wf v
                ∧ ∃ (llen_res : Z),
                  llen_rel v llen_res
                  ∧ ∃ (llen_res_2 : Z),
                    llen_rel ⌊ ds_d27C ⌋ llen_res_2
                    ∧ ∃ (llen_res_3 : Z),
                      llen_rel ⌊ ys ⌋ llen_res_3
                      ∧ ∃ (addZ_res : Z), addZ_rel llen_res_2 llen_res_3 addZ_res ∧ llen_res == addZ_res}.

#[global] Hint Unfold append_spec: lia_unfold.

Definition append (ds_d27C ys : IList): append_spec ds_d27C ys.
Proof.
  destruct ds_d27C as [ds_d27C ds_d27C_p].
  destruct ys as [ys ys_p].
  try revert ys_p; generalize dependent ys; induction ds_d27C as [x xs IH_xs|]; intros.
  - refine (subsumptionCast
            IList_u
            (λ (v : IList_u),
             IList_wf v
             ∧ ∃ (llen_res : Z),
               llen_rel v llen_res
               ∧ ∃ (llen_res_2 : Z),
                 llen_rel (Cons_u x xs) llen_res_2
                 ∧ ∃ (llen_res_3 : Z),
                   llen_rel ys llen_res_3
                   ∧ ∃ (addZ_res : Z), addZ_rel llen_res_2 llen_res_3 addZ_res ∧ llen_res == addZ_res)
            (Cons
             (exist (λ (n : Z), ltbZ_rel 5 n true) x ltac:(solver))
             (subsumptionCast
              IList_u
              (λ (l : IList_u), IList_wf l ∧ True)
              (IH_xs ltac:(try clear IH_xs; solver) ys ltac:(try clear IH_xs; solver))
              ltac:(solver)))
            ltac:(solver)).
  - refine (subsumptionCast
            IList_u
            (λ (v : IList_u),
             IList_wf v
             ∧ ∃ (llen_res : Z),
               llen_rel v llen_res
               ∧ ∃ (llen_res_2 : Z),
                 llen_rel Nil_u llen_res_2
                 ∧ ∃ (llen_res_3 : Z),
                   llen_rel ys llen_res_3
                   ∧ ∃ (addZ_res : Z), addZ_rel llen_res_2 llen_res_3 addZ_res ∧ llen_res == addZ_res)
            (exist (λ (ys : IList_u), IList_wf ys ∧ True) ys ltac:(solver))
            ltac:(solver)).
Defined.

Inductive append_rel: IList_u → IList_u → IList_u → Prop :=
  | append_Cons_x: ∀ x xs ys (append_res : IList_u),
                   append_rel xs ys append_res → append_rel (Cons_u x xs) ys (Cons_u x append_res)
  | append_Nil_x: ∀ ys, append_rel Nil_u ys ys.

#[global] Hint Constructors append_rel: core_hint_db.

#[global] Instance append_lookup_rel: dictionary rel append := { lookup' := append_rel }.

#[global] Instance append_getF: getFunc append_rel := { getF' := append }.

Theorem append_rel_funct [ds_d27C ys : IList_u]:
  ∀ (v v' : IList_u), append_rel ds_d27C ys v → (append_rel ds_d27C ys v' → v = v').
Proof.
  try revert ys_p; generalize dependent ys; induction ds_d27C as [x xs IH_xs|]; intros;
  rel_functionhood_body.
Qed.

#[global] Hint Resolve append_rel_funct: f_rel_funct_db.

Theorem append_Cons_x_lem x xs ys append_Cons_x_lem_res:
  append_rel (Cons_u x xs) ys append_Cons_x_lem_res
  ↔ ∃ (append_res : IList_u),
    append_rel xs ys append_res ∧ append_Cons_x_lem_res == Cons_u x append_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite append_Cons_x_lem: f_rel_back.

Theorem append_Nil_x_lem ys append_Nil_x_lem_res:
  append_rel Nil_u ys append_Nil_x_lem_res ↔ append_Nil_x_lem_res == ys.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite append_Nil_x_lem: f_rel_back.

Theorem append_rel_ex
  (ds_d27C : IList_u)
  (ds_d27C_p : IList_wf ds_d27C ∧ True)
  (ys : IList_u)
  (ys_p : IList_wf ys ∧ True):
  append_rel ds_d27C ys ⌊ append (exist _ ds_d27C ds_d27C_p) (exist _ ys ys_p) -⌋.
Proof.
  Opaque append.
  existence_lemma_pre append;
  try revert ys_p; generalize dependent ys; induction ds_d27C as [x xs IH_xs|]; intros;
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
  (ds_d27C : IList_u)
  (ds_d27C_p : IList_wf ds_d27C ∧ True)
  (ys : IList_u)
  (ys_p : IList_wf ys ∧ True)
  (v : IList_u):
  ⌊ append (exist _ ds_d27C ds_d27C_p) (exist _ ys ys_p) -⌋ = v ↔ append_rel ds_d27C ys v.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite append__append_rel_rw: f_rel_funct_db.

#[global] Hint Resolve append__append_rel_rw: rel_ax_db.

#[global] Instance append_lookup_rw: dictionary rwLem append := {
    lookup' := append__append_rel_rw }.

Theorem append__append_rel (ds_d27C ys : IList) (v : IList_u):
  ⌊ append ds_d27C ys -⌋ = v ↔ append_rel ⌊ ds_d27C ⌋ ⌊ ys ⌋ v.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite append__append_rel: f_rel_funct_db.

Theorem append__append_rel' (ds_d27C_u ys_u : IList_u) (ds_d27C ys : IList) (v : IList_u):
  ds_d27C_u = ⌊ ds_d27C ⌋
  → (ys_u = ⌊ ys ⌋ → ⌊ append ds_d27C ys -⌋ = v ↔ append_rel ds_d27C_u ys_u v).
Proof.
  intros -> ->. refine (append__append_rel ds_d27C ys v).
Qed.

#[global] Hint Resolve append__append_rel': f_rel_funct_db.

Theorem append_rel_mk
  (ds_d27C : IList_u)
  (ds_d27C_p : IList_wf ds_d27C ∧ True)
  (ys : IList_u)
  (ys_p : IList_wf ys ∧ True):
  {v: _ | append_rel ds_d27C ys v}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ v, append_rel ds_d27C ys v)
          (append (exist _ ds_d27C ds_d27C_p) (exist _ ys ys_p))
          _);
  rewrite <- append__append_rel';
  quicksolve.
Qed.

#[global] Hint Resolve append_rel_mk: f_rel_funct_db.

#[global] Instance append_pack:
  @Pack
  (IList ::RT λ (ds_d27C : IList), IList ::RT λ (ys : IList), nilRT)
  (IList_u ::UT (IList_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((IList
  ::RT λ (ds_d27C : IList), IList ::RT λ (ys : IList), nilRT)) ((IList_u ::UT (IList_u ::UT nilUT))))
  IList_u
  (λ (x_77572722 : ArgList (IList ::RT λ (ds_d27C : IList), IList ::RT λ (ys : IList), nilRT))
     (v_x_77572722 : IList_u),
   ltac:(flattenP (λ (ds_d27C ys : IList) (v : IList_u),
 IList_wf v
 ∧ ∃ (llen_res : Z),
   llen_rel v llen_res
   ∧ ∃ (llen_res_2 : Z),
     llen_rel ⌊ ds_d27C ⌋ llen_res_2
     ∧ ∃ (llen_res_3 : Z),
       llen_rel ⌊ ys ⌋ llen_res_3
       ∧ ∃ (addZ_res : Z),
         addZ_rel llen_res_2 llen_res_3 addZ_res ∧ llen_res == addZ_res) x_77572722 v_x_77572722)).
Proof.
  buildPackG append append_rel append__append_rel append_rel_funct.
Defined.

#[global] Instance append_upack: @uPack (IList_u ::UT (IList_u ::UT nilUT)) IList_u.
Proof.
  buildUPackG append_rel append_rel_funct.
Defined.

Definition get_spec
  (ds_d27H : IList)
  (i' : {i': Z | lebZ_rel 0 i' true
                 ∧ ∃ (llen_res : Z), llen_rel ⌊ ds_d27H ⌋ llen_res ∧ ltbZ_rel i' llen_res true}):
  Type :=
  {v: Z | ltbZ_rel 5 v true}.

#[global] Hint Unfold get_spec: lia_unfold.

Definition get
  (ds_d27H : IList)
  (i' : {i': Z | lebZ_rel 0 i' true
                 ∧ ∃ (llen_res : Z), llen_rel ⌊ ds_d27H ⌋ llen_res ∧ ltbZ_rel i' llen_res true}):
  get_spec ds_d27H i'.
Proof.
  destruct ds_d27H as [ds_d27H ds_d27H_p].
  destruct i' as [i' i'_p].
  try revert i'_p; generalize dependent i'; induction ds_d27H as [x xs' IH_xs'|]; intros.
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

Theorem get_rel_funct [ds_d27H : IList_u] [i' : Z]:
  ∀ (v v' : Z), get_rel ds_d27H i' v → (get_rel ds_d27H i' v' → v = v').
Proof.
  try revert i'_p; generalize dependent i'; induction ds_d27H as [x xs' IH_xs'|]; intros;
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
  (ds_d27H : IList_u)
  (ds_d27H_p : IList_wf ds_d27H ∧ True)
  (i' : Z)
  (i'_p : lebZ_rel 0 i' true
          ∧ ∃ (llen_res : Z), llen_rel ds_d27H llen_res ∧ ltbZ_rel i' llen_res true):
  get_rel ds_d27H i' ⌊ get (exist _ ds_d27H ds_d27H_p) (exist _ i' i'_p) -⌋.
Proof.
  Opaque get.
  existence_lemma_pre get;
  try revert i'_p; generalize dependent i'; induction ds_d27H as [x xs' IH_xs'|]; intros;
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
  (ds_d27H : IList_u)
  (ds_d27H_p : IList_wf ds_d27H ∧ True)
  (i' : Z)
  (i'_p : lebZ_rel 0 i' true
          ∧ ∃ (llen_res : Z), llen_rel ds_d27H llen_res ∧ ltbZ_rel i' llen_res true)
  (v : Z):
  ⌊ get (exist _ ds_d27H ds_d27H_p) (exist _ i' i'_p) -⌋ = v ↔ get_rel ds_d27H i' v.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite get__get_rel_rw: f_rel_funct_db.

#[global] Hint Resolve get__get_rel_rw: rel_ax_db.

#[global] Instance get_lookup_rw: dictionary rwLem get := { lookup' := get__get_rel_rw }.

Theorem get__get_rel
  (ds_d27H : IList)
  (i' : {i': Z | lebZ_rel 0 i' true
                 ∧ ∃ (llen_res : Z), llen_rel ⌊ ds_d27H ⌋ llen_res ∧ ltbZ_rel i' llen_res true})
  (v : Z):
  ⌊ get ds_d27H i' -⌋ = v ↔ get_rel ⌊ ds_d27H ⌋ ⌊ i' ⌋ v.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite get__get_rel: f_rel_funct_db.

Theorem get__get_rel'
  (ds_d27H_u : IList_u)
  (i'_u : Z)
  (ds_d27H : IList)
  (i' : {i': Z | lebZ_rel 0 i' true
                 ∧ ∃ (llen_res : Z), llen_rel ⌊ ds_d27H ⌋ llen_res ∧ ltbZ_rel i' llen_res true})
  (v : Z):
  ds_d27H_u = ⌊ ds_d27H ⌋ → (i'_u = ⌊ i' ⌋ → ⌊ get ds_d27H i' -⌋ = v ↔ get_rel ds_d27H_u i'_u v).
Proof.
  intros -> ->. refine (get__get_rel ds_d27H i' v).
Qed.

#[global] Hint Resolve get__get_rel': f_rel_funct_db.

Theorem get_rel_mk
  (ds_d27H : IList_u)
  (ds_d27H_p : IList_wf ds_d27H ∧ True)
  (i' : Z)
  (i'_p : lebZ_rel 0 i' true
          ∧ ∃ (llen_res : Z), llen_rel ds_d27H llen_res ∧ ltbZ_rel i' llen_res true):
  {v: _ | get_rel ds_d27H i' v}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ v, get_rel ds_d27H i' v)
          (get (exist _ ds_d27H ds_d27H_p) (exist _ i' i'_p))
          _);
  rewrite <- get__get_rel';
  quicksolve.
Qed.

#[global] Hint Resolve get_rel_mk: f_rel_funct_db.

#[global] Instance get_pack:
  @Pack
  (IList
   ::RT λ (ds_d27H : IList),
        {i': Z | lebZ_rel 0 i' true
                 ∧ ∃ (llen_res : Z), llen_rel ⌊ ds_d27H ⌋ llen_res ∧ ltbZ_rel i' llen_res true}
        ::RT λ (i' : {i': Z | lebZ_rel 0 i' true
                              ∧ ∃ (llen_res : Z), llen_rel ⌊ ds_d27H ⌋ llen_res ∧ ltbZ_rel i' llen_res true}),
             nilRT)
  (IList_u ::UT (Z ::UT nilUT))
  ltac:(mkProjectsArgListTG ((IList
  ::RT λ (ds_d27H : IList),
       {i': Z | lebZ_rel 0 i' true
                ∧ ∃ (llen_res : Z),
                  llen_rel ⌊ ds_d27H ⌋ llen_res ∧ ltbZ_rel i' llen_res true}
       ::RT λ (i' : {i': Z | lebZ_rel 0 i' true
                             ∧ ∃ (llen_res : Z),
                               llen_rel ⌊ ds_d27H ⌋ llen_res ∧ ltbZ_rel i' llen_res true}),
            nilRT)) ((IList_u ::UT (Z ::UT nilUT))))
  Z
  (λ (x_50037210 : ArgList (IList
                            ::RT λ (ds_d27H : IList),
                                 {i': Z | lebZ_rel 0 i' true
                                          ∧ ∃ (llen_res : Z), llen_rel ⌊ ds_d27H ⌋ llen_res ∧ ltbZ_rel i' llen_res true}
                                 ::RT λ (i' : {i': Z | lebZ_rel 0 i' true
                                                       ∧ ∃ (llen_res : Z),
                                                         llen_rel ⌊ ds_d27H ⌋ llen_res ∧ ltbZ_rel i' llen_res true}),
                                      nilRT))
     (v_x_50037210 : Z),
   ltac:(flattenP (λ (ds_d27H : IList)
   (i' : {i': Z | lebZ_rel 0 i' true
                  ∧ ∃ (llen_res : Z),
                    llen_rel ⌊ ds_d27H ⌋ llen_res ∧ ltbZ_rel i' llen_res true})
   (v : Z),
 ltbZ_rel 5 v true) x_50037210 v_x_50037210)).
Proof.
  buildPackG get get_rel get__get_rel get_rel_funct.
Defined.

#[global] Instance get_upack: @uPack (IList_u ::UT (Z ::UT nilUT)) Z.
Proof.
  buildUPackG get_rel get_rel_funct.
Defined.

Definition applyToFirst_spec
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_44453395 : ArgList ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT))
          (v_x_44453395 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {VV: Z | True}) (y : Z), ltbZ_rel 5 y true) x_44453395 v_x_44453395)))
  (ds_d27z : {ds_d27z: IList_u | IList_wf ds_d27z
                                 ∧ ∃ (llen_res : Z), llen_rel ds_d27z llen_res ∧ llen_res ≠ 0}):
  Type :=
  {v: Z | ∃ (get_res : Z),
          get_rel ⌊ ds_d27z ⌋ 0 get_res ∧ ∃ (f_res : Z), getPackRel f get_res f_res ∧ v == f_res}.

#[global] Hint Unfold applyToFirst_spec: lia_unfold.

Definition applyToFirst
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_44453395 : ArgList ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT))
          (v_x_44453395 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {VV: Z | True}) (y : Z), ltbZ_rel 5 y true) x_44453395 v_x_44453395)))
  (ds_d27z : {ds_d27z: IList_u | IList_wf ds_d27z
                                 ∧ ∃ (llen_res : Z), llen_rel ds_d27z llen_res ∧ llen_res ≠ 0}):
  applyToFirst_spec f ds_d27z.
Proof.
  destruct ds_d27z as [ds_d27z ds_d27z_p].
  destruct ds_d27z as [x l'|].
  - refine (subsumptionCast
            Z
            (λ (v : Z),
             ∃ (get_res : Z),
             get_rel (Cons_u x l') 0 get_res ∧ ∃ (f_res : Z), getPackRel f get_res f_res ∧ v == f_res)
            (getPackF f
             (subsumptionCast
              Z
              (λ (VV : Z), True)
              (exist (λ (n : Z), ltbZ_rel 5 n true) x ltac:(solver))
              ltac:(solver)))
            ltac:(solver)).
  - intros; exfalso; solver.
Defined.

Inductive applyToFirst_rel: @uPack (Z ::UT nilUT) Z → IList_u → Z → Prop :=
  | applyToFirst_x_Cons: ∀ (f : @uPack (Z ::UT nilUT) Z) l' x (f_res : Z),
                         getUPackRel f x f_res → applyToFirst_rel f (Cons_u x l') f_res.

#[global] Hint Constructors applyToFirst_rel: core_hint_db.

#[global] Instance applyToFirst_lookup_rel: dictionary rel applyToFirst := {
    lookup' := applyToFirst_rel }.

#[global] Instance applyToFirst_getF: getFunc applyToFirst_rel := { getF' := applyToFirst }.

Theorem applyToFirst_rel_funct [f : @uPack (Z ::UT nilUT) Z] [ds_d27z : IList_u]:
  ∀ (v v' : Z), applyToFirst_rel f ds_d27z v → (applyToFirst_rel f ds_d27z v' → v = v').
Proof.
  destruct ds_d27z as [x l'|]; rel_functionhood_body.
Qed.

#[global] Hint Resolve applyToFirst_rel_funct: f_rel_funct_db.

Theorem applyToFirst_x_Cons_lem f l' x applyToFirst_x_Cons_lem_res:
  applyToFirst_rel f (Cons_u x l') applyToFirst_x_Cons_lem_res
  ↔ ∃ (f_res : Z), getUPackRel f x f_res ∧ applyToFirst_x_Cons_lem_res == f_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite applyToFirst_x_Cons_lem: f_rel_back.

Theorem applyToFirst_rel_ex
  (f : @Pack
       ({lq_tmp0: Z | True} ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp0: Z | True}
  ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_49697850 : ArgList ({lq_tmp0: Z | True} ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT))
          (v_x_49697850 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {lq_tmp0: Z | True}) (y : Z), ltbZ_rel 5 y true) x_49697850 v_x_49697850)))
  (ds_d27z : IList_u)
  (ds_d27z_p : IList_wf ds_d27z ∧ ∃ (llen_res : Z), llen_rel ds_d27z llen_res ∧ llen_res ≠ 0):
  applyToFirst_rel ⌊ f ⌋ ds_d27z ⌊ applyToFirst f (exist _ ds_d27z ds_d27z_p) -⌋.
Proof.
  Opaque applyToFirst.
  existence_lemma_pre applyToFirst;
  destruct ds_d27z as [x l'|];
  [fix_notations |];
  simpl in *.
  Transparent applyToFirst.
  all: (existence_lemma_quicksolve applyToFirst; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve applyToFirst_rel_ex: rel_ax_db.

#[global] Opaque applyToFirst.

Theorem applyToFirst__applyToFirst_rel_rw
  (f : @Pack
       ({lq_tmp0: Z | True} ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp0: Z | True}
  ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_49697850 : ArgList ({lq_tmp0: Z | True} ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT))
          (v_x_49697850 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {lq_tmp0: Z | True}) (y : Z), ltbZ_rel 5 y true) x_49697850 v_x_49697850)))
  (ds_d27z : IList_u)
  (ds_d27z_p : IList_wf ds_d27z ∧ ∃ (llen_res : Z), llen_rel ds_d27z llen_res ∧ llen_res ≠ 0)
  (v : Z):
  ⌊ applyToFirst f (exist _ ds_d27z ds_d27z_p) -⌋ = v ↔ applyToFirst_rel ⌊ f ⌋ ds_d27z v.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite applyToFirst__applyToFirst_rel_rw: f_rel_funct_db.

#[global] Hint Resolve applyToFirst__applyToFirst_rel_rw: rel_ax_db.

#[global] Instance applyToFirst_lookup_rw: dictionary rwLem applyToFirst := {
    lookup' := applyToFirst__applyToFirst_rel_rw }.

Theorem applyToFirst__applyToFirst_rel
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_44453395 : ArgList ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT))
          (v_x_44453395 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {VV: Z | True}) (y : Z), ltbZ_rel 5 y true) x_44453395 v_x_44453395)))
  (ds_d27z : {ds_d27z: IList_u | IList_wf ds_d27z
                                 ∧ ∃ (llen_res : Z), llen_rel ds_d27z llen_res ∧ llen_res ≠ 0})
  (v : Z):
  ⌊ applyToFirst f ds_d27z -⌋ = v ↔ applyToFirst_rel ⌊ f ⌋ ⌊ ds_d27z ⌋ v.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite applyToFirst__applyToFirst_rel: f_rel_funct_db.

Theorem applyToFirst__applyToFirst_rel'
  (f_u : @uPack (Z ::UT nilUT) Z)
  (ds_d27z_u : IList_u)
  (f : @Pack
       ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_44453395 : ArgList ({VV: Z | True} ::RT λ (lq_tmp0 : {VV: Z | True}), nilRT))
          (v_x_44453395 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {VV: Z | True}) (y : Z), ltbZ_rel 5 y true) x_44453395 v_x_44453395)))
  (ds_d27z : {ds_d27z: IList_u | IList_wf ds_d27z
                                 ∧ ∃ (llen_res : Z), llen_rel ds_d27z llen_res ∧ llen_res ≠ 0})
  (v : Z):
  f_u = ⌊ f ⌋
  → (ds_d27z_u = ⌊ ds_d27z ⌋ → ⌊ applyToFirst f ds_d27z -⌋ = v ↔ applyToFirst_rel f_u ds_d27z_u v).
Proof.
  intros -> ->. refine (applyToFirst__applyToFirst_rel f ds_d27z v).
Qed.

#[global] Hint Resolve applyToFirst__applyToFirst_rel': f_rel_funct_db.

Theorem applyToFirst_rel_mk
  (f : @Pack
       ({lq_tmp0: Z | True} ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT)
       (Z ::UT nilUT)
       ltac:(mkProjectsArgListTG (({lq_tmp0: Z | True}
  ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT)) ((Z ::UT nilUT)))
       Z
       (λ (x_49697850 : ArgList ({lq_tmp0: Z | True} ::RT λ (lq_tmp0 : {lq_tmp0: Z | True}), nilRT))
          (v_x_49697850 : Z),
        ltac:(flattenP (λ (lq_tmp0 : {lq_tmp0: Z | True}) (y : Z), ltbZ_rel 5 y true) x_49697850 v_x_49697850)))
  (ds_d27z : IList_u)
  (ds_d27z_p : IList_wf ds_d27z ∧ ∃ (llen_res : Z), llen_rel ds_d27z llen_res ∧ llen_res ≠ 0):
  {v: _ | applyToFirst_rel (packProj f) ds_d27z v}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ v, applyToFirst_rel (packProj f) ds_d27z v)
          (applyToFirst f (exist _ ds_d27z ds_d27z_p))
          _);
  rewrite <- applyToFirst__applyToFirst_rel';
  quicksolve.
Qed.

#[global] Hint Resolve applyToFirst_rel_mk: f_rel_funct_db.

Definition thm1_spec
  (ds_d27F : IList)
  (x : {x: Z | ltbZ_rel 5 x true})
  (ds_d27G : {ds_d27G: Z | lebZ_rel 0 ds_d27G true
                           ∧ ∃ (llen_res : Z), llen_rel ⌊ ds_d27F ⌋ llen_res ∧ ltbZ_rel ds_d27G llen_res true}):
  Type :=
  {{∃ (get_res : Z),
    get_rel ⌊ ds_d27F ⌋ ⌊ ds_d27G ⌋ get_res
    ∧ ∃ (addZ_res : Z),
      addZ_rel ⌊ ds_d27G ⌋ 1 addZ_res
      ∧ ∃ (get_res_2 : Z),
        get_rel (Cons_u ⌊ x ⌋ ⌊ ds_d27F ⌋) addZ_res get_res_2 ∧ get_res == get_res_2}}.

#[global] Hint Unfold thm1_spec: lia_unfold.

Theorem thm1
  (ds_d27F : IList)
  (x : {x: Z | ltbZ_rel 5 x true})
  (ds_d27G : {ds_d27G: Z | lebZ_rel 0 ds_d27G true
                           ∧ ∃ (llen_res : Z), llen_rel ⌊ ds_d27F ⌋ llen_res ∧ ltbZ_rel ds_d27G llen_res true}):
  thm1_spec ds_d27F x ds_d27G.
Proof.
  destruct ds_d27F as [ds_d27F ds_d27F_p].
  destruct x as [x x_p].
  destruct ds_d27G as [ds_d27G ds_d27G_p].
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (get_res : Z),
           get_rel ds_d27F ds_d27G get_res
           ∧ ∃ (addZ_res : Z),
             addZ_rel ds_d27G 1 addZ_res
             ∧ ∃ (get_res_2 : Z), get_rel (Cons_u x ds_d27F) addZ_res get_res_2 ∧ get_res == get_res_2)
          (# unit)
          ltac:(solver)).
Qed.

Definition thm2_spec
  (ds_d27M ds_d27N : IList)
  (ds_d27O : {ds_d27O: Z | lebZ_rel 0 ds_d27O true
                           ∧ ∃ (llen_res : Z), llen_rel ⌊ ds_d27M ⌋ llen_res ∧ ltbZ_rel ds_d27O llen_res true}):
  Type :=
  {{∃ (get_res : Z),
    get_rel ⌊ ds_d27M ⌋ ⌊ ds_d27O ⌋ get_res
    ∧ ∃ (llen_res : Z),
      llen_rel ⌊ ds_d27N ⌋ llen_res
      ∧ ∃ (addZ_res : Z),
        addZ_rel ⌊ ds_d27O ⌋ llen_res addZ_res
        ∧ ∃ (append_res : IList_u),
          append_rel ⌊ ds_d27N ⌋ ⌊ ds_d27M ⌋ append_res
          ∧ ∃ (get_res_2 : Z), get_rel append_res addZ_res get_res_2 ∧ get_res == get_res_2}}.

#[global] Hint Unfold thm2_spec: lia_unfold.

Theorem thm2
  (ds_d27M ds_d27N : IList)
  (ds_d27O : {ds_d27O: Z | lebZ_rel 0 ds_d27O true
                           ∧ ∃ (llen_res : Z), llen_rel ⌊ ds_d27M ⌋ llen_res ∧ ltbZ_rel ds_d27O llen_res true}):
  thm2_spec ds_d27M ds_d27N ds_d27O.
Proof.
  destruct ds_d27M as [ds_d27M ds_d27M_p].
  destruct ds_d27N as [ds_d27N ds_d27N_p].
  destruct ds_d27O as [ds_d27O ds_d27O_p].
  try revert ds_d27O_p; generalize dependent ds_d27O;
  try revert ds_d27M_p; generalize dependent ds_d27M;
  induction ds_d27N as [y ys IH_ys|];
  intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (get_res : Z),
             get_rel ds_d27M ds_d27O get_res
             ∧ ∃ (llen_res : Z),
               llen_rel (Cons_u y ys) llen_res
               ∧ ∃ (addZ_res : Z),
                 addZ_rel ds_d27O llen_res addZ_res
                 ∧ ∃ (append_res : IList_u),
                   append_rel (Cons_u y ys) ds_d27M append_res
                   ∧ ∃ (get_res_2 : Z), get_rel append_res addZ_res get_res_2 ∧ get_res == get_res_2)
            (let _: ∃ (get_res : Z),
                    get_rel
                    ⌊ append
                      (exist (λ (l : IList_u), IList_wf l ∧ True) ys ltac:(solver))
                      (exist (λ (ds_d27M : IList_u), IList_wf ds_d27M ∧ True) ds_d27M ltac:(solver)) ⌋
                    (ds_d27O + ⌊ llen (exist (λ (l : IList_u), IList_wf l ∧ True) ys ltac:(solver)) ⌋)
                    get_res
                    ∧ ∃ (addZ_res : Z),
                      addZ_rel
                      (ds_d27O + ⌊ llen (exist (λ (l : IList_u), IList_wf l ∧ True) ys ltac:(solver)) ⌋)
                      1
                      addZ_res
                      ∧ ∃ (get_res_2 : Z),
                        get_rel
                        (Cons_u y
                         ⌊ append
                           (exist (λ (l : IList_u), IList_wf l ∧ True) ys ltac:(solver))
                           (exist (λ (ds_d27M : IList_u), IList_wf ds_d27M ∧ True) ds_d27M ltac:(solver)) ⌋)
                        addZ_res
                        get_res_2
                        ∧ get_res == get_res_2 :=
             ⌈ thm1
               (subsumptionCast
                IList_u
                (λ (ds_d27F : IList_u), IList_wf ds_d27F ∧ True)
                (append
                 (exist (λ (l : IList_u), IList_wf l ∧ True) ys ltac:(solver))
                 (exist (λ (ds_d27M : IList_u), IList_wf ds_d27M ∧ True) ds_d27M ltac:(solver)))
                ltac:(solver))
               (exist (λ (n : Z), ltbZ_rel 5 n true) y ltac:(solver))
               (subsumptionCast
                Z
                (λ (ds_d27G : Z),
                 lebZ_rel 0 ds_d27G true
                 ∧ ∃ (llen_res : Z),
                   llen_rel
                   ⌊ append
                     (exist (λ (l : IList_u), IList_wf l ∧ True) ys ltac:(solver))
                     (exist (λ (ds_d27M : IList_u), IList_wf ds_d27M ∧ True) ds_d27M ltac:(solver)) ⌋
                   llen_res
                   ∧ ltbZ_rel ds_d27G llen_res true)
                (subsumptionCast
                 Z
                 (λ (x_1 : Z), True)
                 (exist (λ (ds_d27O : Z),
                         lebZ_rel 0 ds_d27O true
                         ∧ ∃ (llen_res : Z),
                           llen_rel ds_d27M llen_res ∧ ltbZ_rel ds_d27O llen_res true) ds_d27O ltac:(solver))
                 ltac:(solver)
                 +Z subsumptionCast
                    Z
                    (λ (x_2 : Z), True)
                    (llen (exist (λ (l : IList_u), IList_wf l ∧ True) ys ltac:(solver)))
                    ltac:(solver))
                ltac:(solver)) ⌉ in
             IH_ys
             ltac:(try clear IH_ys; solver)
             ds_d27M
             ltac:(try clear IH_ys; solver)
             ds_d27O
             ltac:(try clear IH_ys; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (get_res : Z),
             get_rel ds_d27M ds_d27O get_res
             ∧ ∃ (llen_res : Z),
               llen_rel Nil_u llen_res
               ∧ ∃ (addZ_res : Z),
                 addZ_rel ds_d27O llen_res addZ_res
                 ∧ ∃ (append_res : IList_u),
                   append_rel Nil_u ds_d27M append_res
                   ∧ ∃ (get_res_2 : Z), get_rel append_res addZ_res get_res_2 ∧ get_res == get_res_2)
            (# unit)
            ltac:(solver)).
Qed.
