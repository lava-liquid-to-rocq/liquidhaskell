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
  IList_wf (Cons_u ⌊ n -⌋ ⌊ l -⌋) ∧ True.
Proof.
  repeat first [split | solver].
Defined.

Definition Cons (n : {n: Z | ltbZ_rel 5 n true}) (l : IList): IList :=
  exist _ (Cons_u ⌊ n -⌋ ⌊ l -⌋) (Cons_lem n l).

Definition Nil_lem : IList_wf Nil_u ∧ True.
Proof.
  repeat first [split | solver].
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

Definition llen_spec (ds_d4Wr : IList): Type :=
  {v: Z | gebZ_rel v 0 true}.

#[global] Hint Unfold llen_spec: lia_unfold.

Definition llen (ds_d4Wr : IList): llen_spec ds_d4Wr.
Proof.
  destruct ds_d4Wr as [ds_d4Wr ds_d4Wr_p].
  induction ds_d4Wr as [ds_d4Ws l' IH_l'|].
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
  | llen_Cons: ∀ ds_d4Ws l' (llen_res : Z),
               llen_rel l' llen_res
               → ∀ (addZ_res : Z), addZ_rel llen_res 1 addZ_res → llen_rel (Cons_u ds_d4Ws l') addZ_res
  | llen_Nil: llen_rel Nil_u 0.

#[global] Hint Constructors llen_rel: core_hint_db.

#[global] Instance llen_lookup_rel: dictionary rel llen := { lookup' := llen_rel }.

#[global] Instance llen_getF: getFunc llen_rel := { getF' := llen }.

Theorem llen_rel_funct [ds_d4Wr : IList_u]:
  ∀ (v v' : Z), llen_rel ds_d4Wr v → (llen_rel ds_d4Wr v' → v = v').
Proof.
  induction ds_d4Wr as [ds_d4Ws l' IH_l'|]; rel_functionhood_body.
Qed.

#[global] Hint Resolve llen_rel_funct: f_rel_funct_db.

#[global] Instance llen_lookup_funct: dictionary functionhood llen := {
    lookup' := llen_rel_funct }.

Theorem llen_Cons_lem ds_d4Ws l' llen_Cons_lem_res:
  llen_rel (Cons_u ds_d4Ws l') llen_Cons_lem_res
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

Theorem llen_rel_ex (ds_d4Wr : IList_u) (ds_d4Wr_p : IList_wf ds_d4Wr ∧ True):
  llen_rel ds_d4Wr ⌊ llen (exist _ ds_d4Wr ds_d4Wr_p) -⌋.
Proof.
  Opaque llen.
  existence_lemma_pre llen;
  induction ds_d4Wr as [ds_d4Ws l' IH_l'|];
  [fix_notations; pose proof (IH_l' ltac:(try clear IH_l'; solver)) as IH_91252151; try clear IH_l' |
   fix_notations];
  simpl in *.
  Transparent llen.
  all: (existence_lemma_quicksolve llen; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve llen_rel_ex: rel_ax_db.

#[global] Opaque llen.

Theorem llen__llen_rel_rw (ds_d4Wr : IList_u) (ds_d4Wr_p : IList_wf ds_d4Wr ∧ True) (v : Z):
  ⌊ llen (exist _ ds_d4Wr ds_d4Wr_p) -⌋ = v ↔ llen_rel ds_d4Wr v.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite llen__llen_rel_rw: f_rel_funct_db.

#[global] Hint Resolve llen__llen_rel_rw: rel_ax_db.

#[global] Instance llen_lookup_rw: dictionary rwLem llen := { lookup' := llen__llen_rel_rw }.

Theorem llen__llen_rel (ds_d4Wr : IList) (v : Z): ⌊ llen ds_d4Wr -⌋ = v ↔ llen_rel ⌊ ds_d4Wr ⌋ v.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite llen__llen_rel: f_rel_funct_db.

Theorem llen__llen_rel' (ds_d4Wr_u : IList_u) (ds_d4Wr : IList) (v : Z):
  ds_d4Wr_u = ⌊ ds_d4Wr ⌋ → ⌊ llen ds_d4Wr -⌋ = v ↔ llen_rel ds_d4Wr_u v.
Proof.
  intros ->. refine (llen__llen_rel ds_d4Wr v).
Qed.

#[global] Hint Resolve llen__llen_rel': f_rel_funct_db.

Theorem llen_rel_mk (ds_d4Wr : IList_u) (ds_d4Wr_p : IList_wf ds_d4Wr ∧ True):
  {v: _ | llen_rel ds_d4Wr v}.
Proof.
  intros;
  refine (subsumptionCast _ (λ v, llen_rel ds_d4Wr v) (llen (exist _ ds_d4Wr ds_d4Wr_p)) _);
  rewrite <- llen__llen_rel';
  quicksolve.
Qed.

#[global] Hint Resolve llen_rel_mk: f_rel_funct_db.

#[global] Instance llen_pack:
  @Pack
  (IList ::RT λ (ds_d4Wr : IList), nilRT)
  (IList_u ::UT nilUT)
  ltac:(mkProjectsArgListTG (IList ::RT λ (ds_d4Wr : IList), nilRT) ((IList_u ::UT nilUT)))
  Z
  (λ (x_57559289 : ArgList (IList ::RT λ (ds_d4Wr : IList), nilRT)) (v_x_57559289 : Z),
   ltac:(flattenP (λ (ds_d4Wr : IList) (v : Z), gebZ_rel v 0 true) x_57559289 v_x_57559289)).
Proof.
  buildPackG llen llen_rel llen__llen_rel llen_rel_funct.
Defined.

#[global] Instance llen_upack: @uPack (IList_u ::UT nilUT) Z.
Proof.
  buildUPackG llen_rel llen_rel_funct.
Defined.

Definition append_spec (ds_d4Wj ys : IList): Type :=
  {v: IList_u | IList_wf v
                ∧ ∃ (llen_res : Z),
                  llen_rel v llen_res
                  ∧ ∃ (llen_res_2 : Z),
                    llen_rel ⌊ ds_d4Wj -⌋ llen_res_2
                    ∧ ∃ (llen_res_3 : Z),
                      llen_rel ⌊ ys -⌋ llen_res_3
                      ∧ ∃ (addZ_res : Z), addZ_rel llen_res_2 llen_res_3 addZ_res ∧ llen_res == addZ_res}.

#[global] Hint Unfold append_spec: lia_unfold.

Definition append (ds_d4Wj ys : IList): append_spec ds_d4Wj ys.
Proof.
  destruct ds_d4Wj as [ds_d4Wj ds_d4Wj_p].
  destruct ys as [ys ys_p].
  try revert ys_p; generalize dependent ys; induction ds_d4Wj as [x xs IH_xs|]; intros.
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

Theorem append_rel_funct [ds_d4Wj ys : IList_u]:
  ∀ (v v' : IList_u), append_rel ds_d4Wj ys v → (append_rel ds_d4Wj ys v' → v = v').
Proof.
  try revert ys_p; generalize dependent ys; induction ds_d4Wj as [x xs IH_xs|]; intros;
  rel_functionhood_body.
Qed.

#[global] Hint Resolve append_rel_funct: f_rel_funct_db.

#[global] Instance append_lookup_funct: dictionary functionhood append := {
    lookup' := append_rel_funct }.

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
  (ds_d4Wj : IList_u)
  (ds_d4Wj_p : IList_wf ds_d4Wj ∧ True)
  (ys : IList_u)
  (ys_p : IList_wf ys ∧ True):
  append_rel ds_d4Wj ys ⌊ append (exist _ ds_d4Wj ds_d4Wj_p) (exist _ ys ys_p) -⌋.
Proof.
  Opaque append.
  existence_lemma_pre append;
  try revert ys_p; generalize dependent ys; induction ds_d4Wj as [x xs IH_xs|]; intros;
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
  (ds_d4Wj : IList_u)
  (ds_d4Wj_p : IList_wf ds_d4Wj ∧ True)
  (ys : IList_u)
  (ys_p : IList_wf ys ∧ True)
  (v : IList_u):
  ⌊ append (exist _ ds_d4Wj ds_d4Wj_p) (exist _ ys ys_p) -⌋ = v ↔ append_rel ds_d4Wj ys v.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite append__append_rel_rw: f_rel_funct_db.

#[global] Hint Resolve append__append_rel_rw: rel_ax_db.

#[global] Instance append_lookup_rw: dictionary rwLem append := {
    lookup' := append__append_rel_rw }.

Theorem append__append_rel (ds_d4Wj ys : IList) (v : IList_u):
  ⌊ append ds_d4Wj ys -⌋ = v ↔ append_rel ⌊ ds_d4Wj ⌋ ⌊ ys ⌋ v.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite append__append_rel: f_rel_funct_db.

Theorem append__append_rel' (ds_d4Wj_u ys_u : IList_u) (ds_d4Wj ys : IList) (v : IList_u):
  ds_d4Wj_u = ⌊ ds_d4Wj ⌋
  → (ys_u = ⌊ ys ⌋ → ⌊ append ds_d4Wj ys -⌋ = v ↔ append_rel ds_d4Wj_u ys_u v).
Proof.
  intros -> ->. refine (append__append_rel ds_d4Wj ys v).
Qed.

#[global] Hint Resolve append__append_rel': f_rel_funct_db.

Theorem append_rel_mk
  (ds_d4Wj : IList_u)
  (ds_d4Wj_p : IList_wf ds_d4Wj ∧ True)
  (ys : IList_u)
  (ys_p : IList_wf ys ∧ True):
  {v: _ | append_rel ds_d4Wj ys v}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ v, append_rel ds_d4Wj ys v)
          (append (exist _ ds_d4Wj ds_d4Wj_p) (exist _ ys ys_p))
          _);
  rewrite <- append__append_rel';
  quicksolve.
Qed.

#[global] Hint Resolve append_rel_mk: f_rel_funct_db.

#[global] Instance append_pack:
  @Pack
  (IList ::RT λ (ds_d4Wj : IList), IList ::RT λ (ys : IList), nilRT)
  (IList_u ::UT (IList_u ::UT nilUT))
  ltac:(mkProjectsArgListTG (IList ::RT λ (ds_d4Wj : IList), IList ::RT λ (ys : IList), nilRT) ((IList_u ::UT (IList_u ::UT nilUT))))
  IList_u
  (λ (x_22985943 : ArgList (IList ::RT λ (ds_d4Wj : IList), IList ::RT λ (ys : IList), nilRT))
     (v_x_22985943 : IList_u),
   ltac:(flattenP (λ (ds_d4Wj ys : IList) (v : IList_u),
 IList_wf v
 ∧ ∃ (llen_res : Z),
   llen_rel v llen_res
   ∧ ∃ (llen_res_2 : Z),
     llen_rel ⌊ ds_d4Wj -⌋ llen_res_2
     ∧ ∃ (llen_res_3 : Z),
       llen_rel ⌊ ys -⌋ llen_res_3
       ∧ ∃ (addZ_res : Z),
         addZ_rel llen_res_2 llen_res_3 addZ_res ∧ llen_res == addZ_res) x_22985943 v_x_22985943)).
Proof.
  buildPackG append append_rel append__append_rel append_rel_funct.
Defined.

#[global] Instance append_upack: @uPack (IList_u ::UT (IList_u ::UT nilUT)) IList_u.
Proof.
  buildUPackG append_rel append_rel_funct.
Defined.

Definition get_spec
  (ds_d4Wo : IList)
  (i' : {i': Z | lebZ_rel 0 i' true
                 ∧ ∃ (llen_res : Z), llen_rel ⌊ ds_d4Wo -⌋ llen_res ∧ ltbZ_rel i' llen_res true}):
  Type :=
  {v: Z | ltbZ_rel 5 v true}.

#[global] Hint Unfold get_spec: lia_unfold.

Definition get
  (ds_d4Wo : IList)
  (i' : {i': Z | lebZ_rel 0 i' true
                 ∧ ∃ (llen_res : Z), llen_rel ⌊ ds_d4Wo -⌋ llen_res ∧ ltbZ_rel i' llen_res true}):
  get_spec ds_d4Wo i'.
Proof.
  destruct ds_d4Wo as [ds_d4Wo ds_d4Wo_p].
  destruct i' as [i' i'_p].
  try revert i'_p; generalize dependent i'; induction ds_d4Wo as [x xs' IH_xs'|]; intros.
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

Theorem get_rel_funct [ds_d4Wo : IList_u] [i' : Z]:
  ∀ (v v' : Z), get_rel ds_d4Wo i' v → (get_rel ds_d4Wo i' v' → v = v').
Proof.
  try revert i'_p; generalize dependent i'; induction ds_d4Wo as [x xs' IH_xs'|]; intros;
  [let E := fresh "E" in destruct (i' ==? 0) as [|] eqn:E |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve get_rel_funct: f_rel_funct_db.

#[global] Instance get_lookup_funct: dictionary functionhood get := { lookup' := get_rel_funct }.

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
  (ds_d4Wo : IList_u)
  (ds_d4Wo_p : IList_wf ds_d4Wo ∧ True)
  (i' : Z)
  (i'_p : lebZ_rel 0 i' true
          ∧ ∃ (llen_res : Z), llen_rel ds_d4Wo llen_res ∧ ltbZ_rel i' llen_res true):
  get_rel ds_d4Wo i' ⌊ get (exist _ ds_d4Wo ds_d4Wo_p) (exist _ i' i'_p) -⌋.
Proof.
  Opaque get.
  existence_lemma_pre get;
  try revert i'_p; generalize dependent i'; induction ds_d4Wo as [x xs' IH_xs'|]; intros;
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
  (ds_d4Wo : IList_u)
  (ds_d4Wo_p : IList_wf ds_d4Wo ∧ True)
  (i' : Z)
  (i'_p : lebZ_rel 0 i' true
          ∧ ∃ (llen_res : Z), llen_rel ds_d4Wo llen_res ∧ ltbZ_rel i' llen_res true)
  (v : Z):
  ⌊ get (exist _ ds_d4Wo ds_d4Wo_p) (exist _ i' i'_p) -⌋ = v ↔ get_rel ds_d4Wo i' v.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite get__get_rel_rw: f_rel_funct_db.

#[global] Hint Resolve get__get_rel_rw: rel_ax_db.

#[global] Instance get_lookup_rw: dictionary rwLem get := { lookup' := get__get_rel_rw }.

Theorem get__get_rel
  (ds_d4Wo : IList)
  (i' : {i': Z | lebZ_rel 0 i' true
                 ∧ ∃ (llen_res : Z), llen_rel ⌊ ds_d4Wo -⌋ llen_res ∧ ltbZ_rel i' llen_res true})
  (v : Z):
  ⌊ get ds_d4Wo i' -⌋ = v ↔ get_rel ⌊ ds_d4Wo ⌋ ⌊ i' ⌋ v.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite get__get_rel: f_rel_funct_db.

Theorem get__get_rel'
  (ds_d4Wo_u : IList_u)
  (i'_u : Z)
  (ds_d4Wo : IList)
  (i' : {i': Z | lebZ_rel 0 i' true
                 ∧ ∃ (llen_res : Z), llen_rel ⌊ ds_d4Wo -⌋ llen_res ∧ ltbZ_rel i' llen_res true})
  (v : Z):
  ds_d4Wo_u = ⌊ ds_d4Wo ⌋ → (i'_u = ⌊ i' ⌋ → ⌊ get ds_d4Wo i' -⌋ = v ↔ get_rel ds_d4Wo_u i'_u v).
Proof.
  intros -> ->. refine (get__get_rel ds_d4Wo i' v).
Qed.

#[global] Hint Resolve get__get_rel': f_rel_funct_db.

Theorem get_rel_mk
  (ds_d4Wo : IList_u)
  (ds_d4Wo_p : IList_wf ds_d4Wo ∧ True)
  (i' : Z)
  (i'_p : lebZ_rel 0 i' true
          ∧ ∃ (llen_res : Z), llen_rel ds_d4Wo llen_res ∧ ltbZ_rel i' llen_res true):
  {v: _ | get_rel ds_d4Wo i' v}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ v, get_rel ds_d4Wo i' v)
          (get (exist _ ds_d4Wo ds_d4Wo_p) (exist _ i' i'_p))
          _);
  rewrite <- get__get_rel';
  quicksolve.
Qed.

#[global] Hint Resolve get_rel_mk: f_rel_funct_db.

#[global] Instance get_pack:
  @Pack
  (IList
   ::RT λ (ds_d4Wo : IList),
        {i': Z | lebZ_rel 0 i' true
                 ∧ ∃ (llen_res : Z), llen_rel ⌊ ds_d4Wo -⌋ llen_res ∧ ltbZ_rel i' llen_res true}
        ::RT λ (i' : {i': Z | lebZ_rel 0 i' true
                              ∧ ∃ (llen_res : Z), llen_rel ⌊ ds_d4Wo -⌋ llen_res ∧ ltbZ_rel i' llen_res true}),
             nilRT)
  (IList_u ::UT (Z ::UT nilUT))
  ltac:(mkProjectsArgListTG (IList
 ::RT λ (ds_d4Wo : IList),
      {i': Z | lebZ_rel 0 i' true
               ∧ ∃ (llen_res : Z),
                 llen_rel ⌊ ds_d4Wo -⌋ llen_res ∧ ltbZ_rel i' llen_res true}
      ::RT λ (i' : {i': Z | lebZ_rel 0 i' true
                            ∧ ∃ (llen_res : Z),
                              llen_rel ⌊ ds_d4Wo -⌋ llen_res ∧ ltbZ_rel i' llen_res true}),
           nilRT) ((IList_u ::UT (Z ::UT nilUT))))
  Z
  (λ (x_84900930 : ArgList (IList
                            ::RT λ (ds_d4Wo : IList),
                                 {i': Z | lebZ_rel 0 i' true
                                          ∧ ∃ (llen_res : Z),
                                            llen_rel ⌊ ds_d4Wo -⌋ llen_res ∧ ltbZ_rel i' llen_res true}
                                 ::RT λ (i' : {i': Z | lebZ_rel 0 i' true
                                                       ∧ ∃ (llen_res : Z),
                                                         llen_rel ⌊ ds_d4Wo -⌋ llen_res ∧ ltbZ_rel i' llen_res true}),
                                      nilRT))
     (v_x_84900930 : Z),
   ltac:(flattenP (λ (ds_d4Wo : IList)
   (i' : {i': Z | lebZ_rel 0 i' true
                  ∧ ∃ (llen_res : Z),
                    llen_rel ⌊ ds_d4Wo -⌋ llen_res ∧ ltbZ_rel i' llen_res true})
   (v : Z),
 ltbZ_rel 5 v true) x_84900930 v_x_84900930)).
Proof.
  buildPackG get get_rel get__get_rel get_rel_funct.
Defined.

#[global] Instance get_upack: @uPack (IList_u ::UT (Z ::UT nilUT)) Z.
Proof.
  buildUPackG get_rel get_rel_funct.
Defined.

Definition thm1_spec
  (ds_d4Wm : IList)
  (x : {x: Z | ltbZ_rel 5 x true})
  (ds_d4Wn : {ds_d4Wn: Z | lebZ_rel 0 ds_d4Wn true
                           ∧ ∃ (llen_res : Z), llen_rel ⌊ ds_d4Wm -⌋ llen_res ∧ ltbZ_rel ds_d4Wn llen_res true}):
  Type :=
  {{∃ (get_res : Z),
    get_rel ⌊ ds_d4Wm -⌋ ⌊ ds_d4Wn -⌋ get_res
    ∧ ∃ (addZ_res : Z),
      addZ_rel ⌊ ds_d4Wn -⌋ 1 addZ_res
      ∧ ∃ (get_res_2 : Z),
        get_rel (Cons_u ⌊ x -⌋ ⌊ ds_d4Wm -⌋) addZ_res get_res_2 ∧ get_res == get_res_2}}.

#[global] Hint Unfold thm1_spec: lia_unfold.

Theorem thm1
  (ds_d4Wm : IList)
  (x : {x: Z | ltbZ_rel 5 x true})
  (ds_d4Wn : {ds_d4Wn: Z | lebZ_rel 0 ds_d4Wn true
                           ∧ ∃ (llen_res : Z), llen_rel ⌊ ds_d4Wm -⌋ llen_res ∧ ltbZ_rel ds_d4Wn llen_res true}):
  thm1_spec ds_d4Wm x ds_d4Wn.
Proof.
  destruct ds_d4Wm as [ds_d4Wm ds_d4Wm_p].
  destruct x as [x x_p].
  destruct ds_d4Wn as [ds_d4Wn ds_d4Wn_p].
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (get_res : Z),
           get_rel ds_d4Wm ds_d4Wn get_res
           ∧ ∃ (addZ_res : Z),
             addZ_rel ds_d4Wn 1 addZ_res
             ∧ ∃ (get_res_2 : Z), get_rel (Cons_u x ds_d4Wm) addZ_res get_res_2 ∧ get_res == get_res_2)
          (# unit)
          ltac:(solver)).
Qed.

Definition thm2_spec
  (ds_d4Wt ds_d4Wu : IList)
  (ds_d4Wv : {ds_d4Wv: Z | lebZ_rel 0 ds_d4Wv true
                           ∧ ∃ (llen_res : Z), llen_rel ⌊ ds_d4Wt -⌋ llen_res ∧ ltbZ_rel ds_d4Wv llen_res true}):
  Type :=
  {{∃ (get_res : Z),
    get_rel ⌊ ds_d4Wt -⌋ ⌊ ds_d4Wv -⌋ get_res
    ∧ ∃ (llen_res : Z),
      llen_rel ⌊ ds_d4Wu -⌋ llen_res
      ∧ ∃ (addZ_res : Z),
        addZ_rel ⌊ ds_d4Wv -⌋ llen_res addZ_res
        ∧ ∃ (append_res : IList_u),
          append_rel ⌊ ds_d4Wu -⌋ ⌊ ds_d4Wt -⌋ append_res
          ∧ ∃ (get_res_2 : Z), get_rel append_res addZ_res get_res_2 ∧ get_res == get_res_2}}.

#[global] Hint Unfold thm2_spec: lia_unfold.

Theorem thm2
  (ds_d4Wt ds_d4Wu : IList)
  (ds_d4Wv : {ds_d4Wv: Z | lebZ_rel 0 ds_d4Wv true
                           ∧ ∃ (llen_res : Z), llen_rel ⌊ ds_d4Wt -⌋ llen_res ∧ ltbZ_rel ds_d4Wv llen_res true}):
  thm2_spec ds_d4Wt ds_d4Wu ds_d4Wv.
Proof.
  destruct ds_d4Wt as [ds_d4Wt ds_d4Wt_p].
  destruct ds_d4Wu as [ds_d4Wu ds_d4Wu_p].
  destruct ds_d4Wv as [ds_d4Wv ds_d4Wv_p].
  try revert ds_d4Wv_p; generalize dependent ds_d4Wv;
  try revert ds_d4Wt_p; generalize dependent ds_d4Wt;
  induction ds_d4Wu as [y ys IH_ys|];
  intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (get_res : Z),
             get_rel ds_d4Wt ds_d4Wv get_res
             ∧ ∃ (llen_res : Z),
               llen_rel (Cons_u y ys) llen_res
               ∧ ∃ (addZ_res : Z),
                 addZ_rel ds_d4Wv llen_res addZ_res
                 ∧ ∃ (append_res : IList_u),
                   append_rel (Cons_u y ys) ds_d4Wt append_res
                   ∧ ∃ (get_res_2 : Z), get_rel append_res addZ_res get_res_2 ∧ get_res == get_res_2)
            (let _: ∃ (get_res : Z),
                    get_rel
                    ⌊ append
                      (exist (λ (l : IList_u), IList_wf l ∧ True) ys ltac:(solver))
                      (exist (λ (ds_d4Wt : IList_u), IList_wf ds_d4Wt ∧ True) ds_d4Wt ltac:(solver)) -⌋
                    (ds_d4Wv + ⌊ llen (exist (λ (l : IList_u), IList_wf l ∧ True) ys ltac:(solver)) -⌋)
                    get_res
                    ∧ ∃ (addZ_res : Z),
                      addZ_rel
                      (ds_d4Wv + ⌊ llen (exist (λ (l : IList_u), IList_wf l ∧ True) ys ltac:(solver)) -⌋)
                      1
                      addZ_res
                      ∧ ∃ (get_res_2 : Z),
                        get_rel
                        (Cons_u y
                         ⌊ append
                           (exist (λ (l : IList_u), IList_wf l ∧ True) ys ltac:(solver))
                           (exist (λ (ds_d4Wt : IList_u), IList_wf ds_d4Wt ∧ True) ds_d4Wt ltac:(solver)) -⌋)
                        addZ_res
                        get_res_2
                        ∧ get_res == get_res_2 :=
             ⌈ thm1
               (subsumptionCast
                IList_u
                (λ (ds_d4Wm : IList_u), IList_wf ds_d4Wm ∧ True)
                (append
                 (exist (λ (l : IList_u), IList_wf l ∧ True) ys ltac:(solver))
                 (exist (λ (ds_d4Wt : IList_u), IList_wf ds_d4Wt ∧ True) ds_d4Wt ltac:(solver)))
                ltac:(solver))
               (exist (λ (n : Z), ltbZ_rel 5 n true) y ltac:(solver))
               (subsumptionCast
                Z
                (λ (ds_d4Wn : Z),
                 lebZ_rel 0 ds_d4Wn true
                 ∧ ∃ (llen_res : Z),
                   llen_rel
                   ⌊ append
                     (exist (λ (l : IList_u), IList_wf l ∧ True) ys ltac:(solver))
                     (exist (λ (ds_d4Wt : IList_u), IList_wf ds_d4Wt ∧ True) ds_d4Wt ltac:(solver)) -⌋
                   llen_res
                   ∧ ltbZ_rel ds_d4Wn llen_res true)
                (subsumptionCast
                 Z
                 (λ (x_1 : Z), True)
                 (exist (λ (ds_d4Wv : Z),
                         lebZ_rel 0 ds_d4Wv true
                         ∧ ∃ (llen_res : Z),
                           llen_rel ds_d4Wt llen_res ∧ ltbZ_rel ds_d4Wv llen_res true) ds_d4Wv ltac:(solver))
                 ltac:(solver)
                 +Z subsumptionCast
                    Z
                    (λ (x_2 : Z), True)
                    (llen (exist (λ (l : IList_u), IList_wf l ∧ True) ys ltac:(solver)))
                    ltac:(solver))
                ltac:(solver)) ⌉ in
             IH_ys
             ltac:(try clear IH_ys; solver)
             ds_d4Wt
             ltac:(try clear IH_ys; solver)
             ds_d4Wv
             ltac:(try clear IH_ys; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (get_res : Z),
             get_rel ds_d4Wt ds_d4Wv get_res
             ∧ ∃ (llen_res : Z),
               llen_rel Nil_u llen_res
               ∧ ∃ (addZ_res : Z),
                 addZ_rel ds_d4Wv llen_res addZ_res
                 ∧ ∃ (append_res : IList_u),
                   append_rel Nil_u ds_d4Wt append_res
                   ∧ ∃ (get_res_2 : Z), get_rel append_res addZ_res get_res_2 ∧ get_res == get_res_2)
            (# unit)
            ltac:(solver)).
Qed.
