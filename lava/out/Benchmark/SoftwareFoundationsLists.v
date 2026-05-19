

Load Benchmark.SoftwareFoundationsBasics.

Load Benchmark.SoftwareFoundationsInduction.

Inductive Natprod_u: Type :=
  | Pair_u: MyNat_u → MyNat_u → Natprod_u.

Fixpoint Natprod_eq (x y : Natprod_u): bool :=
  match (x, y) with | (Pair_u n1 n2, Pair_u n1' n2') => (true && (n1 ==? n1')) && (n2 ==? n2') end.

Theorem Natprod_eq_refl : ∀ (x : Natprod_u), is_true (Natprod_eq x x).
Proof.
  eq_refl_rec.
Qed.

#[global] Hint Resolve Natprod_eq_refl: eq_hint_db.

Theorem Natprod_eqb_eq : ∀ (s t : Natprod_u), is_true (Natprod_eq s t) → s = t.
Proof.
  eqb_eq_lem.
Qed.

#[global] Hint Resolve Natprod_eqb_eq: eq_hint_db.

#[global] Instance leibnitz_eq_Natprod: LeibnitzEqB := {
    equalB' := Natprod_eq;
    refl' := Natprod_eq_refl;
    eqb_eq' := Natprod_eqb_eq }.

Fixpoint Natprod_wf (x : Natprod_u): Prop :=
  match x with | Pair_u n1 n2 => (MyNat_wf n1 ∧ True) ∧ (MyNat_wf n2 ∧ True) end.

Theorem Natprod_wf_ref [p : Natprod_u → Prop] (tm : {v: Natprod_u | Natprod_wf v ∧ p v}):
  Natprod_wf ⌊ tm -⌋.
Proof.
  destruct tm as [tm tm_p]. solver.
Qed.

Global Notation Natprod := {x: Natprod_u | Natprod_wf x ∧ True}.

Definition Pair_lem (n1 n2 : MyNat): Natprod_wf (Pair_u ⌊ n1 ⌋ ⌊ n2 ⌋) ∧ True.
Proof.
  repeat first [split; solver].
Defined.

Definition Pair (n1 n2 : MyNat): Natprod :=
  exist _ (Pair_u ⌊ n1 ⌋ ⌊ n2 ⌋) (Pair_lem n1 n2).

Definition wf_Pair_n1 [n1 n2 : MyNat_u] (p : Natprod_wf (Pair_u n1 n2)): MyNat_wf n1.
Proof.
  quicksolve.
Defined.

#[global] Hint Resolve wf_Pair_n1: ref_constr_db.

Definition wf_Pair_n2 [n1 n2 : MyNat_u] (p : Natprod_wf (Pair_u n1 n2)): MyNat_wf n2.
Proof.
  quicksolve.
Defined.

#[global] Hint Resolve wf_Pair_n2: ref_constr_db.

#[global] Hint Resolve Natprod_wf_ref: wf_constr_db.

#[global] Hint Unfold Natprod_wf: wf_constr_db.

#[global] Hint Resolve Natprod_eq: ref_constr_db.

#[global] Hint Unfold Pair: ref_constr_db.

Definition fstSF_spec (ds_d9fR : Natprod): Type :=
  MyNat.

#[global] Hint Unfold fstSF_spec: lia_unfold.

Definition fstSF (ds_d9fR : Natprod): fstSF_spec ds_d9fR.
Proof.
  destruct ds_d9fR as [ds_d9fR ds_d9fR_p].
  destruct ds_d9fR as [n1 n2].
  - refine (exist (λ (n1 : MyNat_u), MyNat_wf n1 ∧ True) n1 ltac:(solver)).
Defined.

Inductive fstSF_rel: Natprod_u → MyNat_u → Prop :=
  | fstSF_Pair: ∀ n1 n2, fstSF_rel (Pair_u n1 n2) n1.

#[global] Hint Constructors fstSF_rel: core_hint_db.

#[global] Instance fstSF_lookup_rel: dictionary rel fstSF := { lookup' := fstSF_rel }.

#[global] Instance fstSF_getF: getFunc fstSF_rel := { getF' := fstSF }.

Theorem fstSF_rel_funct [ds_d9fR : Natprod_u]:
  ∀ (VV VV' : MyNat_u), fstSF_rel ds_d9fR VV → (fstSF_rel ds_d9fR VV' → VV = VV').
Proof.
  destruct ds_d9fR as [n1 n2]; rel_functionhood_body.
Qed.

#[global] Hint Resolve fstSF_rel_funct: f_rel_funct_db.

Theorem fstSF_Pair_lem n1 n2 fstSF_Pair_lem_res:
  fstSF_rel (Pair_u n1 n2) fstSF_Pair_lem_res ↔ fstSF_Pair_lem_res == n1.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite fstSF_Pair_lem: f_rel_back.

Theorem fstSF_rel_ex (ds_d9fR : Natprod_u) (ds_d9fR_p : Natprod_wf ds_d9fR ∧ True):
  fstSF_rel ds_d9fR ⌊ fstSF (exist _ ds_d9fR ds_d9fR_p) -⌋.
Proof.
  Opaque fstSF.
  existence_lemma_pre fstSF;
  destruct ds_d9fR as [n1 n2];
  [fix_notations];
  simpl in *.
  Transparent fstSF.
  all: (existence_lemma_quicksolve fstSF; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve fstSF_rel_ex: rel_ax_db.

#[global] Opaque fstSF.

Theorem fstSF__fstSF_rel_rw
  (ds_d9fR : Natprod_u) (ds_d9fR_p : Natprod_wf ds_d9fR ∧ True) (VV : MyNat_u):
  ⌊ fstSF (exist _ ds_d9fR ds_d9fR_p) -⌋ = VV ↔ fstSF_rel ds_d9fR VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite fstSF__fstSF_rel_rw: f_rel_funct_db.

#[global] Hint Resolve fstSF__fstSF_rel_rw: rel_ax_db.

#[global] Instance fstSF_lookup_rw: dictionary rwLem fstSF := { lookup' := fstSF__fstSF_rel_rw }.

Theorem fstSF__fstSF_rel (ds_d9fR : Natprod) (VV : MyNat_u):
  ⌊ fstSF ds_d9fR -⌋ = VV ↔ fstSF_rel ⌊ ds_d9fR ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite fstSF__fstSF_rel: f_rel_funct_db.

Theorem fstSF__fstSF_rel' (ds_d9fR_u : Natprod_u) (ds_d9fR : Natprod) (VV : MyNat_u):
  ds_d9fR_u = ⌊ ds_d9fR ⌋ → ⌊ fstSF ds_d9fR -⌋ = VV ↔ fstSF_rel ds_d9fR_u VV.
Proof.
  intros ->. refine (fstSF__fstSF_rel ds_d9fR VV).
Qed.

#[global] Hint Resolve fstSF__fstSF_rel': f_rel_funct_db.

Theorem fstSF_rel_mk (ds_d9fR : Natprod_u) (ds_d9fR_p : Natprod_wf ds_d9fR ∧ True):
  {VV: _ | fstSF_rel ds_d9fR VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, fstSF_rel ds_d9fR VV) (fstSF (exist _ ds_d9fR ds_d9fR_p)) _);
  rewrite <- fstSF__fstSF_rel';
  quicksolve.
Qed.

#[global] Hint Resolve fstSF_rel_mk: f_rel_funct_db.

#[global] Instance fstSF_pack:
  @Pack
  (Natprod ::RT λ (ds_d9fR : Natprod), nilRT)
  (Natprod_u ::UT nilUT)
  ltac:(mkProjectsArgListTG (Natprod ::RT λ (ds_d9fR : Natprod), nilRT) ((Natprod_u ::UT nilUT)))
  MyNat_u
  (λ (x_28056445 : ArgList (Natprod ::RT λ (ds_d9fR : Natprod), nilRT)) (v_x_28056445 : MyNat_u),
   ltac:(flattenP (λ (ds_d9fR : Natprod) (VV : MyNat_u), MyNat_wf VV ∧ True) x_28056445 v_x_28056445)).
Proof.
  buildPackG fstSF fstSF_rel fstSF__fstSF_rel fstSF_rel_funct.
Defined.

#[global] Instance fstSF_upack: @uPack (Natprod_u ::UT nilUT) MyNat_u.
Proof.
  buildUPackG fstSF_rel fstSF_rel_funct.
Defined.

Definition sndSF_spec (ds_d9fQ : Natprod): Type :=
  MyNat.

#[global] Hint Unfold sndSF_spec: lia_unfold.

Definition sndSF (ds_d9fQ : Natprod): sndSF_spec ds_d9fQ.
Proof.
  destruct ds_d9fQ as [ds_d9fQ ds_d9fQ_p].
  destruct ds_d9fQ as [n1 n2].
  - refine (exist (λ (n2 : MyNat_u), MyNat_wf n2 ∧ True) n2 ltac:(solver)).
Defined.

Inductive sndSF_rel: Natprod_u → MyNat_u → Prop :=
  | sndSF_Pair: ∀ n1 n2, sndSF_rel (Pair_u n1 n2) n2.

#[global] Hint Constructors sndSF_rel: core_hint_db.

#[global] Instance sndSF_lookup_rel: dictionary rel sndSF := { lookup' := sndSF_rel }.

#[global] Instance sndSF_getF: getFunc sndSF_rel := { getF' := sndSF }.

Theorem sndSF_rel_funct [ds_d9fQ : Natprod_u]:
  ∀ (VV VV' : MyNat_u), sndSF_rel ds_d9fQ VV → (sndSF_rel ds_d9fQ VV' → VV = VV').
Proof.
  destruct ds_d9fQ as [n1 n2]; rel_functionhood_body.
Qed.

#[global] Hint Resolve sndSF_rel_funct: f_rel_funct_db.

Theorem sndSF_Pair_lem n1 n2 sndSF_Pair_lem_res:
  sndSF_rel (Pair_u n1 n2) sndSF_Pair_lem_res ↔ sndSF_Pair_lem_res == n2.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite sndSF_Pair_lem: f_rel_back.

Theorem sndSF_rel_ex (ds_d9fQ : Natprod_u) (ds_d9fQ_p : Natprod_wf ds_d9fQ ∧ True):
  sndSF_rel ds_d9fQ ⌊ sndSF (exist _ ds_d9fQ ds_d9fQ_p) -⌋.
Proof.
  Opaque sndSF.
  existence_lemma_pre sndSF;
  destruct ds_d9fQ as [n1 n2];
  [fix_notations];
  simpl in *.
  Transparent sndSF.
  all: (existence_lemma_quicksolve sndSF; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve sndSF_rel_ex: rel_ax_db.

#[global] Opaque sndSF.

Theorem sndSF__sndSF_rel_rw
  (ds_d9fQ : Natprod_u) (ds_d9fQ_p : Natprod_wf ds_d9fQ ∧ True) (VV : MyNat_u):
  ⌊ sndSF (exist _ ds_d9fQ ds_d9fQ_p) -⌋ = VV ↔ sndSF_rel ds_d9fQ VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite sndSF__sndSF_rel_rw: f_rel_funct_db.

#[global] Hint Resolve sndSF__sndSF_rel_rw: rel_ax_db.

#[global] Instance sndSF_lookup_rw: dictionary rwLem sndSF := { lookup' := sndSF__sndSF_rel_rw }.

Theorem sndSF__sndSF_rel (ds_d9fQ : Natprod) (VV : MyNat_u):
  ⌊ sndSF ds_d9fQ -⌋ = VV ↔ sndSF_rel ⌊ ds_d9fQ ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite sndSF__sndSF_rel: f_rel_funct_db.

Theorem sndSF__sndSF_rel' (ds_d9fQ_u : Natprod_u) (ds_d9fQ : Natprod) (VV : MyNat_u):
  ds_d9fQ_u = ⌊ ds_d9fQ ⌋ → ⌊ sndSF ds_d9fQ -⌋ = VV ↔ sndSF_rel ds_d9fQ_u VV.
Proof.
  intros ->. refine (sndSF__sndSF_rel ds_d9fQ VV).
Qed.

#[global] Hint Resolve sndSF__sndSF_rel': f_rel_funct_db.

Theorem sndSF_rel_mk (ds_d9fQ : Natprod_u) (ds_d9fQ_p : Natprod_wf ds_d9fQ ∧ True):
  {VV: _ | sndSF_rel ds_d9fQ VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, sndSF_rel ds_d9fQ VV) (sndSF (exist _ ds_d9fQ ds_d9fQ_p)) _);
  rewrite <- sndSF__sndSF_rel';
  quicksolve.
Qed.

#[global] Hint Resolve sndSF_rel_mk: f_rel_funct_db.

#[global] Instance sndSF_pack:
  @Pack
  (Natprod ::RT λ (ds_d9fQ : Natprod), nilRT)
  (Natprod_u ::UT nilUT)
  ltac:(mkProjectsArgListTG (Natprod ::RT λ (ds_d9fQ : Natprod), nilRT) ((Natprod_u ::UT nilUT)))
  MyNat_u
  (λ (x_28203475 : ArgList (Natprod ::RT λ (ds_d9fQ : Natprod), nilRT)) (v_x_28203475 : MyNat_u),
   ltac:(flattenP (λ (ds_d9fQ : Natprod) (VV : MyNat_u), MyNat_wf VV ∧ True) x_28203475 v_x_28203475)).
Proof.
  buildPackG sndSF sndSF_rel sndSF__sndSF_rel sndSF_rel_funct.
Defined.

#[global] Instance sndSF_upack: @uPack (Natprod_u ::UT nilUT) MyNat_u.
Proof.
  buildUPackG sndSF_rel sndSF_rel_funct.
Defined.

Definition surjective_pairing'_spec (n m : MyNat): Type :=
  {{∃ (sndSF_res : MyNat_u),
    sndSF_rel (Pair_u ⌊ n ⌋ ⌊ m ⌋) sndSF_res
    ∧ ∃ (fstSF_res : MyNat_u),
      fstSF_rel (Pair_u ⌊ n ⌋ ⌊ m ⌋) fstSF_res ∧ Pair_u ⌊ n ⌋ ⌊ m ⌋ == Pair_u fstSF_res sndSF_res}}.

#[global] Hint Unfold surjective_pairing'_spec: lia_unfold.

Theorem surjective_pairing' (n m : MyNat): surjective_pairing'_spec n m.
Proof.
  destruct n as [n n_p].
  destruct m as [m m_p].
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∃ (sndSF_res : MyNat_u),
           sndSF_rel (Pair_u n m) sndSF_res
           ∧ ∃ (fstSF_res : MyNat_u),
             fstSF_rel (Pair_u n m) fstSF_res ∧ Pair_u n m == Pair_u fstSF_res sndSF_res)
          (# unit)
          ltac:(solver)).
Qed.

Definition surjective_pairing_spec (ds_d9fM : Natprod): Type :=
  {{∃ (sndSF_res : MyNat_u),
    sndSF_rel ⌊ ds_d9fM ⌋ sndSF_res
    ∧ ∃ (fstSF_res : MyNat_u),
      fstSF_rel ⌊ ds_d9fM ⌋ fstSF_res ∧ ⌊ ds_d9fM ⌋ == Pair_u fstSF_res sndSF_res}}.

#[global] Hint Unfold surjective_pairing_spec: lia_unfold.

Theorem surjective_pairing (ds_d9fM : Natprod): surjective_pairing_spec ds_d9fM.
Proof.
  destruct ds_d9fM as [ds_d9fM ds_d9fM_p].
  destruct ds_d9fM as [n m].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (sndSF_res : MyNat_u),
             sndSF_rel (Pair_u n m) sndSF_res
             ∧ ∃ (fstSF_res : MyNat_u),
               fstSF_rel (Pair_u n m) fstSF_res ∧ Pair_u n m == Pair_u fstSF_res sndSF_res)
            (# unit)
            ltac:(solver)).
Qed.

Definition swap_pair_spec (ds_d9fN : Natprod): Type :=
  Natprod.

#[global] Hint Unfold swap_pair_spec: lia_unfold.

Definition swap_pair (ds_d9fN : Natprod): swap_pair_spec ds_d9fN.
Proof.
  destruct ds_d9fN as [ds_d9fN ds_d9fN_p].
  destruct ds_d9fN as [x y].
  - refine (Pair
            (exist (λ (n2 : MyNat_u), MyNat_wf n2 ∧ True) y ltac:(solver))
            (exist (λ (n1 : MyNat_u), MyNat_wf n1 ∧ True) x ltac:(solver))).
Defined.

Inductive swap_pair_rel: Natprod_u → Natprod_u → Prop :=
  | swap_pair_Pair: ∀ x y, swap_pair_rel (Pair_u x y) (Pair_u y x).

#[global] Hint Constructors swap_pair_rel: core_hint_db.

#[global] Instance swap_pair_lookup_rel: dictionary rel swap_pair := { lookup' := swap_pair_rel }.

#[global] Instance swap_pair_getF: getFunc swap_pair_rel := { getF' := swap_pair }.

Theorem swap_pair_rel_funct [ds_d9fN : Natprod_u]:
  ∀ (VV VV' : Natprod_u), swap_pair_rel ds_d9fN VV → (swap_pair_rel ds_d9fN VV' → VV = VV').
Proof.
  destruct ds_d9fN as [x y]; rel_functionhood_body.
Qed.

#[global] Hint Resolve swap_pair_rel_funct: f_rel_funct_db.

Theorem swap_pair_Pair_lem x y swap_pair_Pair_lem_res:
  swap_pair_rel (Pair_u x y) swap_pair_Pair_lem_res ↔ swap_pair_Pair_lem_res == Pair_u y x.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite swap_pair_Pair_lem: f_rel_back.

Theorem swap_pair_rel_ex (ds_d9fN : Natprod_u) (ds_d9fN_p : Natprod_wf ds_d9fN ∧ True):
  swap_pair_rel ds_d9fN ⌊ swap_pair (exist _ ds_d9fN ds_d9fN_p) -⌋.
Proof.
  Opaque swap_pair.
  existence_lemma_pre swap_pair;
  destruct ds_d9fN as [x y];
  [fix_notations];
  simpl in *.
  Transparent swap_pair.
  all: (existence_lemma_quicksolve swap_pair; f__f_rel_ex_body; f_rel_finish).
Qed.

#[global] Hint Resolve swap_pair_rel_ex: rel_ax_db.

#[global] Opaque swap_pair.

Theorem swap_pair__swap_pair_rel_rw
  (ds_d9fN : Natprod_u) (ds_d9fN_p : Natprod_wf ds_d9fN ∧ True) (VV : Natprod_u):
  ⌊ swap_pair (exist _ ds_d9fN ds_d9fN_p) -⌋ = VV ↔ swap_pair_rel ds_d9fN VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite swap_pair__swap_pair_rel_rw: f_rel_funct_db.

#[global] Hint Resolve swap_pair__swap_pair_rel_rw: rel_ax_db.

#[global] Instance swap_pair_lookup_rw: dictionary rwLem swap_pair := {
    lookup' := swap_pair__swap_pair_rel_rw }.

Theorem swap_pair__swap_pair_rel (ds_d9fN : Natprod) (VV : Natprod_u):
  ⌊ swap_pair ds_d9fN -⌋ = VV ↔ swap_pair_rel ⌊ ds_d9fN ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite swap_pair__swap_pair_rel: f_rel_funct_db.

Theorem swap_pair__swap_pair_rel' (ds_d9fN_u : Natprod_u) (ds_d9fN : Natprod) (VV : Natprod_u):
  ds_d9fN_u = ⌊ ds_d9fN ⌋ → ⌊ swap_pair ds_d9fN -⌋ = VV ↔ swap_pair_rel ds_d9fN_u VV.
Proof.
  intros ->. refine (swap_pair__swap_pair_rel ds_d9fN VV).
Qed.

#[global] Hint Resolve swap_pair__swap_pair_rel': f_rel_funct_db.

Theorem swap_pair_rel_mk (ds_d9fN : Natprod_u) (ds_d9fN_p : Natprod_wf ds_d9fN ∧ True):
  {VV: _ | swap_pair_rel ds_d9fN VV}.
Proof.
  intros;
  refine (subsumptionCast
          _
          (λ VV, swap_pair_rel ds_d9fN VV)
          (swap_pair (exist _ ds_d9fN ds_d9fN_p))
          _);
  rewrite <- swap_pair__swap_pair_rel';
  quicksolve.
Qed.

#[global] Hint Resolve swap_pair_rel_mk: f_rel_funct_db.

#[global] Instance swap_pair_pack:
  @Pack
  (Natprod ::RT λ (ds_d9fN : Natprod), nilRT)
  (Natprod_u ::UT nilUT)
  ltac:(mkProjectsArgListTG (Natprod ::RT λ (ds_d9fN : Natprod), nilRT) ((Natprod_u ::UT nilUT)))
  Natprod_u
  (λ (x_41774634 : ArgList (Natprod ::RT λ (ds_d9fN : Natprod), nilRT)) (v_x_41774634 : Natprod_u),
   ltac:(flattenP (λ (ds_d9fN : Natprod) (VV : Natprod_u), Natprod_wf VV ∧ True) x_41774634 v_x_41774634)).
Proof.
  buildPackG swap_pair swap_pair_rel swap_pair__swap_pair_rel swap_pair_rel_funct.
Defined.

#[global] Instance swap_pair_upack: @uPack (Natprod_u ::UT nilUT) Natprod_u.
Proof.
  buildUPackG swap_pair_rel swap_pair_rel_funct.
Defined.
