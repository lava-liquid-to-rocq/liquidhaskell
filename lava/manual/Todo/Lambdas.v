From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Definition appId (x: {x: Z | True}): {VV: Z | True}. 
Proof. 
	destruct x as [x x_p].
	assert (f_def: (forall (y: {y: Z | True}) , {v: Z | v = (⌊ y -⌋)})).
  intros [y y_p]; refine (exist _ y _); solver.
  pose ltac:(fun_to_pack f_def) as f.

  assert (@Pack ({y:Z|True} ::RT (fun _ => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({y:Z|True} ::RT (fun _ => nilRT)) (Z ::UT nilUT))) Z
  (fun (y: (ArgList {y:Z|True} ::RT (fun _ => nilRT))) => (fun (v_x_86852483: Z) => (ltac: (flattenP (fun (_: Z) => True) y v_x_86852483))))).
	refine (subsumptionCast _ _ 
		((getPackF f) (exist (fun (y: Z) => True) x (ltac: (solver)))) _); 
	solver. 
Defined. 
Inductive Maybe_u : Set := 
	 | Nothing_u: Maybe_u. 
Fixpoint Maybe_eq (x: Maybe_u) (y: Maybe_u): bool := 
	match (x, y) with (Nothing_u, Nothing_u) => true end. 
Definition Maybe_eq_refl: (forall (x: Maybe_u) , is_true (Maybe_eq x x)). 
Proof. 
	eq_refl. 
Qed. 
#[global] Hint Resolve Maybe_eq_refl : eq_hint_db.
Definition Maybe_eqb_eq: (forall (s: Maybe_u) (t: Maybe_u) , (is_true (Maybe_eq s t)) -> (s = t)). 
Proof. 
	eqb_eq_lem. 
Qed. 
#[global] Hint Resolve Maybe_eqb_eq : eq_hint_db.
#[global] Instance leibnitz_eq_Maybe : LeibnitzEqB := { 
	equalB' := Maybe_eq;
	refl' := Maybe_eq_refl;
	eqb_eq' := Maybe_eqb_eq
}.
Fixpoint Maybe_wf (x: Maybe_u): Prop := 
	match x with Nothing_u => True end. 
Theorem Maybe_wf_ref [p: Maybe_u -> Prop] (tm: {v: Maybe_u | (Maybe_wf v) /\ (p v)}): Maybe_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation Maybe := {x: Maybe_u | (Maybe_wf x) /\ True}. 
Definition Nothing_lem: (Maybe_wf Nothing_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Nothing: Maybe := 
	exist _ Nothing_u Nothing_lem. 
#[global] Hint Resolve Maybe_wf_ref : wf_constr_db.
#[global] Hint Unfold Maybe_wf : wf_constr_db.
#[global] Hint Resolve Maybe_eq : ref_constr_db.
#[global] Hint Unfold Nothing : ref_constr_db.
