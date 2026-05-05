From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Set Universe Polymorphism.
Inductive Nats_u : Type := 
	 | Suc_u: Nats_u -> Nats_u
	 | Zero_u: Nats_u. 
Fixpoint Nats_eq (x: Nats_u) (y: Nats_u): bool := 
	match (x, y) with (Suc_u x, Suc_u x') => (true && (Nats_eq x x')) | (Zero_u, Zero_u) => true | (_, _) => false end. 
Theorem Nats_eq_refl: (forall (x: Nats_u) , is_true (Nats_eq x x)). 
Proof. 
	eq_refl_rec. 
Qed. 
#[global] Hint Resolve Nats_eq_refl : eq_hint_db.
Theorem Nats_eqb_eq: (forall (s: Nats_u) (t: Nats_u) , (is_true (Nats_eq s t)) -> (s = t)). 
Proof. 
	eqb_eq_lem. 
Qed. 
#[global] Hint Resolve Nats_eqb_eq : eq_hint_db.
#[global] Instance leibnitz_eq_Nats : LeibnitzEqB := { 
	equalB' := Nats_eq;
	refl' := Nats_eq_refl;
	eqb_eq' := Nats_eqb_eq
}.
Fixpoint Nats_wf (x: Nats_u): Prop := 
	match x with (Suc_u n) => ((Nats_wf n) /\ True) | Zero_u => True end. 
Theorem Nats_wf_ref [p: Nats_u -> Prop] (tm: {v: Nats_u | (Nats_wf v) /\ (p v)}): Nats_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation Nats := {x: Nats_u | (Nats_wf x) /\ True}. 
Definition Suc_lem (n: Nats): (Nats_wf (Suc_u (⌊ n -⌋))) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Suc (n: Nats): Nats := 
	exist _ (Suc_u (⌊ n -⌋)) (Suc_lem n). 
Definition Zero_lem: (Nats_wf Zero_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Zero: Nats := 
	exist _ Zero_u Zero_lem. 
Definition wf_Suc_n [n: Nats_u] (p: Nats_wf (Suc_u n)): Nats_wf n. 
Proof. 
	quicksolve. 
Defined. 
#[global] Hint Resolve Nats_wf_ref : wf_constr_db.
#[global] Hint Unfold Nats_wf : wf_constr_db.
#[global] Hint Resolve Nats_eq : ref_constr_db.
#[global] Hint Resolve wf_Suc_n : ref_constr_db.
#[global] Hint Unfold Suc : ref_constr_db.
#[global] Hint Unfold Zero : ref_constr_db.
Definition even_spec (n: Nats): Type := 
	Bool. 
#[global] Hint Unfold even_spec : lia_unfold.
Definition even (n: Nats): even_spec n. 
Proof. 
	destruct n as [n n_p]. 
	induction n as [(*Suc*) n IH_n | (*Zero*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ (negBool (IH_n (ltac: (try clear IH_n; 
	solver)))) _); 
		solver.  
	  - intros . 
		refine (exist _ true _); 
		solver.  
Defined. 
Inductive even_rel : (Nats_u -> (bool -> Prop)) := 
	 | even_Zero: even_rel Zero_u true
	 | even_Suc: (forall n , forall (evenres: bool), (even_rel n evenres) -> (even_rel (Suc_u n) (negb evenres))). 
#[global] Hint Constructors even_rel : core_hint_db.
#[global] Instance even_lookup_rel : dictionary rel even := { 
	lookup' := even_rel
}.
#[global] Instance even_getF : getFunc even_rel := { 
	getF' := even
}.
Theorem even_rel_funct [n: Nats_u]: (forall (VV: bool) (VV': bool) (H: even_rel n VV) (K: even_rel n VV') , VV = VV'). 
Proof. 
	induction n as [(*Suc*) n IH_n | (*Zero*) ]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve even_rel_funct : f_rel_funct_db.
Theorem even_Zero_lem: (even_rel Zero_u true) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite even_Zero_lem : f_rel_back.
Theorem even_Suc_lem (n: _) (res: bool): (even_rel (Suc_u n) res) <-> (exists (evenres: bool), (res = (negb evenres)) /\ (even_rel n evenres)). 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite even_Suc_lem : f_rel_back.
Theorem even_rel_ex (n: Nats_u) (n_p: (Nats_wf n) /\ True): even_rel n (⌊ even (exist _ n n_p) -⌋). 
Proof. 
	Opaque even.
	existence_lemma_pre even; 
	induction n as [(*Suc*) n IH_n | (*Zero*) ]; 
	intros ; 
	[fix_notations; 
	pose proof (IH_n (ltac: (try clear IH_n; 
	solver))) as IH_52571464; 
	try clear IH_n| 
	fix_notations]; 
	simpl in *. 
	Transparent even.
	all: existence_lemma_quicksolve even; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve even_rel_ex : rel_ax_db.
#[global] Opaque even. 
Theorem even__even_rel_rw (n: Nats_u) (n_p: (Nats_wf n) /\ True) (VV: bool): ((⌊ even (exist _ n n_p) -⌋) = VV) <-> (even_rel n VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite even__even_rel_rw : f_rel_funct_db.
#[global] Hint Resolve even__even_rel_rw : rel_ax_db.
#[global] Instance even_lookup_rw : dictionary rwLem even := { 
	lookup' := even__even_rel_rw
}.
Theorem even__even_rel (n_r: Nats) (VV: bool): ((⌊ even n_r -⌋) = VV) <-> (even_rel (⌊ n_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite even__even_rel : f_rel_funct_db.
Theorem even__even_rel' (n: Nats_u) (n_r: Nats) (VV: bool): (n = (⌊ n_r -⌋)) -> (((⌊ even n_r -⌋) = VV) <-> (even_rel n VV)). 
Proof. 
	intros ->. 
	refine (even__even_rel n_r VV). 
Qed. 
#[global] Hint Resolve even__even_rel' : f_rel_funct_db.
Theorem even_rel_mk [n: Nats_u] (n_p: (Nats_wf n) /\ True): {VV: _ | even_rel n VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (even_rel n VV)) (even (exist _ n n_p)) _); 
	rewrite <- even__even_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve even_rel_mk : f_rel_funct_db.
#[global] Instance evenPack : (@Pack (Nats ::RT (fun (n_r: Nats) => nilRT)) (Nats_u ::UT nilUT) (ltac: (mkProjectsArgListTG (Nats ::RT (fun (n_r: Nats) => nilRT)) (Nats_u ::UT nilUT))) bool (fun (x_13547772: (ArgList Nats ::RT (fun (n_r: Nats) => nilRT))) => (fun (v_x_13547772: bool) => (ltac: (flattenP (fun (n_r: Nats) => (fun (VV: bool) => True)) x_13547772 v_x_13547772))))).
Proof. 
	buildPackG even even_rel even__even_rel even_rel_funct. 
Defined.