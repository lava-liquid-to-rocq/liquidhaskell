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
Definition add_spec (m: Nats) (n: Nats): Type := 
	Nats. 
#[global] Hint Unfold add_spec : lia_unfold.
Definition add (m: Nats) (n: Nats): add_spec m n. 
Proof. 
	destruct m as [m m_p]. 
	destruct n as [n n_p]. 
	try revert n_p; generalize dependent n; 
	induction m as [(*Suc*) m IH_m | (*Zero*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ 
		(Suc 
		(subsumptionCast Nats_u (fun (n: Nats_u) => ((Nats_wf n) /\ True)) 
		(IH_m (ltac: (try clear IH_m; 
	solver)) n (ltac: (try clear IH_m; 
	solver))) (ltac: (solver)))) _); 
		solver.  
	  - intros . 
		refine (exist _ n _); 
		solver.  
Defined. 
Inductive add_rel : (Nats_u -> (Nats_u -> (Nats_u -> Prop))) := 
	 | add_Zero: (forall n , add_rel Zero_u n n)
	 | add_Suc: (forall m n , forall (addres: Nats_u), (add_rel m n addres) -> (add_rel (Suc_u m) n (Suc_u addres))). 
#[global] Hint Constructors add_rel : core_hint_db.
#[global] Instance add_lookup_rel : dictionary rel add := { 
	lookup' := add_rel
}.
#[global] Instance add_getF : getFunc add_rel := { 
	getF' := add
}.
Theorem add_rel_funct [m: Nats_u] [n: Nats_u]: (forall (VV: Nats_u) (VV': Nats_u) (H: add_rel m n VV) (K: add_rel m n VV') , VV = VV'). 
Proof. 
	try revert n_p; generalize dependent n; 
	induction m as [(*Suc*) m IH_m | (*Zero*) ]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve add_rel_funct : f_rel_funct_db.
Theorem add_Zero_lem (n: _): (add_rel Zero_u n n) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite add_Zero_lem : f_rel_back.
Theorem add_Suc_lem (m: _) (n: _) (addres: Nats_u) (h_46743849: add_rel m n addres): (add_rel (Suc_u m) n (Suc_u addres)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite add_Suc_lem : f_rel_back.
Theorem add_rel_ex (m: Nats_u) (n: Nats_u) (m_p: (Nats_wf m) /\ True) (n_p: (Nats_wf n) /\ True): add_rel m n (⌊ add (exist _ m m_p) (exist _ n n_p) -⌋). 
Proof. 
	Opaque add.
	existence_lemma_pre add; 
	try revert n_p; generalize dependent n; 
	induction m as [(*Suc*) m IH_m | (*Zero*) ]; 
	intros ; 
	[fix_notations; 
	pose proof (IH_m (ltac: (try clear IH_m; 
	solver)) n (ltac: (try clear IH_m; 
	solver))) as IH_13828668; 
	try clear IH_m| 
	fix_notations]; 
	simpl in *. 
	Transparent add.
	all: existence_lemma_quicksolve add; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve add_rel_ex : rel_ax_db.
#[global] Opaque add. 
Theorem add__add_rel_rw (m: Nats_u) (n: Nats_u) (m_p: (Nats_wf m) /\ True) (n_p: (Nats_wf n) /\ True) (VV: Nats_u): ((⌊ add (exist _ m m_p) (exist _ n n_p) -⌋) = VV) <-> (add_rel m n VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite add__add_rel_rw : f_rel_funct_db.
#[global] Hint Resolve add__add_rel_rw : rel_ax_db.
#[global] Instance add_lookup_rw : dictionary rwLem add := { 
	lookup' := add__add_rel_rw
}.
Theorem add__add_rel (m_r: Nats) (n_r: Nats) (VV: Nats_u): ((⌊ add m_r n_r -⌋) = VV) <-> (add_rel (⌊ m_r -⌋) (⌊ n_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite add__add_rel : f_rel_funct_db.
Theorem add__add_rel' (m: Nats_u) (n: Nats_u) (m_r: Nats) (n_r: Nats) (VV: Nats_u): (m = (⌊ m_r -⌋)) -> ((n = (⌊ n_r -⌋)) -> (((⌊ add m_r n_r -⌋) = VV) <-> (add_rel m n VV))). 
Proof. 
	intros -> ->. 
	refine (add__add_rel m_r n_r VV). 
Qed. 
#[global] Hint Resolve add__add_rel' : f_rel_funct_db.
Theorem add_rel_mk [m: Nats_u] [n: Nats_u] (m_p: (Nats_wf m) /\ True) (n_p: (Nats_wf n) /\ True): {VV: _ | add_rel m n VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (add_rel m n VV)) (add (exist _ m m_p) (exist _ n n_p)) _); 
	rewrite <- add__add_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve add_rel_mk : f_rel_funct_db.
#[global] Instance addPack : (@Pack (Nats ::RT (fun (m_r: Nats) => (Nats ::RT (fun (n_r: Nats) => nilRT)))) (Nats_u ::UT (Nats_u ::UT nilUT)) (ltac: (mkProjectsArgListTG (Nats ::RT (fun (m_r: Nats) => (Nats ::RT (fun (n_r: Nats) => nilRT)))) (Nats_u ::UT (Nats_u ::UT nilUT)))) Nats_u (fun (x_44523598: (ArgList Nats ::RT (fun (m_r: Nats) => (Nats ::RT (fun (n_r: Nats) => nilRT))))) => (fun (v_x_44523598: Nats_u) => (ltac: (flattenP (fun (m_r: Nats) => (fun (n_r: Nats) => (fun (VV: Nats_u) => ((Nats_wf VV) /\ True)))) x_44523598 v_x_44523598))))).
Proof. 
	buildPackG add add_rel add__add_rel add_rel_funct. 
Defined.
Definition add'_spec (m: Nats) (n: Nats): Type := 
	{v: Nats_u | (Nats_wf v) /\ (forall (addres: Nats_u), (add_rel (⌊ m -⌋) (⌊ n -⌋) addres) -> (forall (add_res_2: Nats_u), (add_rel addres Zero_u add_res_2) -> (add_res_2 == v)))}. 
#[global] Hint Unfold add'_spec : lia_unfold.
Definition add' (m: Nats) (n: Nats): add'_spec m n. 
Proof. 
	destruct m as [m m_p]. 
	destruct n as [n n_p]. 
	refine (subsumptionCast _ _ 
		(add 
		(subsumptionCast Nats_u (fun (m: Nats_u) => ((Nats_wf m) /\ True)) 
		(add 
		(exist (fun (m: Nats_u) => ((Nats_wf m) /\ True)) m (ltac: (solver))) 
		(exist (fun (n: Nats_u) => ((Nats_wf n) /\ True)) n (ltac: (solver)))) (ltac: (solver))) 
		(subsumptionCast Nats_u (fun (n: Nats_u) => ((Nats_wf n) /\ True)) Zero (ltac: (solver)))) _); 
	solver. 
Defined. 
Definition add''_spec (m: Nats) (n: Nats): Type := 
	{v: Nats_u | (Nats_wf v) /\ (forall (addres: Nats_u), (add_rel (⌊ m -⌋) (⌊ n -⌋) addres) -> (addres == v))}. 
#[global] Hint Unfold add''_spec : lia_unfold.
Definition add'' (m: Nats) (n: Nats): add''_spec m n. 
Proof. 
	destruct m as [m m_p]. 
	destruct n as [n n_p]. 
	refine (subsumptionCast _ _ 
		(add 
		(exist (fun (m: Nats_u) => ((Nats_wf m) /\ True)) m (ltac: (solver))) 
		(exist (fun (n: Nats_u) => ((Nats_wf n) /\ True)) n (ltac: (solver)))) _); 
	solver. 
Defined. 
Definition add_assoc_spec (m: Nats) (n: Nats) (o: Nats): Type := 
	{{forall (addres: Nats_u), (add_rel (⌊ n -⌋) (⌊ o -⌋) addres) -> (forall (add_res_2: Nats_u), (add_rel (⌊ m -⌋) addres add_res_2) -> (forall (add_res_3: Nats_u), (add_rel (⌊ m -⌋) (⌊ n -⌋) add_res_3) -> (forall (add_res_4: Nats_u), (add_rel add_res_3 (⌊ o -⌋) add_res_4) -> (add_res_2 == add_res_4))))}}. 
#[global] Hint Unfold add_assoc_spec : lia_unfold.
Theorem add_assoc (m: Nats) (n: Nats) (o: Nats): add_assoc_spec m n o. 
Proof. 
	destruct m as [m m_p]. 
	destruct n as [n n_p]. 
	destruct o as [o o_p]. 
	try revert o_p; generalize dependent o; try revert n_p; generalize dependent n; 
	induction m as [(*Suc*) m IH_m | (*Zero*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ 
		(IH_m (ltac: (try clear IH_m; 
	solver)) n (ltac: (try clear IH_m; 
	solver)) o (ltac: (try clear IH_m; 
	solver))) _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
Qed. 
Definition add_suc_r_spec (m: Nats) (n: Nats): Type := 
	{{forall (addres: Nats_u), (add_rel (⌊ m -⌋) (⌊ n -⌋) addres) -> (forall (add_res_2: Nats_u), (add_rel (⌊ m -⌋) (Suc_u (⌊ n -⌋)) add_res_2) -> ((Suc_u addres) == add_res_2))}}. 
#[global] Hint Unfold add_suc_r_spec : lia_unfold.
Theorem add_suc_r (m: Nats) (n: Nats): add_suc_r_spec m n. 
Proof. 
	destruct m as [m m_p]. 
	destruct n as [n n_p]. 
	try revert n_p; generalize dependent n; 
	induction m as [(*Suc*) m IH_m | (*Zero*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ 
		(IH_m (ltac: (try clear IH_m; 
	solver)) n (ltac: (try clear IH_m; 
	solver))) _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
Qed. 
Definition add_zero_l_spec (n: Nats): Type := 
	{{forall (addres: Nats_u), (add_rel Zero_u (⌊ n -⌋) addres) -> (addres = (⌊ n -⌋))}}. 
#[global] Hint Unfold add_zero_l_spec : lia_unfold.
Theorem add_zero_l (n: Nats): add_zero_l_spec n. 
Proof. 
	destruct n as [n n_p]. 
	induction n as [(*Suc*) n IH_n | (*Zero*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ (IH_n (ltac: (try clear IH_n; 
	solver))) _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
Qed. 
Definition add_zero_l_test_spec: Type := 
	{{forall (addres: Nats_u), (add_rel Zero_u (Suc_u (Suc_u Zero_u)) addres) -> (addres == (Suc_u (Suc_u Zero_u)))}}. 
#[global] Hint Unfold add_zero_l_test_spec : lia_unfold.
Theorem add_zero_l_test: add_zero_l_test_spec. 
Proof. 
	refine (subsumptionCast _ _ 
		(add_zero_l 
		(subsumptionCast Nats_u (fun (n: Nats_u) => ((Nats_wf n) /\ True)) 
		(Suc 
		(subsumptionCast Nats_u (fun (n: Nats_u) => ((Nats_wf n) /\ True)) 
		(Suc 
		(subsumptionCast Nats_u (fun (n: Nats_u) => ((Nats_wf n) /\ True)) Zero (ltac: (solver)))) (ltac: (solver)))) (ltac: (solver)))) _); 
	solver. 
Qed. 
Definition add_zero_r_spec (n: Nats): Type := 
	{{forall (addres: Nats_u), (add_rel (⌊ n -⌋) Zero_u addres) -> (addres = (⌊ n -⌋))}}. 
#[global] Hint Unfold add_zero_r_spec : lia_unfold.
Theorem add_zero_r (n: Nats): add_zero_r_spec n. 
Proof. 
	destruct n as [n n_p]. 
	induction n as [(*Suc*) n IH_n | (*Zero*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ (IH_n (ltac: (try clear IH_n; 
	solver))) _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
Qed. 
Definition eqN_spec (m: Nats) (n: Nats): Type := 
	Bool. 
#[global] Hint Unfold eqN_spec : lia_unfold.
Definition eqN (m: Nats) (n: Nats): eqN_spec m n. 
Proof. 
	destruct m as [m m_p]. 
	destruct n as [n n_p]. 
	try revert n_p; generalize dependent n; 
	induction m as [(*Suc*) m IH_m | (*Zero*) ]. 
	  - intros . 
		induction n as [(*Suc*) n IH_n | (*Zero*) ]. 
		  -- intros . 
			refine (subsumptionCast _ _ 
		(IH_m (ltac: (try clear IH_m; 
	solver)) n (ltac: (try clear IH_m; 
	solver))) _); 
			solver.  
		  -- intros . 
			refine (exist _ false _); 
			solver.   
	  - intros . 
		induction n as [(*Suc*) lq_anf7205759403792810464 IH_lq_anf7205759403792810464 | (*Zero*) ]. 
		  -- intros . 
			refine (exist _ false _); 
			solver.  
		  -- intros . 
			refine (exist _ true _); 
			solver.   
Defined. 
Inductive eqN_rel : (Nats_u -> (Nats_u -> (bool -> Prop))) := 
	 | eqN_Zero_Zero: eqN_rel Zero_u Zero_u true
	 | eqN_Zero_Suc: (forall lq_anf7205759403792810464 , eqN_rel Zero_u (Suc_u lq_anf7205759403792810464) false)
	 | eqN_Suc_Zero: (forall m , eqN_rel (Suc_u m) Zero_u false)
	 | eqN_Suc_Suc: (forall m n , forall (eqNres: bool), (eqN_rel m n eqNres) -> (eqN_rel (Suc_u m) (Suc_u n) eqNres)). 
#[global] Hint Constructors eqN_rel : core_hint_db.
#[global] Instance eqN_lookup_rel : dictionary rel eqN := { 
	lookup' := eqN_rel
}.
#[global] Instance eqN_getF : getFunc eqN_rel := { 
	getF' := eqN
}.
Theorem eqN_rel_funct [m: Nats_u] [n: Nats_u]: (forall (VV: bool) (VV': bool) (H: eqN_rel m n VV) (K: eqN_rel m n VV') , VV = VV'). 
Proof. 
	try revert n_p; generalize dependent n; 
	induction m as [(*Suc*) m IH_m | (*Zero*) ]; 
	intros ; 
	[induction n as [(*Suc*) n IH_n | (*Zero*) ]; 
	intros | 
	induction n as [(*Suc*) lq_anf7205759403792810464 IH_lq_anf7205759403792810464 | (*Zero*) ]; 
	intros ]; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve eqN_rel_funct : f_rel_funct_db.
Theorem eqN_Zero_Zero_lem: (eqN_rel Zero_u Zero_u true) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite eqN_Zero_Zero_lem : f_rel_back.
Theorem eqN_Zero_Suc_lem (lq_anf7205759403792810464: _): (eqN_rel Zero_u (Suc_u lq_anf7205759403792810464) false) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite eqN_Zero_Suc_lem : f_rel_back.
Theorem eqN_Suc_Zero_lem (m: _): (eqN_rel (Suc_u m) Zero_u false) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite eqN_Suc_Zero_lem : f_rel_back.
Theorem eqN_Suc_Suc_lem (m: _) (n: _) (eqNres: bool) (h_79216627: eqN_rel m n eqNres): (eqN_rel (Suc_u m) (Suc_u n) eqNres) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite eqN_Suc_Suc_lem : f_rel_back.
Theorem eqN_rel_ex (m: Nats_u) (n: Nats_u) (m_p: (Nats_wf m) /\ True) (n_p: (Nats_wf n) /\ True): eqN_rel m n (⌊ eqN (exist _ m m_p) (exist _ n n_p) -⌋). 
Proof. 
	Opaque eqN.
	existence_lemma_pre eqN; 
	try revert n_p; generalize dependent n; 
	induction m as [(*Suc*) m IH_m | (*Zero*) ]; 
	intros ; 
	[induction n as [(*Suc*) n IH_n | (*Zero*) ]; 
	intros ; 
	[fix_notations; 
	pose proof (IH_m (ltac: (try clear IH_m; 
	solver)) n (ltac: (try clear IH_m; 
	solver))) as IH_13828668; 
	try clear IH_m; 
	try clear IH_n| 
	fix_notations; 
	try clear IH_m]| 
	induction n as [(*Suc*) lq_anf7205759403792810464 IH_lq_anf7205759403792810464 | (*Zero*) ]; 
	intros ; 
	[fix_notations; 
	try clear IH_lq_anf7205759403792810464| 
	fix_notations]]; 
	simpl in *. 
	Transparent eqN.
	all: existence_lemma_quicksolve eqN; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve eqN_rel_ex : rel_ax_db.
#[global] Opaque eqN. 
Theorem eqN__eqN_rel_rw (m: Nats_u) (n: Nats_u) (m_p: (Nats_wf m) /\ True) (n_p: (Nats_wf n) /\ True) (VV: bool): ((⌊ eqN (exist _ m m_p) (exist _ n n_p) -⌋) = VV) <-> (eqN_rel m n VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite eqN__eqN_rel_rw : f_rel_funct_db.
#[global] Hint Resolve eqN__eqN_rel_rw : rel_ax_db.
#[global] Instance eqN_lookup_rw : dictionary rwLem eqN := { 
	lookup' := eqN__eqN_rel_rw
}.
Theorem eqN__eqN_rel (m_r: Nats) (n_r: Nats) (VV: bool): ((⌊ eqN m_r n_r -⌋) = VV) <-> (eqN_rel (⌊ m_r -⌋) (⌊ n_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite eqN__eqN_rel : f_rel_funct_db.
Theorem eqN__eqN_rel' (m: Nats_u) (n: Nats_u) (m_r: Nats) (n_r: Nats) (VV: bool): (m = (⌊ m_r -⌋)) -> ((n = (⌊ n_r -⌋)) -> (((⌊ eqN m_r n_r -⌋) = VV) <-> (eqN_rel m n VV))). 
Proof. 
	intros -> ->. 
	refine (eqN__eqN_rel m_r n_r VV). 
Qed. 
#[global] Hint Resolve eqN__eqN_rel' : f_rel_funct_db.
Theorem eqN_rel_mk [m: Nats_u] [n: Nats_u] (m_p: (Nats_wf m) /\ True) (n_p: (Nats_wf n) /\ True): {VV: _ | eqN_rel m n VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (eqN_rel m n VV)) (eqN (exist _ m m_p) (exist _ n n_p)) _); 
	rewrite <- eqN__eqN_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve eqN_rel_mk : f_rel_funct_db.
#[global] Instance eqNPack : (@Pack (Nats ::RT (fun (m_r: Nats) => (Nats ::RT (fun (n_r: Nats) => nilRT)))) (Nats_u ::UT (Nats_u ::UT nilUT)) (ltac: (mkProjectsArgListTG (Nats ::RT (fun (m_r: Nats) => (Nats ::RT (fun (n_r: Nats) => nilRT)))) (Nats_u ::UT (Nats_u ::UT nilUT)))) bool (fun (x_44523598: (ArgList Nats ::RT (fun (m_r: Nats) => (Nats ::RT (fun (n_r: Nats) => nilRT))))) => (fun (v_x_44523598: bool) => (ltac: (flattenP (fun (m_r: Nats) => (fun (n_r: Nats) => (fun (VV: bool) => True))) x_44523598 v_x_44523598))))).
Proof. 
	buildPackG eqN eqN_rel eqN__eqN_rel eqN_rel_funct. 
Defined.
Definition test_eqN_spec: Type := 
	{r: bool | is_true r}. 
#[global] Hint Unfold test_eqN_spec : lia_unfold.
Definition test_eqN: test_eqN_spec. 
Proof. 
	refine (subsumptionCast _ _ 
		(eqN 
		(subsumptionCast Nats_u (fun (m: Nats_u) => ((Nats_wf m) /\ True)) 
		(Suc 
		(subsumptionCast Nats_u (fun (n: Nats_u) => ((Nats_wf n) /\ True)) 
		(Suc 
		(subsumptionCast Nats_u (fun (n: Nats_u) => ((Nats_wf n) /\ True)) 
		(Suc 
		(subsumptionCast Nats_u (fun (n: Nats_u) => ((Nats_wf n) /\ True)) Zero (ltac: (solver)))) (ltac: (solver)))) (ltac: (solver)))) (ltac: (solver))) 
		(subsumptionCast Nats_u (fun (n: Nats_u) => ((Nats_wf n) /\ True)) 
		(Suc 
		(subsumptionCast Nats_u (fun (n: Nats_u) => ((Nats_wf n) /\ True)) 
		(Suc 
		(subsumptionCast Nats_u (fun (n: Nats_u) => ((Nats_wf n) /\ True)) 
		(Suc 
		(subsumptionCast Nats_u (fun (n: Nats_u) => ((Nats_wf n) /\ True)) Zero (ltac: (solver)))) (ltac: (solver)))) (ltac: (solver)))) (ltac: (solver)))) _); 
	solver. 
Defined. 
Definition test_eqN'_spec: Type := 
	{r: bool | not (is_true r)}. 
#[global] Hint Unfold test_eqN'_spec : lia_unfold.
Definition test_eqN': test_eqN'_spec. 
Proof. 
	refine (subsumptionCast _ _ 
		(eqN 
		(subsumptionCast Nats_u (fun (m: Nats_u) => ((Nats_wf m) /\ True)) 
		(Suc 
		(subsumptionCast Nats_u (fun (n: Nats_u) => ((Nats_wf n) /\ True)) 
		(Suc 
		(subsumptionCast Nats_u (fun (n: Nats_u) => ((Nats_wf n) /\ True)) Zero (ltac: (solver)))) (ltac: (solver)))) (ltac: (solver))) 
		(subsumptionCast Nats_u (fun (n: Nats_u) => ((Nats_wf n) /\ True)) 
		(Suc 
		(subsumptionCast Nats_u (fun (n: Nats_u) => ((Nats_wf n) /\ True)) Zero (ltac: (solver)))) (ltac: (solver)))) _); 
	solver. 
Defined. 
Definition geqN_spec (m: Nats) (n: Nats): Type := 
	Bool. 
#[global] Hint Unfold geqN_spec : lia_unfold.
Definition geqN (m: Nats) (n: Nats): geqN_spec m n. 
Proof. 
	destruct m as [m m_p]. 
	destruct n as [n n_p]. 
	try revert m_p; generalize dependent m; 
	induction n as [(*Suc*) n IH_n | (*Zero*) ]. 
	  - intros . 
		induction m as [(*Suc*) m IH_m | (*Zero*) ]. 
		  -- intros . 
			refine (subsumptionCast _ _ 
		(IH_n (ltac: (try clear IH_n; 
	solver)) m (ltac: (try clear IH_n; 
	solver))) _); 
			solver.  
		  -- intros . 
			refine (exist _ false _); 
			solver.   
	  - intros . 
		refine (exist _ true _); 
		solver.  
Defined. 
Inductive geqN_rel : (Nats_u -> (Nats_u -> (bool -> Prop))) := 
	 | geqN_Zero: (forall m , geqN_rel m Zero_u true)
	 | geqN_Zero_Suc: (forall n , geqN_rel Zero_u (Suc_u n) false)
	 | geqN_Suc_Suc: (forall m n , forall (geqNres: bool), (geqN_rel m n geqNres) -> (geqN_rel (Suc_u m) (Suc_u n) geqNres)). 
#[global] Hint Constructors geqN_rel : core_hint_db.
#[global] Instance geqN_lookup_rel : dictionary rel geqN := { 
	lookup' := geqN_rel
}.
#[global] Instance geqN_getF : getFunc geqN_rel := { 
	getF' := geqN
}.
Theorem geqN_rel_funct [m: Nats_u] [n: Nats_u]: (forall (VV: bool) (VV': bool) (H: geqN_rel m n VV) (K: geqN_rel m n VV') , VV = VV'). 
Proof. 
	try revert m_p; generalize dependent m; 
	induction n as [(*Suc*) n IH_n | (*Zero*) ]; 
	intros ; 
	[induction m as [(*Suc*) m IH_m | (*Zero*) ]; 
	intros | 
	]; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve geqN_rel_funct : f_rel_funct_db.
Theorem geqN_Zero_lem (m: _): (geqN_rel m Zero_u true) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite geqN_Zero_lem : f_rel_back.
Theorem geqN_Zero_Suc_lem (n: _): (geqN_rel Zero_u (Suc_u n) false) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite geqN_Zero_Suc_lem : f_rel_back.
Theorem geqN_Suc_Suc_lem (m: _) (n: _) (geqNres: bool) (h_23538365: geqN_rel m n geqNres): (geqN_rel (Suc_u m) (Suc_u n) geqNres) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite geqN_Suc_Suc_lem : f_rel_back.
Theorem geqN_rel_ex (m: Nats_u) (n: Nats_u) (m_p: (Nats_wf m) /\ True) (n_p: (Nats_wf n) /\ True): geqN_rel m n (⌊ geqN (exist _ m m_p) (exist _ n n_p) -⌋). 
Proof. 
	Opaque geqN.
	existence_lemma_pre geqN; 
	try revert m_p; generalize dependent m; 
	induction n as [(*Suc*) n IH_n | (*Zero*) ]; 
	intros ; 
	[induction m as [(*Suc*) m IH_m | (*Zero*) ]; 
	intros ; 
	[fix_notations; 
	pose proof (IH_n (ltac: (try clear IH_n; 
	solver)) m (ltac: (try clear IH_n; 
	solver))) as IH_64866221; 
	try clear IH_n; 
	try clear IH_m| 
	fix_notations; 
	try clear IH_n]| 
	fix_notations]; 
	simpl in *. 
	Transparent geqN.
	all: existence_lemma_quicksolve geqN; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve geqN_rel_ex : rel_ax_db.
#[global] Opaque geqN. 
Theorem geqN__geqN_rel_rw (m: Nats_u) (n: Nats_u) (m_p: (Nats_wf m) /\ True) (n_p: (Nats_wf n) /\ True) (VV: bool): ((⌊ geqN (exist _ m m_p) (exist _ n n_p) -⌋) = VV) <-> (geqN_rel m n VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite geqN__geqN_rel_rw : f_rel_funct_db.
#[global] Hint Resolve geqN__geqN_rel_rw : rel_ax_db.
#[global] Instance geqN_lookup_rw : dictionary rwLem geqN := { 
	lookup' := geqN__geqN_rel_rw
}.
Theorem geqN__geqN_rel (m_r: Nats) (n_r: Nats) (VV: bool): ((⌊ geqN m_r n_r -⌋) = VV) <-> (geqN_rel (⌊ m_r -⌋) (⌊ n_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite geqN__geqN_rel : f_rel_funct_db.
Theorem geqN__geqN_rel' (m: Nats_u) (n: Nats_u) (m_r: Nats) (n_r: Nats) (VV: bool): (m = (⌊ m_r -⌋)) -> ((n = (⌊ n_r -⌋)) -> (((⌊ geqN m_r n_r -⌋) = VV) <-> (geqN_rel m n VV))). 
Proof. 
	intros -> ->. 
	refine (geqN__geqN_rel m_r n_r VV). 
Qed. 
#[global] Hint Resolve geqN__geqN_rel' : f_rel_funct_db.
Theorem geqN_rel_mk [m: Nats_u] [n: Nats_u] (m_p: (Nats_wf m) /\ True) (n_p: (Nats_wf n) /\ True): {VV: _ | geqN_rel m n VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (geqN_rel m n VV)) (geqN (exist _ m m_p) (exist _ n n_p)) _); 
	rewrite <- geqN__geqN_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve geqN_rel_mk : f_rel_funct_db.
#[global] Instance geqNPack : (@Pack (Nats ::RT (fun (m_r: Nats) => (Nats ::RT (fun (n_r: Nats) => nilRT)))) (Nats_u ::UT (Nats_u ::UT nilUT)) (ltac: (mkProjectsArgListTG (Nats ::RT (fun (m_r: Nats) => (Nats ::RT (fun (n_r: Nats) => nilRT)))) (Nats_u ::UT (Nats_u ::UT nilUT)))) bool (fun (x_44523598: (ArgList Nats ::RT (fun (m_r: Nats) => (Nats ::RT (fun (n_r: Nats) => nilRT))))) => (fun (v_x_44523598: bool) => (ltac: (flattenP (fun (m_r: Nats) => (fun (n_r: Nats) => (fun (VV: bool) => True))) x_44523598 v_x_44523598))))).
Proof. 
	buildPackG geqN geqN_rel geqN__geqN_rel geqN_rel_funct. 
Defined.
Definition PeanoNats__sub_spec (m: Nats) (n: {n: Nats_u | (Nats_wf n) /\ (geqN_rel (⌊ m -⌋) n true)}): Type := 
	{o: Nats_u | (Nats_wf o) /\ ((o <> Zero_u) <-> ((⌊ m -⌋) <> (⌊ n -⌋)))}. 
#[global] Hint Unfold PeanoNats__sub_spec : lia_unfold.
Definition PeanoNats__sub (m: Nats) (n: {n: Nats_u | (Nats_wf n) /\ (geqN_rel (⌊ m -⌋) n true)}): PeanoNats__sub_spec m n. 
Proof. 
	destruct m as [m m_p]. 
	destruct n as [n n_p]. 
	try revert n_p; generalize dependent n; 
	induction m as [(*Suc*) m IH_m | (*Zero*) ]. 
	  - intros . 
		induction n as [(*Suc*) n IH_n | (*Zero*) ]. 
		  -- intros . 
			refine (subsumptionCast _ _ 
		(IH_m (ltac: (try clear IH_m; 
	solver)) n (ltac: (try clear IH_m; 
	solver))) _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ 
		(Suc 
		(exist (fun (n: Nats_u) => ((Nats_wf n) /\ True)) m (ltac: (solver)))) _); 
			solver.   
	  - intros . 
		induction n as [(*Suc*) lq_anf7205759403792810480 IH_lq_anf7205759403792810480 | (*Zero*) ]. 
		  -- intros . 
			intros ; 
			exfalso; 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Zero _); 
			solver.   
Defined. 
Inductive PeanoNats__sub_rel : (Nats_u -> (Nats_u -> (Nats_u -> Prop))) := 
	 | PeanoNats__sub_Zero_Zero: PeanoNats__sub_rel Zero_u Zero_u Zero_u
	 | PeanoNats__sub_Suc_Zero: (forall m , PeanoNats__sub_rel (Suc_u m) Zero_u (Suc_u m))
	 | PeanoNats__sub_Suc_Suc: (forall m n , forall (PeanoNats__subres: Nats_u), (PeanoNats__sub_rel m n PeanoNats__subres) -> (PeanoNats__sub_rel (Suc_u m) (Suc_u n) PeanoNats__subres)). 
#[global] Hint Constructors PeanoNats__sub_rel : core_hint_db.
#[global] Instance PeanoNats__sub_lookup_rel : dictionary rel PeanoNats__sub := { 
	lookup' := PeanoNats__sub_rel
}.
#[global] Instance PeanoNats__sub_getF : getFunc PeanoNats__sub_rel := { 
	getF' := PeanoNats__sub
}.
Theorem PeanoNats__sub_rel_funct [m: Nats_u] [n: Nats_u]: (forall (o: Nats_u) (o': Nats_u) (H: PeanoNats__sub_rel m n o) (K: PeanoNats__sub_rel m n o') , o = o'). 
Proof. 
	try revert n_p; generalize dependent n; 
	induction m as [(*Suc*) m IH_m | (*Zero*) ]; 
	intros ; 
	[induction n as [(*Suc*) n IH_n | (*Zero*) ]; 
	intros | 
	induction n as [(*Suc*) lq_anf7205759403792810480 IH_lq_anf7205759403792810480 | (*Zero*) ]; 
	intros ]; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve PeanoNats__sub_rel_funct : f_rel_funct_db.
Theorem PeanoNats__sub_Zero_Zero_lem: (PeanoNats__sub_rel Zero_u Zero_u Zero_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite PeanoNats__sub_Zero_Zero_lem : f_rel_back.
Theorem PeanoNats__sub_Suc_Zero_lem (m: _): (PeanoNats__sub_rel (Suc_u m) Zero_u (Suc_u m)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite PeanoNats__sub_Suc_Zero_lem : f_rel_back.
Theorem PeanoNats__sub_Suc_Suc_lem (m: _) (n: _) (PeanoNats__subres: Nats_u) (h_75241776: PeanoNats__sub_rel m n PeanoNats__subres): (PeanoNats__sub_rel (Suc_u m) (Suc_u n) PeanoNats__subres) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite PeanoNats__sub_Suc_Suc_lem : f_rel_back.
Theorem PeanoNats__sub_rel_ex (m: Nats_u) (n: Nats_u) (m_p: (Nats_wf m) /\ True) (n_p: (Nats_wf n) /\ (geqN_rel m n true)): PeanoNats__sub_rel m n (⌊ PeanoNats__sub (exist _ m m_p) (exist _ n n_p) -⌋). 
Proof. 
	Opaque PeanoNats__sub.
	existence_lemma_pre PeanoNats__sub; 
	try revert n_p; generalize dependent n; 
	induction m as [(*Suc*) m IH_m | (*Zero*) ]; 
	intros ; 
	[induction n as [(*Suc*) n IH_n | (*Zero*) ]; 
	intros ; 
	[fix_notations; 
	pose proof (IH_m (ltac: (try clear IH_m; 
	solver)) n (ltac: (try clear IH_m; 
	solver))) as IH_13828668; 
	try clear IH_m; 
	try clear IH_n| 
	fix_notations; 
	try clear IH_m]| 
	induction n as [(*Suc*) lq_anf7205759403792810480 IH_lq_anf7205759403792810480 | (*Zero*) ]; 
	intros ; 
	[fix_notations; 
	try clear IH_lq_anf7205759403792810480| 
	fix_notations]]; 
	simpl in *. 
	Transparent PeanoNats__sub.
	all: existence_lemma_quicksolve PeanoNats__sub; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve PeanoNats__sub_rel_ex : rel_ax_db.
#[global] Opaque PeanoNats__sub. 
Theorem PeanoNats__sub__PeanoNats__sub_rel_rw (m: Nats_u) (n: Nats_u) (m_p: (Nats_wf m) /\ True) (n_p: (Nats_wf n) /\ (geqN_rel m n true)) (o: Nats_u): ((⌊ PeanoNats__sub (exist _ m m_p) (exist _ n n_p) -⌋) = o) <-> (PeanoNats__sub_rel m n o). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite PeanoNats__sub__PeanoNats__sub_rel_rw : f_rel_funct_db.
#[global] Hint Resolve PeanoNats__sub__PeanoNats__sub_rel_rw : rel_ax_db.
#[global] Instance PeanoNats__sub_lookup_rw : dictionary rwLem PeanoNats__sub := { 
	lookup' := PeanoNats__sub__PeanoNats__sub_rel_rw
}.
Theorem PeanoNats__sub__PeanoNats__sub_rel (m_r: Nats) (n_r: {n: Nats_u | (Nats_wf n) /\ (geqN_rel (⌊ m_r -⌋) n true)}) (o: Nats_u): ((⌊ PeanoNats__sub m_r n_r -⌋) = o) <-> (PeanoNats__sub_rel (⌊ m_r -⌋) (⌊ n_r -⌋) o). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite PeanoNats__sub__PeanoNats__sub_rel : f_rel_funct_db.
Theorem PeanoNats__sub__PeanoNats__sub_rel' (m: Nats_u) (n: Nats_u) (m_r: Nats) (n_r: {n: Nats_u | (Nats_wf n) /\ (geqN_rel (⌊ m_r -⌋) n true)}) (o: Nats_u): (m = (⌊ m_r -⌋)) -> ((n = (⌊ n_r -⌋)) -> (((⌊ PeanoNats__sub m_r n_r -⌋) = o) <-> (PeanoNats__sub_rel m n o))). 
Proof. 
	intros -> ->. 
	refine (PeanoNats__sub__PeanoNats__sub_rel m_r n_r o). 
Qed. 
#[global] Hint Resolve PeanoNats__sub__PeanoNats__sub_rel' : f_rel_funct_db.
Theorem PeanoNats__sub_rel_mk [m: Nats_u] [n: Nats_u] (m_p: (Nats_wf m) /\ True) (n_p: (Nats_wf n) /\ (geqN_rel m n true)): {o: _ | PeanoNats__sub_rel m n o}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (o: _) => (PeanoNats__sub_rel m n o)) (PeanoNats__sub (exist _ m m_p) (exist _ n n_p)) _); 
	rewrite <- PeanoNats__sub__PeanoNats__sub_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve PeanoNats__sub_rel_mk : f_rel_funct_db.
#[global] Instance PeanoNats__subPack : (@Pack (Nats ::RT (fun (m_r: Nats) => ({n: Nats_u | (Nats_wf n) /\ (geqN_rel (⌊ m_r -⌋) n true)} ::RT (fun (n_r: {n: Nats_u | (Nats_wf n) /\ (geqN_rel (⌊ m_r -⌋) n true)}) => nilRT)))) (Nats_u ::UT (Nats_u ::UT nilUT)) (ltac: (mkProjectsArgListTG (Nats ::RT (fun (m_r: Nats) => ({n: Nats_u | (Nats_wf n) /\ (geqN_rel (⌊ m_r -⌋) n true)} ::RT (fun (n_r: {n: Nats_u | (Nats_wf n) /\ (geqN_rel (⌊ m_r -⌋) n true)}) => nilRT)))) (Nats_u ::UT (Nats_u ::UT nilUT)))) Nats_u (fun (x_87946269: (ArgList Nats ::RT (fun (m_r: Nats) => ({n: Nats_u | (Nats_wf n) /\ (geqN_rel (⌊ m_r -⌋) n true)} ::RT (fun (n_r: {n: Nats_u | (Nats_wf n) /\ (geqN_rel (⌊ m_r -⌋) n true)}) => nilRT))))) => (fun (v_x_87946269: Nats_u) => (ltac: (flattenP (fun (m_r: Nats) => (fun (n_r: {n: Nats_u | (Nats_wf n) /\ (geqN_rel (⌊ m_r -⌋) n true)}) => (fun (o: Nats_u) => ((Nats_wf o) /\ ((o <> Zero_u) <-> ((⌊ m_r -⌋) <> (⌊ n_r -⌋))))))) x_87946269 v_x_87946269))))).
Proof. 
	buildPackG PeanoNats__sub PeanoNats__sub_rel PeanoNats__sub__PeanoNats__sub_rel PeanoNats__sub_rel_funct. 
Defined.
Definition add_sub_spec (m: Nats) (n: Nats): Type := 
	{{forall (addres: Nats_u), (add_rel (⌊ m -⌋) (⌊ n -⌋) addres) -> (forall (PeanoNats__subres: Nats_u), (PeanoNats__sub_rel addres (⌊ n -⌋) PeanoNats__subres) -> (PeanoNats__subres = (⌊ m -⌋)))}}. 
#[global] Hint Unfold add_sub_spec : lia_unfold.
Theorem add_sub (m: Nats) (n: Nats): add_sub_spec m n. 
Proof. 
	destruct m as [m m_p]. 
	destruct n as [n n_p]. 
	try revert n_p; generalize dependent n; 
	induction m as [(*Suc*) m IH_m | (*Zero*) ]. 
	  - intros . 
		induction n as [(*Suc*) n IH_n | (*Zero*) ]. 
		  -- intros . 
			pose proof (IH_n (ltac: (try clear IH_n; 
	solver))) as H_61903511. 
			simpl in H_61903511. 
			refine (subsumptionCast _ _ 
		(add_suc_r 
		(subsumptionCast Nats_u (fun (m: Nats_u) => ((Nats_wf m) /\ True)) 
		(Suc 
		(exist (fun (n: Nats_u) => ((Nats_wf n) /\ True)) m (ltac: (solver)))) (ltac: (solver))) 
		(exist (fun (n: Nats_u) => ((Nats_wf n) /\ True)) n (ltac: (solver)))) _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ 
		(add_zero_r 
		(exist (fun (n: Nats_u) => ((Nats_wf n) /\ True)) m (ltac: (solver)))) _); 
			solver.   
	  - intros . 
		induction n as [(*Suc*) n IH_n | (*Zero*) ]. 
		  -- intros . 
			pose proof (IH_n (ltac: (try clear IH_n; 
	solver))) as H_38815771. 
			simpl in H_38815771. 
			refine (subsumptionCast _ _ 
		(add_suc_r 
		(subsumptionCast Nats_u (fun (m: Nats_u) => ((Nats_wf m) /\ True)) Zero (ltac: (solver))) 
		(exist (fun (n: Nats_u) => ((Nats_wf n) /\ True)) n (ltac: (solver)))) _); 
			solver.  
		  -- intros . 
			refine (exist _ unit _); 
			solver.   
Qed. 
Definition mult_spec (m: Nats) (n: Nats): Type := 
	Nats. 
#[global] Hint Unfold mult_spec : lia_unfold.
Definition mult (m: Nats) (n: Nats): mult_spec m n. 
Proof. 
	destruct m as [m m_p]. 
	destruct n as [n n_p]. 
	try revert n_p; generalize dependent n; 
	induction m as [(*Suc*) m IH_m | (*Zero*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ 
		(add 
		(exist (fun (m: Nats_u) => ((Nats_wf m) /\ True)) n (ltac: (solver))) 
		(subsumptionCast Nats_u (fun (n: Nats_u) => ((Nats_wf n) /\ True)) 
		(IH_m (ltac: (try clear IH_m; 
	solver)) n (ltac: (try clear IH_m; 
	solver))) (ltac: (solver)))) _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ Zero _); 
		solver.  
Defined. 
Inductive mult_rel : (Nats_u -> (Nats_u -> (Nats_u -> Prop))) := 
	 | mult_Zero: (forall n , mult_rel Zero_u n Zero_u)
	 | mult_Suc: (forall m n , forall (multres: Nats_u), (mult_rel m n multres) -> (forall (addres: Nats_u), (add_rel n multres addres) -> (mult_rel (Suc_u m) n addres))). 
#[global] Hint Constructors mult_rel : core_hint_db.
#[global] Instance mult_lookup_rel : dictionary rel mult := { 
	lookup' := mult_rel
}.
#[global] Instance mult_getF : getFunc mult_rel := { 
	getF' := mult
}.
Theorem mult_rel_funct [m: Nats_u] [n: Nats_u]: (forall (VV: Nats_u) (VV': Nats_u) (H: mult_rel m n VV) (K: mult_rel m n VV') , VV = VV'). 
Proof. 
	try revert n_p; generalize dependent n; 
	induction m as [(*Suc*) m IH_m | (*Zero*) ]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve mult_rel_funct : f_rel_funct_db.
Theorem mult_Zero_lem (n: _): (mult_rel Zero_u n Zero_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite mult_Zero_lem : f_rel_back.
Theorem mult_Suc_lem (m: _) (n: _) (addres: Nats_u): (mult_rel (Suc_u m) n addres) <-> (exists (multres: Nats_u), (mult_rel m n multres) /\ (add_rel n multres addres)). 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite mult_Suc_lem : f_rel_back.
Theorem mult_rel_ex (m: Nats_u) (n: Nats_u) (m_p: (Nats_wf m) /\ True) (n_p: (Nats_wf n) /\ True): mult_rel m n (⌊ mult (exist _ m m_p) (exist _ n n_p) -⌋). 
Proof. 
	Opaque mult.
	existence_lemma_pre mult; 
	try revert n_p; generalize dependent n; 
	induction m as [(*Suc*) m IH_m | (*Zero*) ]; 
	intros ; 
	[fix_notations; 
	pose proof (IH_m (ltac: (try clear IH_m; 
	solver)) n (ltac: (try clear IH_m; 
	solver))) as IH_13828668; 
	try clear IH_m| 
	fix_notations]; 
	simpl in *. 
	Transparent mult.
	all: existence_lemma_quicksolve mult; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve mult_rel_ex : rel_ax_db.
#[global] Opaque mult. 
Theorem mult__mult_rel_rw (m: Nats_u) (n: Nats_u) (m_p: (Nats_wf m) /\ True) (n_p: (Nats_wf n) /\ True) (VV: Nats_u): ((⌊ mult (exist _ m m_p) (exist _ n n_p) -⌋) = VV) <-> (mult_rel m n VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite mult__mult_rel_rw : f_rel_funct_db.
#[global] Hint Resolve mult__mult_rel_rw : rel_ax_db.
#[global] Instance mult_lookup_rw : dictionary rwLem mult := { 
	lookup' := mult__mult_rel_rw
}.
Theorem mult__mult_rel (m_r: Nats) (n_r: Nats) (VV: Nats_u): ((⌊ mult m_r n_r -⌋) = VV) <-> (mult_rel (⌊ m_r -⌋) (⌊ n_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite mult__mult_rel : f_rel_funct_db.
Theorem mult__mult_rel' (m: Nats_u) (n: Nats_u) (m_r: Nats) (n_r: Nats) (VV: Nats_u): (m = (⌊ m_r -⌋)) -> ((n = (⌊ n_r -⌋)) -> (((⌊ mult m_r n_r -⌋) = VV) <-> (mult_rel m n VV))). 
Proof. 
	intros -> ->. 
	refine (mult__mult_rel m_r n_r VV). 
Qed. 
#[global] Hint Resolve mult__mult_rel' : f_rel_funct_db.
Theorem mult_rel_mk [m: Nats_u] [n: Nats_u] (m_p: (Nats_wf m) /\ True) (n_p: (Nats_wf n) /\ True): {VV: _ | mult_rel m n VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (mult_rel m n VV)) (mult (exist _ m m_p) (exist _ n n_p)) _); 
	rewrite <- mult__mult_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve mult_rel_mk : f_rel_funct_db.
#[global] Instance multPack : (@Pack (Nats ::RT (fun (m_r: Nats) => (Nats ::RT (fun (n_r: Nats) => nilRT)))) (Nats_u ::UT (Nats_u ::UT nilUT)) (ltac: (mkProjectsArgListTG (Nats ::RT (fun (m_r: Nats) => (Nats ::RT (fun (n_r: Nats) => nilRT)))) (Nats_u ::UT (Nats_u ::UT nilUT)))) Nats_u (fun (x_44523598: (ArgList Nats ::RT (fun (m_r: Nats) => (Nats ::RT (fun (n_r: Nats) => nilRT))))) => (fun (v_x_44523598: Nats_u) => (ltac: (flattenP (fun (m_r: Nats) => (fun (n_r: Nats) => (fun (VV: Nats_u) => ((Nats_wf VV) /\ True)))) x_44523598 v_x_44523598))))).
Proof. 
	buildPackG mult mult_rel mult__mult_rel mult_rel_funct. 
Defined.
<<<<<<< HEAD

#[global] Instance add_upack: @uPack (Nats_u ::UT (Nats_u ::UT nilUT)) Nats_u.
Proof.
  buildUPackG add_rel add_rel_funct.
Defined.

Definition add' (m n : Nats):
  {v: Nats_u | Nats_wf v
               ∧ ∀ add_res,
                 add_rel ⌊ m ⌋ ⌊ n ⌋ add_res → ∀ add_res_2, add_rel add_res Zero_u add_res_2 → add_res_2 == v}.
Proof.
  destruct m as [m m_p].
  destruct n as [n n_p].
  refine (subsumptionCast
          Nats_u
          (λ (v : Nats_u),
           Nats_wf v
           ∧ ∀ add_res,
             add_rel ⌊ m ⌋ ⌊ n ⌋ add_res → ∀ add_res_2, add_rel add_res Zero_u add_res_2 → add_res_2 == v)
          (add
           (add
            (exist (λ (m : Nats_u), Nats_wf m ∧ True) m ltac:(solver))
            (exist (λ (n : Nats_u), Nats_wf n ∧ True) n ltac:(solver)))
           Zero)
          ltac:(solver)).
Defined.

Definition add'' (m n : Nats):
  {v: Nats_u | Nats_wf v ∧ ∀ add_res, add_rel ⌊ m ⌋ ⌊ n ⌋ add_res → add_res == v}.
Proof.
  destruct m as [m m_p].
  destruct n as [n n_p].
  refine (subsumptionCast
          Nats_u
          (λ (v : Nats_u), Nats_wf v ∧ ∀ add_res, add_rel ⌊ m ⌋ ⌊ n ⌋ add_res → add_res == v)
          (add
           (exist (λ (m : Nats_u), Nats_wf m ∧ True) m ltac:(solver))
           (exist (λ (n : Nats_u), Nats_wf n ∧ True) n ltac:(solver)))
          ltac:(solver)).
Defined.

Definition add_assoc (m n o : Nats):
  {{∀ add_res,
    add_rel ⌊ n ⌋ ⌊ o ⌋ add_res
    → ∀ add_res_2,
      add_rel ⌊ m ⌋ add_res add_res_2
      → ∀ add_res_3,
        add_rel ⌊ m ⌋ ⌊ n ⌋ add_res_3
        → ∀ add_res_4, add_rel add_res_3 ⌊ o ⌋ add_res_4 → add_res_2 == add_res_4}}.
Proof.
  destruct m as [m m_p].
  destruct n as [n n_p].
  destruct o as [o o_p].
  try revert o_p; generalize dependent o; try revert n_p; generalize dependent n;
  induction m as [m IH_m|];
  intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∀ add_res,
             add_rel ⌊ n ⌋ ⌊ o ⌋ add_res
             → ∀ add_res_2,
               add_rel ⌊ m ⌋ add_res add_res_2
               → ∀ add_res_3,
                 add_rel ⌊ m ⌋ ⌊ n ⌋ add_res_3
                 → ∀ add_res_4, add_rel add_res_3 ⌊ o ⌋ add_res_4 → add_res_2 == add_res_4)
            (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver) o ltac:(try clear IH_m; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∀ add_res,
             add_rel ⌊ n ⌋ ⌊ o ⌋ add_res
             → ∀ add_res_2,
               add_rel ⌊ m ⌋ add_res add_res_2
               → ∀ add_res_3,
                 add_rel ⌊ m ⌋ ⌊ n ⌋ add_res_3
                 → ∀ add_res_4, add_rel add_res_3 ⌊ o ⌋ add_res_4 → add_res_2 == add_res_4)
            (# unit)
            ltac:(solver)).
Defined.

Definition add_suc_r (m n : Nats):
  {{∀ add_res,
    add_rel ⌊ m ⌋ ⌊ n ⌋ add_res
    → ∀ add_res_2, add_rel ⌊ m ⌋ (Suc_u ⌊ n ⌋) add_res_2 → Suc_u add_res == add_res_2}}.
Proof.
  destruct m as [m m_p].
  destruct n as [n n_p].
  try revert n_p; generalize dependent n; induction m as [m IH_m|]; intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∀ add_res,
             add_rel ⌊ m ⌋ ⌊ n ⌋ add_res
             → ∀ add_res_2, add_rel ⌊ m ⌋ (Suc_u ⌊ n ⌋) add_res_2 → Suc_u add_res == add_res_2)
            (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∀ add_res,
             add_rel ⌊ m ⌋ ⌊ n ⌋ add_res
             → ∀ add_res_2, add_rel ⌊ m ⌋ (Suc_u ⌊ n ⌋) add_res_2 → Suc_u add_res == add_res_2)
            (# unit)
            ltac:(solver)).
Defined.

Definition add_zero_l (n : Nats): {{∀ add_res, add_rel Zero_u ⌊ n ⌋ add_res → add_res == ⌊ n ⌋}}.
Proof.
  destruct n as [n n_p].
  induction n as [n IH_n|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∀ add_res, add_rel Zero_u ⌊ n ⌋ add_res → add_res == ⌊ n ⌋)
            (IH_n ltac:(try clear IH_n; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∀ add_res, add_rel Zero_u ⌊ n ⌋ add_res → add_res == ⌊ n ⌋)
            (# unit)
            ltac:(solver)).
Defined.

Definition add_zero_l_test :
  {{∀ add_res, add_rel Zero_u (Suc_u (Suc_u Zero_u)) add_res → add_res == Suc_u (Suc_u Zero_u)}}.
Proof.
  refine (subsumptionCast
          Unit
          (λ (VV : Unit),
           ∀ add_res, add_rel Zero_u (Suc_u (Suc_u Zero_u)) add_res → add_res == Suc_u (Suc_u Zero_u))
          (add_zero_l (Suc (Suc Zero)))
          ltac:(solver)).
Defined.

Definition add_zero_r (n : Nats): {{∀ add_res, add_rel ⌊ n ⌋ Zero_u add_res → add_res == ⌊ n ⌋}}.
Proof.
  destruct n as [n n_p].
  induction n as [n IH_n|].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∀ add_res, add_rel ⌊ n ⌋ Zero_u add_res → add_res == ⌊ n ⌋)
            (IH_n ltac:(try clear IH_n; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∀ add_res, add_rel ⌊ n ⌋ Zero_u add_res → add_res == ⌊ n ⌋)
            (# unit)
            ltac:(solver)).
Defined.

Definition eqN (m n : Nats): Bool.
Proof.
  destruct m as [m m_p].
  destruct n as [n n_p].
  try revert n_p; generalize dependent n; induction m as [m IH_m|]; intros.
  - destruct n as [n|].
    + refine (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver)).
    + refine (# false).
  - destruct n as [lq_anf7205759403792802883|].
    + refine (# false).
    + refine (# true).
Defined.

Inductive eqN_rel: Nats_u → Nats_u → bool → Prop :=
  | eqN_Zero_Zero: eqN_rel Zero_u Zero_u true
  | eqN_Zero_Suc: ∀ lq_anf7205759403792802883, eqN_rel Zero_u (Suc_u lq_anf7205759403792802883) false
  | eqN_Suc_Zero: ∀ m, eqN_rel (Suc_u m) Zero_u false
  | eqN_Suc_Suc: ∀ m n eqN_res, eqN_rel m n eqN_res → eqN_rel (Suc_u m) (Suc_u n) eqN_res.

#[global] Hint Constructors eqN_rel: core_hint_db.

#[global] Instance eqN_lookup_rel: dictionary rel eqN := { lookup' := eqN_rel }.

#[global] Instance eqN_getF: getFunc eqN_rel := { getF' := eqN }.

Definition eqN_rel_funct [m n : Nats_u]:
  ∀ (VV VV' : bool), eqN_rel m n VV → (eqN_rel m n VV' → VV = VV').
Proof.
  try revert n_p; generalize dependent n; induction m as [m IH_m|]; intros;
  [destruct n as [n|] | destruct n as [lq_anf7205759403792802883|]];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve eqN_rel_funct: f_rel_funct_db.

Theorem eqN_Zero_Zero_lem eqN_Zero_Zero_lem_res:
  eqN_rel Zero_u Zero_u eqN_Zero_Zero_lem_res ↔ eqN_Zero_Zero_lem_res == true.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite eqN_Zero_Zero_lem: f_rel_back.

Theorem eqN_Zero_Suc_lem lq_anf7205759403792802883 eqN_Zero_Suc_lem_res:
  eqN_rel Zero_u (Suc_u lq_anf7205759403792802883) eqN_Zero_Suc_lem_res
  ↔ eqN_Zero_Suc_lem_res == false.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite eqN_Zero_Suc_lem: f_rel_back.

Theorem eqN_Suc_Zero_lem m eqN_Suc_Zero_lem_res:
  eqN_rel (Suc_u m) Zero_u eqN_Suc_Zero_lem_res ↔ eqN_Suc_Zero_lem_res == false.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite eqN_Suc_Zero_lem: f_rel_back.

Theorem eqN_Suc_Suc_lem m n eqN_Suc_Suc_lem_res:
  eqN_rel (Suc_u m) (Suc_u n) eqN_Suc_Suc_lem_res
  ↔ ∃ eqN_res, eqN_rel m n eqN_res ∧ eqN_Suc_Suc_lem_res == eqN_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite eqN_Suc_Suc_lem: f_rel_back.

Theorem eqN_rel_ex (m : Nats_u) (m_p : Nats_wf m ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True):
  eqN_rel m n ⌊ eqN (exist _ m m_p) (exist _ n n_p) ⌋.
Proof.
  existence_lemma_pre eqN;
  try revert n_p; generalize dependent n; induction m as [m IH_m|]; intros;
  [destruct n as [n|];
   [fix_notations;
    pose proof (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver)) as IH_14792487;
    try clear IH_m |
    fix_notations] |
   destruct n as [lq_anf7205759403792802883|];
   [fix_notations | fix_notations]];
  existence_lemma_quicksolve eqN;
  f__f_rel_ex_body;
  f_rel_finish.
Qed.

#[global] Hint Resolve eqN_rel_ex: rel_ax_db.

Opaque eqN.

Theorem eqN__eqN_rel_rw
  (m : Nats_u) (m_p : Nats_wf m ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True) (VV : bool):
  ⌊ eqN (exist _ m m_p) (exist _ n n_p) ⌋ = VV ↔ eqN_rel m n VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite eqN__eqN_rel_rw: f_rel_funct_db.

#[global] Hint Resolve eqN__eqN_rel_rw: rel_ax_db.

#[global] Instance eqN_lookup_rw: dictionary rwLem eqN := { lookup' := eqN__eqN_rel_rw }.

Theorem eqN__eqN_rel (m n : Nats) (VV : bool): ⌊ eqN m n ⌋ = VV ↔ eqN_rel ⌊ m ⌋ ⌊ n ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite eqN__eqN_rel: f_rel_funct_db.

Theorem eqN__eqN_rel' (m_u n_u : Nats_u) (m n : Nats) (VV : bool):
  m_u = ⌊ m ⌋ → (n_u = ⌊ n ⌋ → ⌊ eqN m n ⌋ = VV ↔ eqN_rel m_u n_u VV).
Proof.
  intros -> ->. refine (eqN__eqN_rel m n VV).
Qed.

#[global] Hint Resolve eqN__eqN_rel': f_rel_funct_db.

Definition eqN_rel_mk (m : Nats_u) (m_p : Nats_wf m ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True):
  {VV: _ | eqN_rel m n VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, eqN_rel m n VV) (eqN (exist _ m m_p) (exist _ n n_p)) _);
  rewrite <- eqN__eqN_rel';
  quicksolve.
Qed.

#[global] Hint Resolve eqN_rel_mk: f_rel_funct_db.

#[global] Instance eqN_pack:
  @Pack
  (Nats ::RT λ (m : Nats), Nats ::RT λ (n : Nats), nilRT)
  (Nats_u ::UT (Nats_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((Nats ::RT λ (m : Nats), Nats ::RT λ (n : Nats), nilRT)) ((Nats_u ::UT (Nats_u ::UT nilUT))))
  bool
  (λ (x_90321534 : ArgList (Nats ::RT λ (m : Nats), Nats ::RT λ (n : Nats), nilRT))
     (v_x_90321534 : bool),
   ltac:(flattenP (λ (m n : Nats) (VV : bool), True) x_90321534 v_x_90321534)).
Proof.
  buildPackG eqN eqN_rel eqN__eqN_rel eqN_rel_funct.
Defined.

#[global] Instance eqN_upack: @uPack (Nats_u ::UT (Nats_u ::UT nilUT)) bool.
Proof.
  buildUPackG eqN_rel eqN_rel_funct.
Defined.

Definition test_eqN : {r : bool | is_true r}.
Proof.
  refine (subsumptionCast
          bool
          (λ (r : bool), is_true r)
          (eqN (Suc (Suc (Suc Zero))) (Suc (Suc (Suc Zero))))
          ltac:(solver)).
Defined.

Definition test_eqN' : {r : bool | ¬ is_true r}.
Proof.
  refine (subsumptionCast
          bool
          (λ (r : bool), ¬ is_true r)
          (eqN (Suc (Suc Zero)) (Suc Zero))
          ltac:(solver)).
Defined.

Definition geqN (m n : Nats): Bool.
Proof.
  destruct m as [m m_p].
  destruct n as [n n_p].
  try revert m_p; generalize dependent m;
  induction n as [lq_anf7205759403792802880 IH_lq_anf7205759403792802880|];
  intros.
  - destruct m as [m|].
    + refine (IH_lq_anf7205759403792802880
              ltac:(try clear IH_lq_anf7205759403792802880; solver)
              m
              ltac:(try clear IH_lq_anf7205759403792802880; solver)).
    + refine (# false).
  - refine (# true).
Defined.

Inductive geqN_rel: Nats_u → Nats_u → bool → Prop :=
  | geqN_x_Zero: ∀ m, geqN_rel m Zero_u true
  | geqN_Zero_Suc: ∀ lq_anf7205759403792802880,
                   geqN_rel Zero_u (Suc_u lq_anf7205759403792802880) false
  | geqN_Suc_Suc: ∀ m lq_anf7205759403792802880 geqN_res,
                  geqN_rel m lq_anf7205759403792802880 geqN_res
                  → geqN_rel (Suc_u m) (Suc_u lq_anf7205759403792802880) geqN_res.

#[global] Hint Constructors geqN_rel: core_hint_db.

#[global] Instance geqN_lookup_rel: dictionary rel geqN := { lookup' := geqN_rel }.

#[global] Instance geqN_getF: getFunc geqN_rel := { getF' := geqN }.

Definition geqN_rel_funct [m n : Nats_u]:
  ∀ (VV VV' : bool), geqN_rel m n VV → (geqN_rel m n VV' → VV = VV').
Proof.
  try revert m_p; generalize dependent m;
  induction n as [lq_anf7205759403792802880 IH_lq_anf7205759403792802880|];
  intros;
  [destruct m as [m|] |];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve geqN_rel_funct: f_rel_funct_db.

Theorem geqN_x_Zero_lem m geqN_x_Zero_lem_res:
  geqN_rel m Zero_u geqN_x_Zero_lem_res ↔ geqN_x_Zero_lem_res == true.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite geqN_x_Zero_lem: f_rel_back.

Theorem geqN_Zero_Suc_lem lq_anf7205759403792802880 geqN_Zero_Suc_lem_res:
  geqN_rel Zero_u (Suc_u lq_anf7205759403792802880) geqN_Zero_Suc_lem_res
  ↔ geqN_Zero_Suc_lem_res == false.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite geqN_Zero_Suc_lem: f_rel_back.

Theorem geqN_Suc_Suc_lem lq_anf7205759403792802880 m geqN_Suc_Suc_lem_res:
  geqN_rel (Suc_u m) (Suc_u lq_anf7205759403792802880) geqN_Suc_Suc_lem_res
  ↔ ∃ geqN_res, geqN_rel m lq_anf7205759403792802880 geqN_res ∧ geqN_Suc_Suc_lem_res == geqN_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite geqN_Suc_Suc_lem: f_rel_back.

Theorem geqN_rel_ex (m : Nats_u) (m_p : Nats_wf m ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True):
  geqN_rel m n ⌊ geqN (exist _ m m_p) (exist _ n n_p) ⌋.
Proof.
  existence_lemma_pre geqN;
  try revert m_p; generalize dependent m;
  induction n as [lq_anf7205759403792802880 IH_lq_anf7205759403792802880|];
  intros;
  [destruct m as [m|];
   [fix_notations;
    pose proof (IH_lq_anf7205759403792802880
                ltac:(try clear IH_lq_anf7205759403792802880; solver)
                m
                ltac:(try clear IH_lq_anf7205759403792802880; solver)) as IH_46078018;
    try clear IH_lq_anf7205759403792802880 |
    fix_notations] |
   fix_notations];
  existence_lemma_quicksolve geqN;
  f__f_rel_ex_body;
  f_rel_finish.
Qed.

#[global] Hint Resolve geqN_rel_ex: rel_ax_db.

Opaque geqN.

Theorem geqN__geqN_rel_rw
  (m : Nats_u) (m_p : Nats_wf m ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True) (VV : bool):
  ⌊ geqN (exist _ m m_p) (exist _ n n_p) ⌋ = VV ↔ geqN_rel m n VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite geqN__geqN_rel_rw: f_rel_funct_db.

#[global] Hint Resolve geqN__geqN_rel_rw: rel_ax_db.

#[global] Instance geqN_lookup_rw: dictionary rwLem geqN := { lookup' := geqN__geqN_rel_rw }.

Theorem geqN__geqN_rel (m n : Nats) (VV : bool): ⌊ geqN m n ⌋ = VV ↔ geqN_rel ⌊ m ⌋ ⌊ n ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite geqN__geqN_rel: f_rel_funct_db.

Theorem geqN__geqN_rel' (m_u n_u : Nats_u) (m n : Nats) (VV : bool):
  m_u = ⌊ m ⌋ → (n_u = ⌊ n ⌋ → ⌊ geqN m n ⌋ = VV ↔ geqN_rel m_u n_u VV).
Proof.
  intros -> ->. refine (geqN__geqN_rel m n VV).
Qed.

#[global] Hint Resolve geqN__geqN_rel': f_rel_funct_db.

Definition geqN_rel_mk (m : Nats_u) (m_p : Nats_wf m ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True):
  {VV: _ | geqN_rel m n VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, geqN_rel m n VV) (geqN (exist _ m m_p) (exist _ n n_p)) _);
  rewrite <- geqN__geqN_rel';
  quicksolve.
Qed.

#[global] Hint Resolve geqN_rel_mk: f_rel_funct_db.

#[global] Instance geqN_pack:
  @Pack
  (Nats ::RT λ (m : Nats), Nats ::RT λ (n : Nats), nilRT)
  (Nats_u ::UT (Nats_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((Nats ::RT λ (m : Nats), Nats ::RT λ (n : Nats), nilRT)) ((Nats_u ::UT (Nats_u ::UT nilUT))))
  bool
  (λ (x_90321534 : ArgList (Nats ::RT λ (m : Nats), Nats ::RT λ (n : Nats), nilRT))
     (v_x_90321534 : bool),
   ltac:(flattenP (λ (m n : Nats) (VV : bool), True) x_90321534 v_x_90321534)).
Proof.
  buildPackG geqN geqN_rel geqN__geqN_rel geqN_rel_funct.
Defined.

#[global] Instance geqN_upack: @uPack (Nats_u ::UT (Nats_u ::UT nilUT)) bool.
Proof.
  buildUPackG geqN_rel geqN_rel_funct.
Defined.

Definition mult (m n : Nats): Nats.
Proof.
  destruct m as [m m_p].
  destruct n as [n n_p].
  try revert n_p; generalize dependent n; induction m as [m IH_m|]; intros.
  - refine (add
            (exist (λ (n : Nats_u), Nats_wf n ∧ True) n ltac:(solver))
            (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver))).
  - refine Zero.
Defined.

Inductive mult_rel: Nats_u → Nats_u → Nats_u → Prop :=
  | mult_Zero_x: ∀ n, mult_rel Zero_u n Zero_u
  | mult_Suc_x: ∀ m n mult_res,
                mult_rel m n mult_res → ∀ add_res, add_rel n mult_res add_res → mult_rel (Suc_u m) n add_res.

#[global] Hint Constructors mult_rel: core_hint_db.

#[global] Instance mult_lookup_rel: dictionary rel mult := { lookup' := mult_rel }.

#[global] Instance mult_getF: getFunc mult_rel := { getF' := mult }.

Definition mult_rel_funct [m n : Nats_u]:
  ∀ (VV VV' : Nats_u), mult_rel m n VV → (mult_rel m n VV' → VV = VV').
Proof.
  try revert n_p; generalize dependent n; induction m as [m IH_m|]; intros; rel_functionhood_body.
Qed.

#[global] Hint Resolve mult_rel_funct: f_rel_funct_db.

Theorem mult_Zero_x_lem n mult_Zero_x_lem_res:
  mult_rel Zero_u n mult_Zero_x_lem_res ↔ mult_Zero_x_lem_res == Zero_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite mult_Zero_x_lem: f_rel_back.

Theorem mult_Suc_x_lem m n mult_Suc_x_lem_res:
  mult_rel (Suc_u m) n mult_Suc_x_lem_res
  ↔ ∃ mult_res,
    mult_rel m n mult_res ∧ ∃ add_res, add_rel n mult_res add_res ∧ mult_Suc_x_lem_res == add_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite mult_Suc_x_lem: f_rel_back.

Theorem mult_rel_ex (m : Nats_u) (m_p : Nats_wf m ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True):
  mult_rel m n ⌊ mult (exist _ m m_p) (exist _ n n_p) ⌋.
Proof.
  existence_lemma_pre mult;
  try revert n_p; generalize dependent n; induction m as [m IH_m|]; intros;
  [fix_notations | fix_notations];
  existence_lemma_quicksolve mult;
  f__f_rel_ex_body;
  f_rel_finish.
Qed.

#[global] Hint Resolve mult_rel_ex: rel_ax_db.

Opaque mult.

Theorem mult__mult_rel_rw
  (m : Nats_u) (m_p : Nats_wf m ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True) (VV : Nats_u):
  ⌊ mult (exist _ m m_p) (exist _ n n_p) ⌋ = VV ↔ mult_rel m n VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite mult__mult_rel_rw: f_rel_funct_db.

#[global] Hint Resolve mult__mult_rel_rw: rel_ax_db.

#[global] Instance mult_lookup_rw: dictionary rwLem mult := { lookup' := mult__mult_rel_rw }.

Theorem mult__mult_rel (m n : Nats) (VV : Nats_u): ⌊ mult m n ⌋ = VV ↔ mult_rel ⌊ m ⌋ ⌊ n ⌋ VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite mult__mult_rel: f_rel_funct_db.

Theorem mult__mult_rel' (m_u n_u : Nats_u) (m n : Nats) (VV : Nats_u):
  m_u = ⌊ m ⌋ → (n_u = ⌊ n ⌋ → ⌊ mult m n ⌋ = VV ↔ mult_rel m_u n_u VV).
Proof.
  intros -> ->. refine (mult__mult_rel m n VV).
Qed.

#[global] Hint Resolve mult__mult_rel': f_rel_funct_db.

Definition mult_rel_mk (m : Nats_u) (m_p : Nats_wf m ∧ True) (n : Nats_u) (n_p : Nats_wf n ∧ True):
  {VV: _ | mult_rel m n VV}.
Proof.
  intros;
  refine (subsumptionCast _ (λ VV, mult_rel m n VV) (mult (exist _ m m_p) (exist _ n n_p)) _);
  rewrite <- mult__mult_rel';
  quicksolve.
Qed.

#[global] Hint Resolve mult_rel_mk: f_rel_funct_db.

#[global] Instance mult_pack:
  @Pack
  (Nats ::RT λ (m : Nats), Nats ::RT λ (n : Nats), nilRT)
  (Nats_u ::UT (Nats_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((Nats ::RT λ (m : Nats), Nats ::RT λ (n : Nats), nilRT)) ((Nats_u ::UT (Nats_u ::UT nilUT))))
  Nats_u
  (λ (x_90321534 : ArgList (Nats ::RT λ (m : Nats), Nats ::RT λ (n : Nats), nilRT))
     (v_x_90321534 : Nats_u),
   ltac:(flattenP (λ (m n : Nats) (VV : Nats_u), Nats_wf VV ∧ True) x_90321534 v_x_90321534)).
Proof.
  buildPackG mult mult_rel mult__mult_rel mult_rel_funct.
Defined.

#[global] Instance mult_upack: @uPack (Nats_u ::UT (Nats_u ::UT nilUT)) Nats_u.
Proof.
  buildUPackG mult_rel mult_rel_funct.
Defined.

Definition add_dist_rmult (m n o : Nats):
  {{∀ add_res,
    add_rel ⌊ m ⌋ ⌊ n ⌋ add_res
    → ∀ mult_res,
      mult_rel add_res ⌊ o ⌋ mult_res
      → ∀ mult_res_2,
        mult_rel ⌊ n ⌋ ⌊ o ⌋ mult_res_2
        → ∀ mult_res_3,
          mult_rel ⌊ m ⌋ ⌊ o ⌋ mult_res_3
          → ∀ add_res_2, add_rel mult_res_3 mult_res_2 add_res_2 → mult_res == add_res_2}}.
Proof.
  destruct m as [m m_p].
  destruct n as [n n_p].
  destruct o as [o o_p].
  try revert o_p; generalize dependent o; try revert n_p; generalize dependent n;
  induction m as [m IH_m|];
  intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∀ add_res,
             add_rel ⌊ m ⌋ ⌊ n ⌋ add_res
             → ∀ mult_res,
               mult_rel add_res ⌊ o ⌋ mult_res
               → ∀ mult_res_2,
                 mult_rel ⌊ n ⌋ ⌊ o ⌋ mult_res_2
                 → ∀ mult_res_3,
                   mult_rel ⌊ m ⌋ ⌊ o ⌋ mult_res_3
                   → ∀ add_res_2, add_rel mult_res_3 mult_res_2 add_res_2 → mult_res == add_res_2)
            (let _: ∀ add_res,
                    add_rel
                    ⌊ mult
                      (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver))
                      (exist (λ (o : Nats_u), Nats_wf o ∧ True) o ltac:(solver)) ⌋
                    ⌊ mult
                      (exist (λ (n : Nats_u), Nats_wf n ∧ True) n ltac:(solver))
                      (exist (λ (o : Nats_u), Nats_wf o ∧ True) o ltac:(solver)) ⌋
                    add_res
                    → ∀ add_res_2,
                      add_rel o add_res add_res_2
                      → ∀ add_res_3,
                        add_rel
                        o
                        ⌊ mult
                          (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver))
                          (exist (λ (o : Nats_u), Nats_wf o ∧ True) o ltac:(solver)) ⌋
                        add_res_3
                        → ∀ add_res_4,
                          add_rel
                          add_res_3
                          ⌊ mult
                            (exist (λ (n : Nats_u), Nats_wf n ∧ True) n ltac:(solver))
                            (exist (λ (o : Nats_u), Nats_wf o ∧ True) o ltac:(solver)) ⌋
                          add_res_4
                          → add_res_2 == add_res_4 :=
             ⌈ add_assoc
               (exist (λ (o : Nats_u), Nats_wf o ∧ True) o ltac:(solver))
               (mult
                (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver))
                (exist (λ (o : Nats_u), Nats_wf o ∧ True) o ltac:(solver)))
               (mult
                (exist (λ (n : Nats_u), Nats_wf n ∧ True) n ltac:(solver))
                (exist (λ (o : Nats_u), Nats_wf o ∧ True) o ltac:(solver))) ⌉ in
             IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver) o ltac:(try clear IH_m; solver))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∀ add_res,
             add_rel ⌊ m ⌋ ⌊ n ⌋ add_res
             → ∀ mult_res,
               mult_rel add_res ⌊ o ⌋ mult_res
               → ∀ mult_res_2,
                 mult_rel ⌊ n ⌋ ⌊ o ⌋ mult_res_2
                 → ∀ mult_res_3,
                   mult_rel ⌊ m ⌋ ⌊ o ⌋ mult_res_3
                   → ∀ add_res_2, add_rel mult_res_3 mult_res_2 add_res_2 → mult_res == add_res_2)
            (# unit)
            ltac:(solver)).
Defined.

Definition one : Nats.
Proof.
  refine (Suc Zero).
Defined.

Inductive one_rel: Nats_u → Prop :=
  | one_Constr: one_rel (Suc_u Zero_u).

#[global] Hint Constructors one_rel: core_hint_db.

#[global] Instance one_lookup_rel: dictionary rel one := { lookup' := one_rel }.

#[global] Instance one_getF: getFunc one_rel := { getF' := one }.

Definition one_rel_funct : ∀ (VV VV' : Nats_u), one_rel VV → (one_rel VV' → VV = VV').
Proof.
  rel_functionhood_body.
Qed.

#[global] Hint Resolve one_rel_funct: f_rel_funct_db.

Theorem one_inv_lem one_inv_lem_res: one_rel one_inv_lem_res ↔ one_inv_lem_res == Suc_u Zero_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite one_inv_lem: f_rel_back.

Theorem one_rel_ex : one_rel ⌊ one ⌋.
Proof.
  existence_lemma_pre one;
  fix_notations;
  existence_lemma_quicksolve one;
  f__f_rel_ex_body;
  f_rel_finish.
Qed.

#[global] Hint Resolve one_rel_ex: rel_ax_db.

Opaque one.

Theorem one__one_rel_rw (VV : Nats_u): ⌊ one ⌋ = VV ↔ one_rel VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite one__one_rel_rw: f_rel_funct_db.

#[global] Hint Resolve one__one_rel_rw: rel_ax_db.

#[global] Instance one_lookup_rw: dictionary rwLem one := { lookup' := one__one_rel_rw }.

Theorem one__one_rel (VV : Nats_u): ⌊ one ⌋ = VV ↔ one_rel VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite one__one_rel: f_rel_funct_db.

Theorem one__one_rel' (VV : Nats_u): ⌊ one ⌋ = VV ↔ one_rel VV.
Proof.
  intros. refine (one__one_rel VV).
Qed.

#[global] Hint Resolve one__one_rel': f_rel_funct_db.

Definition one_rel_mk : {VV: _ | one_rel VV}.
Proof.
  intros; refine (subsumptionCast _ (λ VV, one_rel VV) one _); rewrite <- one__one_rel'; quicksolve.
Qed.

#[global] Hint Resolve one_rel_mk: f_rel_funct_db.

Definition sub
  (m : Nats) (n : {n: Nats_u | Nats_wf n ∧ ∀ geqN_res, geqN_rel ⌊ m ⌋ n geqN_res → is_true geqN_res}):
  {o: Nats_u | Nats_wf o ∧ (o ≠ Zero_u ↔ ⌊ m ⌋ ≠ ⌊ n ⌋)}.
Proof.
  destruct m as [m m_p].
  destruct n as [n n_p].
  try revert n_p; generalize dependent n; induction m as [m IH_m|]; intros.
  - destruct n as [n|].
    + refine (subsumptionCast
              Nats_u
              (λ (o : Nats_u), Nats_wf o ∧ (o ≠ Zero_u ↔ ⌊ m ⌋ ≠ ⌊ n ⌋))
              (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver))
              ltac:(solver)).
    + refine (subsumptionCast
              Nats_u
              (λ (o : Nats_u), Nats_wf o ∧ (o ≠ Zero_u ↔ ⌊ m ⌋ ≠ ⌊ n ⌋))
              (Suc (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver)))
              ltac:(solver)).
  - destruct n as [lq_anf7205759403792802899|].
    + intros; exfalso; solver.
    + refine (subsumptionCast
              Nats_u
              (λ (o : Nats_u), Nats_wf o ∧ (o ≠ Zero_u ↔ ⌊ m ⌋ ≠ ⌊ n ⌋))
              Zero
              ltac:(solver)).
Defined.

Inductive sub_rel: Nats_u → Nats_u → Nats_u → Prop :=
  | sub_Zero_Zero: sub_rel Zero_u Zero_u Zero_u
  | sub_Suc_Zero: ∀ m, sub_rel (Suc_u m) Zero_u (Suc_u m)
  | sub_Suc_Suc: ∀ m n sub_res, sub_rel m n sub_res → sub_rel (Suc_u m) (Suc_u n) sub_res.

#[global] Hint Constructors sub_rel: core_hint_db.

#[global] Instance sub_lookup_rel: dictionary rel sub := { lookup' := sub_rel }.

#[global] Instance sub_getF: getFunc sub_rel := { getF' := sub }.

Definition sub_rel_funct [m n : Nats_u]:
  ∀ (o o' : Nats_u), sub_rel m n o → (sub_rel m n o' → o = o').
Proof.
  try revert n_p; generalize dependent n; induction m as [m IH_m|]; intros;
  [destruct n as [n|] | destruct n as [lq_anf7205759403792802899|]];
  rel_functionhood_body.
Qed.

#[global] Hint Resolve sub_rel_funct: f_rel_funct_db.

Theorem sub_Zero_Zero_lem sub_Zero_Zero_lem_res:
  sub_rel Zero_u Zero_u sub_Zero_Zero_lem_res ↔ sub_Zero_Zero_lem_res == Zero_u.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite sub_Zero_Zero_lem: f_rel_back.

Theorem sub_Suc_Zero_lem m sub_Suc_Zero_lem_res:
  sub_rel (Suc_u m) Zero_u sub_Suc_Zero_lem_res ↔ sub_Suc_Zero_lem_res == Suc_u m.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite sub_Suc_Zero_lem: f_rel_back.

Theorem sub_Suc_Suc_lem m n sub_Suc_Suc_lem_res:
  sub_rel (Suc_u m) (Suc_u n) sub_Suc_Suc_lem_res
  ↔ ∃ sub_res, sub_rel m n sub_res ∧ sub_Suc_Suc_lem_res == sub_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite sub_Suc_Suc_lem: f_rel_back.

Theorem sub_rel_ex
  (m : Nats_u)
  (m_p : Nats_wf m ∧ True)
  (n : Nats_u)
  (n_p : Nats_wf n ∧ ∀ geqN_res, geqN_rel m n geqN_res → is_true geqN_res):
  sub_rel m n ⌊ sub (exist _ m m_p) (exist _ n n_p) ⌋.
Proof.
  existence_lemma_pre sub;
  try revert n_p; generalize dependent n; induction m as [m IH_m|]; intros;
  [destruct n as [n|];
   [fix_notations;
    pose proof (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver)) as IH_14792487;
    try clear IH_m |
    fix_notations] |
   destruct n as [lq_anf7205759403792802899|];
   [ | fix_notations]];
  existence_lemma_quicksolve sub;
  f__f_rel_ex_body;
  f_rel_finish.
Qed.

#[global] Hint Resolve sub_rel_ex: rel_ax_db.

Opaque sub.

Theorem sub__sub_rel_rw
  (m : Nats_u)
  (m_p : Nats_wf m ∧ True)
  (n : Nats_u)
  (n_p : Nats_wf n ∧ ∀ geqN_res, geqN_rel m n geqN_res → is_true geqN_res)
  (o : Nats_u):
  ⌊ sub (exist _ m m_p) (exist _ n n_p) ⌋ = o ↔ sub_rel m n o.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite sub__sub_rel_rw: f_rel_funct_db.

#[global] Hint Resolve sub__sub_rel_rw: rel_ax_db.

#[global] Instance sub_lookup_rw: dictionary rwLem sub := { lookup' := sub__sub_rel_rw }.

Theorem sub__sub_rel
  (m : Nats)
  (n : {n: Nats_u | Nats_wf n ∧ ∀ geqN_res, geqN_rel ⌊ m ⌋ n geqN_res → is_true geqN_res})
  (o : Nats_u):
  ⌊ sub m n ⌋ = o ↔ sub_rel ⌊ m ⌋ ⌊ n ⌋ o.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite sub__sub_rel: f_rel_funct_db.

Theorem sub__sub_rel'
  (m_u n_u : Nats_u)
  (m : Nats)
  (n : {n: Nats_u | Nats_wf n ∧ ∀ geqN_res, geqN_rel ⌊ m ⌋ n geqN_res → is_true geqN_res})
  (o : Nats_u):
  m_u = ⌊ m ⌋ → (n_u = ⌊ n ⌋ → ⌊ sub m n ⌋ = o ↔ sub_rel m_u n_u o).
Proof.
  intros -> ->. refine (sub__sub_rel m n o).
Qed.

#[global] Hint Resolve sub__sub_rel': f_rel_funct_db.

Definition sub_rel_mk
  (m : Nats_u)
  (m_p : Nats_wf m ∧ True)
  (n : Nats_u)
  (n_p : Nats_wf n ∧ ∀ geqN_res, geqN_rel m n geqN_res → is_true geqN_res):
  {o: _ | sub_rel m n o}.
Proof.
  intros;
  refine (subsumptionCast _ (λ o, sub_rel m n o) (sub (exist _ m m_p) (exist _ n n_p)) _);
  rewrite <- sub__sub_rel';
  quicksolve.
Qed.

#[global] Hint Resolve sub_rel_mk: f_rel_funct_db.

#[global] Instance sub_pack:
  @Pack
  (Nats
   ::RT λ (m : Nats),
        {n: Nats_u | Nats_wf n ∧ ∀ geqN_res, geqN_rel ⌊ m ⌋ n geqN_res → is_true geqN_res}
        ::RT λ (n : {n: Nats_u | Nats_wf n ∧ ∀ geqN_res, geqN_rel ⌊ m ⌋ n geqN_res → is_true geqN_res}),
             nilRT)
  (Nats_u ::UT (Nats_u ::UT nilUT))
  ltac:(mkProjectsArgListTG ((Nats
  ::RT λ (m : Nats),
       {n: Nats_u | Nats_wf n
                    ∧ ∀ geqN_res, geqN_rel ⌊ m ⌋ n geqN_res → is_true geqN_res}
       ::RT λ (n : {n: Nats_u | Nats_wf n
                                ∧ ∀ geqN_res, geqN_rel ⌊ m ⌋ n geqN_res → is_true geqN_res}),
            nilRT)) ((Nats_u ::UT (Nats_u ::UT nilUT))))
  Nats_u
  (λ (x_19226769 : ArgList (Nats
                            ::RT λ (m : Nats),
                                 {n: Nats_u | Nats_wf n ∧ ∀ geqN_res, geqN_rel ⌊ m ⌋ n geqN_res → is_true geqN_res}
                                 ::RT λ (n : {n: Nats_u | Nats_wf n
                                                          ∧ ∀ geqN_res, geqN_rel ⌊ m ⌋ n geqN_res → is_true geqN_res}),
                                      nilRT))
     (v_x_19226769 : Nats_u),
   ltac:(flattenP (λ (m : Nats)
   (n : {n: Nats_u | Nats_wf n
                     ∧ ∀ geqN_res, geqN_rel ⌊ m ⌋ n geqN_res → is_true geqN_res})
   (o : Nats_u),
 Nats_wf o ∧ (o ≠ Zero_u ↔ ⌊ m ⌋ ≠ ⌊ n ⌋)) x_19226769 v_x_19226769)).
Proof.
  buildPackG sub sub_rel sub__sub_rel sub_rel_funct.
Defined.

#[global] Instance sub_upack: @uPack (Nats_u ::UT (Nats_u ::UT nilUT)) Nats_u.
Proof.
  buildUPackG sub_rel sub_rel_funct.
Defined.

Definition add_sub (m n : Nats):
  {{∀ add_res,
    add_rel ⌊ m ⌋ ⌊ n ⌋ add_res → ∀ sub_res, sub_rel add_res ⌊ n ⌋ sub_res → sub_res == ⌊ m ⌋}}.
Proof.
  destruct m as [m m_p].
  destruct n as [n n_p].
  destruct m as [m|].
  - induction n as [lq_anf7205759403792802869 IH_lq_anf7205759403792802869|].
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∀ add_res,
               add_rel ⌊ m ⌋ ⌊ n ⌋ add_res → ∀ sub_res, sub_rel add_res ⌊ n ⌋ sub_res → sub_res == ⌊ m ⌋)
              (let _: ∀ add_res,
                      add_rel (Suc_u m) lq_anf7205759403792802869 add_res
                      → ∀ sub_res, sub_rel add_res lq_anf7205759403792802869 sub_res → sub_res == Suc_u m :=
               ⌈ IH_lq_anf7205759403792802869 ltac:(try clear IH_lq_anf7205759403792802869; solver) ⌉ in
               add_suc_r
               (Suc (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver)))
               (exist (λ (n : Nats_u), Nats_wf n ∧ True) lq_anf7205759403792802869 ltac:(solver)))
              ltac:(solver)).
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∀ add_res,
               add_rel ⌊ m ⌋ ⌊ n ⌋ add_res → ∀ sub_res, sub_rel add_res ⌊ n ⌋ sub_res → sub_res == ⌊ m ⌋)
              (add_zero_r (exist (λ (n : Nats_u), Nats_wf n ∧ True) m ltac:(solver)))
              ltac:(solver)).
  - induction n as [lq_anf7205759403792802861 IH_lq_anf7205759403792802861|].
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∀ add_res,
               add_rel ⌊ m ⌋ ⌊ n ⌋ add_res → ∀ sub_res, sub_rel add_res ⌊ n ⌋ sub_res → sub_res == ⌊ m ⌋)
              (let _: ∀ add_res,
                      add_rel Zero_u lq_anf7205759403792802861 add_res
                      → ∀ sub_res, sub_rel add_res lq_anf7205759403792802861 sub_res → sub_res == Zero_u :=
               ⌈ IH_lq_anf7205759403792802861 ltac:(try clear IH_lq_anf7205759403792802861; solver) ⌉ in
               add_suc_r Zero (exist (λ (n : Nats_u), Nats_wf n ∧ True) lq_anf7205759403792802861 ltac:(solver)))
              ltac:(solver)).
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∀ add_res,
               add_rel ⌊ m ⌋ ⌊ n ⌋ add_res → ∀ sub_res, sub_rel add_res ⌊ n ⌋ sub_res → sub_res == ⌊ m ⌋)
              (# unit)
              ltac:(solver)).
Defined.

Definition sub_self (m n : Nats):
  {{∀ eqN_res,
    eqN_rel ⌊ m ⌋ ⌊ n ⌋ eqN_res
    → ∀ sub_res, sub_rel ⌊ m ⌋ ⌊ n ⌋ sub_res → (is_true eqN_res → sub_res == Zero_u)}}.
Proof.
  destruct m as [m m_p].
  destruct n as [n n_p].
  try revert n_p; generalize dependent n; induction m as [m IH_m|]; intros.
  - destruct n as [n|].
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∀ eqN_res,
               eqN_rel ⌊ m ⌋ ⌊ n ⌋ eqN_res
               → ∀ sub_res, sub_rel ⌊ m ⌋ ⌊ n ⌋ sub_res → (is_true eqN_res → sub_res == Zero_u))
              (IH_m ltac:(try clear IH_m; solver) n ltac:(try clear IH_m; solver))
              ltac:(solver)).
    + refine (subsumptionCast
              Unit
              (λ (VV : Unit),
               ∀ eqN_res,
               eqN_rel ⌊ m ⌋ ⌊ n ⌋ eqN_res
               → ∀ sub_res, sub_rel ⌊ m ⌋ ⌊ n ⌋ sub_res → (is_true eqN_res → sub_res == Zero_u))
              (# unit)
              ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∀ eqN_res,
             eqN_rel ⌊ m ⌋ ⌊ n ⌋ eqN_res
             → ∀ sub_res, sub_rel ⌊ m ⌋ ⌊ n ⌋ sub_res → (is_true eqN_res → sub_res == Zero_u))
            (# unit)
            ltac:(solver)).
Defined.

Definition two : Nats.
Proof.
  refine (Suc one).
Defined.

Inductive two_rel: Nats_u → Prop :=
  | two_Constr: ∀ one_res, one_rel one_res → two_rel (Suc_u one_res).

#[global] Hint Constructors two_rel: core_hint_db.

#[global] Instance two_lookup_rel: dictionary rel two := { lookup' := two_rel }.

#[global] Instance two_getF: getFunc two_rel := { getF' := two }.

Definition two_rel_funct : ∀ (VV VV' : Nats_u), two_rel VV → (two_rel VV' → VV = VV').
Proof.
  rel_functionhood_body.
Qed.

#[global] Hint Resolve two_rel_funct: f_rel_funct_db.

Theorem two_inv_lem two_inv_lem_res:
  two_rel two_inv_lem_res ↔ ∃ one_res, one_rel one_res ∧ two_inv_lem_res == Suc_u one_res.
Proof.
  rel_back' _nil.
Qed.

#[global] Hint Rewrite two_inv_lem: f_rel_back.

Theorem two_rel_ex : two_rel ⌊ two ⌋.
Proof.
  existence_lemma_pre two;
  fix_notations;
  existence_lemma_quicksolve two;
  f__f_rel_ex_body;
  f_rel_finish.
Qed.

#[global] Hint Resolve two_rel_ex: rel_ax_db.

Opaque two.

Theorem two__two_rel_rw (VV : Nats_u): ⌊ two ⌋ = VV ↔ two_rel VV.
Proof.
  f__f_rel_rw.
Qed.

#[global] Hint Rewrite two__two_rel_rw: f_rel_funct_db.

#[global] Hint Resolve two__two_rel_rw: rel_ax_db.

#[global] Instance two_lookup_rw: dictionary rwLem two := { lookup' := two__two_rel_rw }.

Theorem two__two_rel (VV : Nats_u): ⌊ two ⌋ = VV ↔ two_rel VV.
Proof.
  f__f_rel.
Qed.

#[global] Hint Rewrite two__two_rel: f_rel_funct_db.

Theorem two__two_rel' (VV : Nats_u): ⌊ two ⌋ = VV ↔ two_rel VV.
Proof.
  intros. refine (two__two_rel VV).
Qed.

#[global] Hint Resolve two__two_rel': f_rel_funct_db.

Definition two_rel_mk : {VV: _ | two_rel VV}.
Proof.
  intros; refine (subsumptionCast _ (λ VV, two_rel VV) two _); rewrite <- two__two_rel'; quicksolve.
Qed.

#[global] Hint Resolve two_rel_mk: f_rel_funct_db.
=======
Definition add_dist_rmult_spec (m: Nats) (n: Nats) (o: Nats): Type := 
	{{forall (addres: Nats_u), (add_rel (⌊ m -⌋) (⌊ n -⌋) addres) -> (forall (multres: Nats_u), (mult_rel addres (⌊ o -⌋) multres) -> (forall (mult_res_2: Nats_u), (mult_rel (⌊ n -⌋) (⌊ o -⌋) mult_res_2) -> (forall (mult_res_3: Nats_u), (mult_rel (⌊ m -⌋) (⌊ o -⌋) mult_res_3) -> (forall (add_res_2: Nats_u), (add_rel mult_res_3 mult_res_2 add_res_2) -> (multres == add_res_2)))))}}. 
#[global] Hint Unfold add_dist_rmult_spec : lia_unfold.
Theorem add_dist_rmult (m: Nats) (n: Nats) (o: Nats): add_dist_rmult_spec m n o. 
Proof. 
	destruct m as [m m_p]. 
	destruct n as [n n_p]. 
	destruct o as [o o_p]. 
	try revert o_p; generalize dependent o; try revert n_p; generalize dependent n; 
	induction m as [(*Suc*) m IH_m | (*Zero*) ]. 
	  - intros . 
		pose proof (add_assoc 
		(exist (fun (m: Nats_u) => ((Nats_wf m) /\ True)) o (ltac: (solver))) 
		(subsumptionCast Nats_u (fun (n: Nats_u) => ((Nats_wf n) /\ True)) 
		(mult 
		(exist (fun (m: Nats_u) => ((Nats_wf m) /\ True)) m (ltac: (solver))) 
		(exist (fun (n: Nats_u) => ((Nats_wf n) /\ True)) o (ltac: (solver)))) (ltac: (solver))) 
		(subsumptionCast Nats_u (fun (o: Nats_u) => ((Nats_wf o) /\ True)) 
		(mult 
		(exist (fun (m: Nats_u) => ((Nats_wf m) /\ True)) n (ltac: (solver))) 
		(exist (fun (n: Nats_u) => ((Nats_wf n) /\ True)) o (ltac: (solver)))) (ltac: (solver)))) as H_77751195. 
		simpl in H_77751195. 
		refine (subsumptionCast _ _ 
		(IH_m (ltac: (try clear IH_m; 
	solver)) n (ltac: (try clear IH_m; 
	solver)) o (ltac: (try clear IH_m; 
	solver))) _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
Qed. 
Definition one_spec: Type := 
	Nats. 
#[global] Hint Unfold one_spec : lia_unfold.
Definition one: one_spec. 
Proof. 
	refine (subsumptionCast _ _ 
		(Suc 
		(subsumptionCast Nats_u (fun (n: Nats_u) => ((Nats_wf n) /\ True)) Zero (ltac: (solver)))) _); 
	solver. 
Defined. 
Inductive one_rel : (Nats_u -> Prop) := 
	 | one_def: one_rel (Suc_u Zero_u). 
#[global] Hint Constructors one_rel : core_hint_db.
#[global] Instance one_lookup_rel : dictionary rel one := { 
	lookup' := one_rel
}.
#[global] Instance one_getF : getFunc one_rel := { 
	getF' := one
}.
Theorem one_rel_funct: (forall (VV: Nats_u) (VV': Nats_u) (H: one_rel VV) (K: one_rel VV') , VV = VV'). 
Proof. 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve one_rel_funct : f_rel_funct_db.
Theorem one_def_lem: (one_rel (Suc_u Zero_u)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite one_def_lem : f_rel_back.
Theorem one_rel_ex: one_rel (⌊ one -⌋). 
Proof. 
	Opaque one.
	existence_lemma_pre one; 
	fix_notations; 
	simpl in *. 
	Transparent one.
	all: existence_lemma_quicksolve one; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve one_rel_ex : rel_ax_db.
#[global] Opaque one. 
Theorem one__one_rel_rw (VV: Nats_u): ((⌊ one -⌋) = VV) <-> (one_rel VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite one__one_rel_rw : f_rel_funct_db.
#[global] Hint Resolve one__one_rel_rw : rel_ax_db.
#[global] Instance one_lookup_rw : dictionary rwLem one := { 
	lookup' := one__one_rel_rw
}.
Theorem one__one_rel (VV: Nats_u): ((⌊ one -⌋) = VV) <-> (one_rel VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite one__one_rel : f_rel_funct_db.
Theorem one__one_rel' (VV: Nats_u): ((⌊ one -⌋) = VV) <-> (one_rel VV). 
Proof. 
	intros . 
	refine (one__one_rel VV). 
Qed. 
#[global] Hint Resolve one__one_rel' : f_rel_funct_db.
Theorem one_rel_mk: {VV: _ | one_rel VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (one_rel VV)) one _); 
	rewrite <- one__one_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve one_rel_mk : f_rel_funct_db.
Definition sub_self_spec (m: Nats) (n: Nats): Type := 
	{{forall (eqNres: bool), (eqN_rel (⌊ m -⌋) (⌊ n -⌋) eqNres) -> (forall (PeanoNats__subres: Nats_u), (PeanoNats__sub_rel (⌊ m -⌋) (⌊ n -⌋) PeanoNats__subres) -> ((is_true eqNres) -> (PeanoNats__subres = Zero_u)))}}. 
#[global] Hint Unfold sub_self_spec : lia_unfold.
Theorem sub_self (m: Nats) (n: Nats): sub_self_spec m n. 
Proof. 
	destruct m as [m m_p]. 
	destruct n as [n n_p]. 
	try revert n_p; generalize dependent n; 
	induction m as [(*Suc*) m IH_m | (*Zero*) ]. 
	  - intros . 
		induction n as [(*Suc*) n IH_n | (*Zero*) ]. 
		  -- intros . 
			refine (subsumptionCast _ _ 
		(IH_m (ltac: (try clear IH_m; 
	solver)) n (ltac: (try clear IH_m; 
	solver))) _); 
			solver.  
		  -- intros . 
			refine (exist _ unit _); 
			solver.   
	  - intros . 
		refine (exist _ unit _); 
		solver.  
Qed. 
Definition two_spec: Type := 
	Nats. 
#[global] Hint Unfold two_spec : lia_unfold.
Definition two: two_spec. 
Proof. 
	refine (subsumptionCast _ _ 
		(Suc 
		(subsumptionCast Nats_u (fun (n: Nats_u) => ((Nats_wf n) /\ True)) one (ltac: (solver)))) _); 
	solver. 
Defined. 
Inductive two_rel : (Nats_u -> Prop) := 
	 | two_def: two_rel (Suc_u (⌊ one -⌋)). 
#[global] Hint Constructors two_rel : core_hint_db.
#[global] Instance two_lookup_rel : dictionary rel two := { 
	lookup' := two_rel
}.
#[global] Instance two_getF : getFunc two_rel := { 
	getF' := two
}.
Theorem two_rel_funct: (forall (VV: Nats_u) (VV': Nats_u) (H: two_rel VV) (K: two_rel VV') , VV = VV'). 
Proof. 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve two_rel_funct : f_rel_funct_db.
Theorem two_def_lem: (two_rel (Suc_u (⌊ one -⌋))) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite two_def_lem : f_rel_back.
Theorem two_rel_ex: two_rel (⌊ two -⌋). 
Proof. 
	Opaque two.
	existence_lemma_pre two; 
	fix_notations; 
	simpl in *. 
	Transparent two.
	all: existence_lemma_quicksolve two; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve two_rel_ex : rel_ax_db.
#[global] Opaque two. 
Theorem two__two_rel_rw (VV: Nats_u): ((⌊ two -⌋) = VV) <-> (two_rel VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite two__two_rel_rw : f_rel_funct_db.
#[global] Hint Resolve two__two_rel_rw : rel_ax_db.
#[global] Instance two_lookup_rw : dictionary rwLem two := { 
	lookup' := two__two_rel_rw
}.
Theorem two__two_rel (VV: Nats_u): ((⌊ two -⌋) = VV) <-> (two_rel VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite two__two_rel : f_rel_funct_db.
Theorem two__two_rel' (VV: Nats_u): ((⌊ two -⌋) = VV) <-> (two_rel VV). 
Proof. 
	intros . 
	refine (two__two_rel VV). 
Qed. 
#[global] Hint Resolve two__two_rel' : f_rel_funct_db.
Theorem two_rel_mk: {VV: _ | two_rel VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (two_rel VV)) two _); 
	rewrite <- two__two_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve two_rel_mk : f_rel_funct_db.
>>>>>>> 30f5ad28b2b58d4cd36512b224803724fd1a0050
