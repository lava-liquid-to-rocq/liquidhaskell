From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Inductive Nats_u : Set := 
	 | Suc_u: Nats_u -> Nats_u
	 | Zero_u: Nats_u. 
Fixpoint Nats_eq (x: Nats_u) (y: Nats_u): bool := 
	match (x, y) with (Suc_u x, Suc_u x') => (true && (Nats_eq x x')) | (Zero_u, Zero_u) => true | (_, _) => false end. 
Definition Nats_eq_refl: (forall (x: Nats_u) , is_true (Nats_eq x x)). 
Proof. 
	eq_refl. 
Qed. 
#[global] Hint Resolve Nats_eq_refl : eq_hint_db.
Definition Nats_eqb_eq: (forall (s: Nats_u) (t: Nats_u) , (is_true (Nats_eq s t)) -> (s = t)). 
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
Definition add (m: Nats) (n: Nats): Nats. 
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
Definition add_rel_funct [m: Nats_u] [n: Nats_u]: (forall (VV: Nats_u) (VV': Nats_u) (H: add_rel m n VV) (K: add_rel m n VV') , VV = VV'). 
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
	existence_lemma_quicksolve add; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve add_rel_ex : rel_ax_db.
Opaque add. 
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
Definition add_rel_mk [m: Nats_u] [n: Nats_u] (m_p: (Nats_wf m) /\ True) (n_p: (Nats_wf n) /\ True): {VV: _ | add_rel m n VV}. 
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
Definition add' (m: Nats) (n: Nats): {v: Nats_u | (Nats_wf v) /\ (forall (addres: Nats_u), (add_rel (⌊ m -⌋) (⌊ n -⌋) addres) -> (forall (add_res_2: Nats_u), (add_rel addres Zero_u add_res_2) -> (add_res_2 == v)))}. 
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
Definition add'' (m: Nats) (n: Nats): {v: Nats_u | (Nats_wf v) /\ (forall (addres: Nats_u), (add_rel (⌊ m -⌋) (⌊ n -⌋) addres) -> (addres == v))}. 
Proof. 
	destruct m as [m m_p]. 
	destruct n as [n n_p]. 
	refine (subsumptionCast _ _ 
		(add 
		(exist (fun (m: Nats_u) => ((Nats_wf m) /\ True)) m (ltac: (solver))) 
		(exist (fun (n: Nats_u) => ((Nats_wf n) /\ True)) n (ltac: (solver)))) _); 
	solver. 
Defined. 
Definition add_assoc (m: Nats) (n: Nats) (o: Nats): {{forall (addres: Nats_u), (add_rel (⌊ n -⌋) (⌊ o -⌋) addres) -> (forall (add_res_2: Nats_u), (add_rel (⌊ m -⌋) addres add_res_2) -> (forall (add_res_3: Nats_u), (add_rel (⌊ m -⌋) (⌊ n -⌋) add_res_3) -> (forall (add_res_4: Nats_u), (add_rel add_res_3 (⌊ o -⌋) add_res_4) -> (add_res_2 == add_res_4))))}}. 
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
Defined. 
Definition add_suc_r (m: Nats) (n: Nats): {{forall (addres: Nats_u), (add_rel (⌊ m -⌋) (⌊ n -⌋) addres) -> (forall (add_res_2: Nats_u), (add_rel (⌊ m -⌋) (Suc_u (⌊ n -⌋)) add_res_2) -> ((Suc_u addres) == add_res_2))}}. 
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
Defined. 
Definition add_zero_l (n: Nats): {{forall (addres: Nats_u), (add_rel Zero_u (⌊ n -⌋) addres) -> (addres = (⌊ n -⌋))}}. 
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
Defined. 
Definition add_zero_l_test: {{forall (addres: Nats_u), (add_rel Zero_u (Suc_u (Suc_u Zero_u)) addres) -> (addres == (Suc_u (Suc_u Zero_u)))}}. 
Proof. 
	refine (subsumptionCast _ _ 
		(add_zero_l 
		(subsumptionCast Nats_u (fun (n: Nats_u) => ((Nats_wf n) /\ True)) 
		(Suc 
		(subsumptionCast Nats_u (fun (n: Nats_u) => ((Nats_wf n) /\ True)) 
		(Suc 
		(subsumptionCast Nats_u (fun (n: Nats_u) => ((Nats_wf n) /\ True)) Zero (ltac: (solver)))) (ltac: (solver)))) (ltac: (solver)))) _); 
	solver. 
Defined. 
Definition add_zero_r (n: Nats): {{forall (addres: Nats_u), (add_rel (⌊ n -⌋) Zero_u addres) -> (addres = (⌊ n -⌋))}}. 
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
Defined. 
Definition eqN (m: Nats) (n: Nats): Bool. 
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
		induction n as [(*Suc*) lq_anf7205759403792805258 IH_lq_anf7205759403792805258 | (*Zero*) ]. 
		  -- intros . 
			refine (exist _ false _); 
			solver.  
		  -- intros . 
			refine (exist _ true _); 
			solver.   
Defined. 
Inductive eqN_rel : (Nats_u -> (Nats_u -> (bool -> Prop))) := 
	 | eqN_Zero_Zero: eqN_rel Zero_u Zero_u true
	 | eqN_Zero_Suc: (forall lq_anf7205759403792805258 , eqN_rel Zero_u (Suc_u lq_anf7205759403792805258) false)
	 | eqN_Suc_Zero: (forall m , eqN_rel (Suc_u m) Zero_u false)
	 | eqN_Suc_Suc: (forall m n , forall (eqNres: bool), (eqN_rel m n eqNres) -> (eqN_rel (Suc_u m) (Suc_u n) eqNres)). 
#[global] Hint Constructors eqN_rel : core_hint_db.
#[global] Instance eqN_lookup_rel : dictionary rel eqN := { 
	lookup' := eqN_rel
}.
#[global] Instance eqN_getF : getFunc eqN_rel := { 
	getF' := eqN
}.
Definition eqN_rel_funct [m: Nats_u] [n: Nats_u]: (forall (VV: bool) (VV': bool) (H: eqN_rel m n VV) (K: eqN_rel m n VV') , VV = VV'). 
Proof. 
	try revert n_p; generalize dependent n; 
	induction m as [(*Suc*) m IH_m | (*Zero*) ]; 
	intros ; 
	[induction n as [(*Suc*) n IH_n | (*Zero*) ]; 
	intros | 
	induction n as [(*Suc*) lq_anf7205759403792805258 IH_lq_anf7205759403792805258 | (*Zero*) ]; 
	intros ]; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve eqN_rel_funct : f_rel_funct_db.
Theorem eqN_Zero_Zero_lem: (eqN_rel Zero_u Zero_u true) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite eqN_Zero_Zero_lem : f_rel_back.
Theorem eqN_Zero_Suc_lem (lq_anf7205759403792805258: _): (eqN_rel Zero_u (Suc_u lq_anf7205759403792805258) false) <-> True. 
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
	induction n as [(*Suc*) lq_anf7205759403792805258 IH_lq_anf7205759403792805258 | (*Zero*) ]; 
	intros ; 
	[fix_notations; 
	try clear IH_lq_anf7205759403792805258| 
	fix_notations]]; 
	existence_lemma_quicksolve eqN; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve eqN_rel_ex : rel_ax_db.
Opaque eqN. 
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
Definition eqN_rel_mk [m: Nats_u] [n: Nats_u] (m_p: (Nats_wf m) /\ True) (n_p: (Nats_wf n) /\ True): {VV: _ | eqN_rel m n VV}. 
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
Definition test_eqN: {r: bool | is_true r}. 
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
Definition test_eqN': {r: bool | not (is_true r)}. 
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
Definition geqN (m: Nats) (n: Nats): Bool. 
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
Definition geqN_rel_funct [m: Nats_u] [n: Nats_u]: (forall (VV: bool) (VV': bool) (H: geqN_rel m n VV) (K: geqN_rel m n VV') , VV = VV'). 
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
	existence_lemma_quicksolve geqN; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve geqN_rel_ex : rel_ax_db.
Opaque geqN. 
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
Definition geqN_rel_mk [m: Nats_u] [n: Nats_u] (m_p: (Nats_wf m) /\ True) (n_p: (Nats_wf n) /\ True): {VV: _ | geqN_rel m n VV}. 
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
Definition PeanoNats__sub (m: Nats) (n: {n: Nats_u | (Nats_wf n) /\ (geqN_rel (⌊ m -⌋) n true)}): {o: Nats_u | (Nats_wf o) /\ ((o <> Zero_u) <-> ((⌊ m -⌋) <> (⌊ n -⌋)))}. 
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
		induction n as [(*Suc*) lq_anf7205759403792805274 IH_lq_anf7205759403792805274 | (*Zero*) ]. 
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
Definition PeanoNats__sub_rel_funct [m: Nats_u] [n: Nats_u]: (forall (o: Nats_u) (o': Nats_u) (H: PeanoNats__sub_rel m n o) (K: PeanoNats__sub_rel m n o') , o = o'). 
Proof. 
	try revert n_p; generalize dependent n; 
	induction m as [(*Suc*) m IH_m | (*Zero*) ]; 
	intros ; 
	[induction n as [(*Suc*) n IH_n | (*Zero*) ]; 
	intros | 
	induction n as [(*Suc*) lq_anf7205759403792805274 IH_lq_anf7205759403792805274 | (*Zero*) ]; 
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
	induction n as [(*Suc*) lq_anf7205759403792805274 IH_lq_anf7205759403792805274 | (*Zero*) ]; 
	intros ; 
	[fix_notations; 
	try clear IH_lq_anf7205759403792805274| 
	fix_notations]]; 
	existence_lemma_quicksolve PeanoNats__sub; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve PeanoNats__sub_rel_ex : rel_ax_db.
Opaque PeanoNats__sub. 
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
Definition PeanoNats__sub_rel_mk [m: Nats_u] [n: Nats_u] (m_p: (Nats_wf m) /\ True) (n_p: (Nats_wf n) /\ (geqN_rel m n true)): {o: _ | PeanoNats__sub_rel m n o}. 
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
Definition add_sub (m: Nats) (n: Nats): {{forall (addres: Nats_u), (add_rel (⌊ m -⌋) (⌊ n -⌋) addres) -> (forall (PeanoNats__subres: Nats_u), (PeanoNats__sub_rel addres (⌊ n -⌋) PeanoNats__subres) -> (PeanoNats__subres = (⌊ m -⌋)))}}. 
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
			fix_notations. 
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
			fix_notations. 
			refine (subsumptionCast _ _ 
		(add_suc_r 
		(subsumptionCast Nats_u (fun (m: Nats_u) => ((Nats_wf m) /\ True)) Zero (ltac: (solver))) 
		(exist (fun (n: Nats_u) => ((Nats_wf n) /\ True)) n (ltac: (solver)))) _); 
			solver.  
		  -- intros . 
			refine (exist _ unit _); 
			solver.   
Defined. 
Definition mult (m: Nats) (n: Nats): Nats. 
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
Definition mult_rel_funct [m: Nats_u] [n: Nats_u]: (forall (VV: Nats_u) (VV': Nats_u) (H: mult_rel m n VV) (K: mult_rel m n VV') , VV = VV'). 
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
	existence_lemma_quicksolve mult; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve mult_rel_ex : rel_ax_db.
Opaque mult. 
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
Definition mult_rel_mk [m: Nats_u] [n: Nats_u] (m_p: (Nats_wf m) /\ True) (n_p: (Nats_wf n) /\ True): {VV: _ | mult_rel m n VV}. 
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
Definition add_dist_rmult (m: Nats) (n: Nats) (o: Nats): {{forall (addres: Nats_u), (add_rel (⌊ m -⌋) (⌊ n -⌋) addres) -> (forall (multres: Nats_u), (mult_rel addres (⌊ o -⌋) multres) -> (forall (mult_res_2: Nats_u), (mult_rel (⌊ n -⌋) (⌊ o -⌋) mult_res_2) -> (forall (mult_res_3: Nats_u), (mult_rel (⌊ m -⌋) (⌊ o -⌋) mult_res_3) -> (forall (add_res_2: Nats_u), (add_rel mult_res_3 mult_res_2 add_res_2) -> (multres == add_res_2)))))}}. 
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
		fix_notations. 
		refine (subsumptionCast _ _ 
		(IH_m (ltac: (try clear IH_m; 
	solver)) n (ltac: (try clear IH_m; 
	solver)) o (ltac: (try clear IH_m; 
	solver))) _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
Defined. 
Definition one: Nats. 
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
Definition one_rel_funct: (forall (VV: Nats_u) (VV': Nats_u) (H: one_rel VV) (K: one_rel VV') , VV = VV'). 
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
	existence_lemma_pre one; 
	fix_notations; 
	existence_lemma_quicksolve one; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve one_rel_ex : rel_ax_db.
Opaque one. 
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
Definition one_rel_mk: {VV: _ | one_rel VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (one_rel VV)) one _); 
	rewrite <- one__one_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve one_rel_mk : f_rel_funct_db.
Definition sub_self (m: Nats) (n: Nats): {{forall (eqNres: bool), (eqN_rel (⌊ m -⌋) (⌊ n -⌋) eqNres) -> (forall (PeanoNats__subres: Nats_u), (PeanoNats__sub_rel (⌊ m -⌋) (⌊ n -⌋) PeanoNats__subres) -> ((is_true eqNres) -> (PeanoNats__subres = Zero_u)))}}. 
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
Defined. 
Definition two: Nats. 
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
Definition two_rel_funct: (forall (VV: Nats_u) (VV': Nats_u) (H: two_rel VV) (K: two_rel VV') , VV = VV'). 
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
	existence_lemma_pre two; 
	fix_notations; 
	existence_lemma_quicksolve two; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve two_rel_ex : rel_ax_db.
Opaque two. 
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
Definition two_rel_mk: {VV: _ | two_rel VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (two_rel VV)) two _); 
	rewrite <- two__two_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve two_rel_mk : f_rel_funct_db.