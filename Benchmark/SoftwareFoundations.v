From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Set Universe Polymorphism.
Inductive SFBool_u : Type := 
	 | SFFalse_u: SFBool_u
	 | SFTrue_u: SFBool_u. 
Fixpoint SFBool_eq (x: SFBool_u) (y: SFBool_u): bool := 
	match (x, y) with (SFFalse_u, SFFalse_u) => true | (SFTrue_u, SFTrue_u) => true | (_, _) => false end. 
Theorem SFBool_eq_refl: (forall (x: SFBool_u) , is_true (SFBool_eq x x)). 
Proof. 
	eq_refl_rec. 
Qed. 
#[global] Hint Resolve SFBool_eq_refl : eq_hint_db.
Theorem SFBool_eqb_eq: (forall (s: SFBool_u) (t: SFBool_u) , (is_true (SFBool_eq s t)) -> (s = t)). 
Proof. 
	eqb_eq_lem. 
Qed. 
#[global] Hint Resolve SFBool_eqb_eq : eq_hint_db.
#[global] Instance leibnitz_eq_SFBool : LeibnitzEqB := { 
	equalB' := SFBool_eq;
	refl' := SFBool_eq_refl;
	eqb_eq' := SFBool_eqb_eq
}.
Fixpoint SFBool_wf (x: SFBool_u): Prop := 
	match x with SFFalse_u => True | SFTrue_u => True end. 
Theorem SFBool_wf_ref [p: SFBool_u -> Prop] (tm: {v: SFBool_u | (SFBool_wf v) /\ (p v)}): SFBool_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation SFBool := {x: SFBool_u | (SFBool_wf x) /\ True}. 
Definition SFFalse_lem: (SFBool_wf SFFalse_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition SFFalse: SFBool := 
	exist _ SFFalse_u SFFalse_lem. 
Definition SFTrue_lem: (SFBool_wf SFTrue_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition SFTrue: SFBool := 
	exist _ SFTrue_u SFTrue_lem. 
#[global] Hint Resolve SFBool_wf_ref : wf_constr_db.
#[global] Hint Unfold SFBool_wf : wf_constr_db.
#[global] Hint Resolve SFBool_eq : ref_constr_db.
#[global] Hint Unfold SFFalse : ref_constr_db.
#[global] Hint Unfold SFTrue : ref_constr_db.
Definition andb_spec (b1: SFBool) (b2: SFBool): Type := 
	SFBool. 
#[global] Hint Unfold andb_spec : lia_unfold.
Definition andb (b1: SFBool) (b2: SFBool): andb_spec b1 b2. 
Proof. 
	destruct b1 as [b1 b1_p]. 
	destruct b2 as [b2 b2_p]. 
	try revert b2_p; generalize dependent b2; 
	induction b1 as [(*SFFalse*)  | (*SFTrue*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ SFFalse _); 
		solver.  
	  - intros . 
		refine (exist _ b2 _); 
		solver.  
Defined. 
Inductive andb_rel : (SFBool_u -> (SFBool_u -> (SFBool_u -> Prop))) := 
	 | andb_SFTrue: (forall b2 , andb_rel SFTrue_u b2 b2)
	 | andb_SFFalse: (forall b2 , andb_rel SFFalse_u b2 SFFalse_u). 
#[global] Hint Constructors andb_rel : core_hint_db.
#[global] Instance andb_lookup_rel : dictionary rel andb := { 
	lookup' := andb_rel
}.
#[global] Instance andb_getF : getFunc andb_rel := { 
	getF' := andb
}.
Theorem andb_rel_funct [b1: SFBool_u] [b2: SFBool_u]: (forall (VV: SFBool_u) (VV': SFBool_u) (H: andb_rel b1 b2 VV) (K: andb_rel b1 b2 VV') , VV = VV'). 
Proof. 
	try revert b2_p; generalize dependent b2; 
	destruct b1 as [(*SFFalse*)  | (*SFTrue*) ]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve andb_rel_funct : f_rel_funct_db.
Theorem andb_SFTrue_lem (b2: _): (andb_rel SFTrue_u b2 b2) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite andb_SFTrue_lem : f_rel_back.
Theorem andb_SFFalse_lem (b2: _): (andb_rel SFFalse_u b2 SFFalse_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite andb_SFFalse_lem : f_rel_back.
Theorem andb_rel_ex (b1: SFBool_u) (b2: SFBool_u) (b1_p: (SFBool_wf b1) /\ True) (b2_p: (SFBool_wf b2) /\ True): andb_rel b1 b2 (⌊ andb (exist _ b1 b1_p) (exist _ b2 b2_p) -⌋). 
Proof. 
	Opaque andb.
	existence_lemma_pre andb; 
	try revert b2_p; generalize dependent b2; 
	destruct b1 as [(*SFFalse*)  | (*SFTrue*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations]; 
	simpl in *. 
	Transparent andb.
	all: existence_lemma_quicksolve andb; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve andb_rel_ex : rel_ax_db.
#[global] Opaque andb. 
Theorem andb__andb_rel_rw (b1: SFBool_u) (b2: SFBool_u) (b1_p: (SFBool_wf b1) /\ True) (b2_p: (SFBool_wf b2) /\ True) (VV: SFBool_u): ((⌊ andb (exist _ b1 b1_p) (exist _ b2 b2_p) -⌋) = VV) <-> (andb_rel b1 b2 VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite andb__andb_rel_rw : f_rel_funct_db.
#[global] Hint Resolve andb__andb_rel_rw : rel_ax_db.
#[global] Instance andb_lookup_rw : dictionary rwLem andb := { 
	lookup' := andb__andb_rel_rw
}.
Theorem andb__andb_rel (b1_r: SFBool) (b2_r: SFBool) (VV: SFBool_u): ((⌊ andb b1_r b2_r -⌋) = VV) <-> (andb_rel (⌊ b1_r -⌋) (⌊ b2_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite andb__andb_rel : f_rel_funct_db.
Theorem andb__andb_rel' (b1: SFBool_u) (b2: SFBool_u) (b1_r: SFBool) (b2_r: SFBool) (VV: SFBool_u): (b1 = (⌊ b1_r -⌋)) -> ((b2 = (⌊ b2_r -⌋)) -> (((⌊ andb b1_r b2_r -⌋) = VV) <-> (andb_rel b1 b2 VV))). 
Proof. 
	intros -> ->. 
	refine (andb__andb_rel b1_r b2_r VV). 
Qed. 
#[global] Hint Resolve andb__andb_rel' : f_rel_funct_db.
Theorem andb_rel_mk [b1: SFBool_u] [b2: SFBool_u] (b1_p: (SFBool_wf b1) /\ True) (b2_p: (SFBool_wf b2) /\ True): {VV: _ | andb_rel b1 b2 VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (andb_rel b1 b2 VV)) (andb (exist _ b1 b1_p) (exist _ b2 b2_p)) _); 
	rewrite <- andb__andb_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve andb_rel_mk : f_rel_funct_db.
#[global] Instance andbPack : (@Pack (SFBool ::RT (fun (b1_r: SFBool) => (SFBool ::RT (fun (b2_r: SFBool) => nilRT)))) (SFBool_u ::UT (SFBool_u ::UT nilUT)) (ltac: (mkProjectsArgListTG (SFBool ::RT (fun (b1_r: SFBool) => (SFBool ::RT (fun (b2_r: SFBool) => nilRT)))) (SFBool_u ::UT (SFBool_u ::UT nilUT)))) SFBool_u (fun (x_41925750: (ArgList SFBool ::RT (fun (b1_r: SFBool) => (SFBool ::RT (fun (b2_r: SFBool) => nilRT))))) => (fun (v_x_41925750: SFBool_u) => (ltac: (flattenP (fun (b1_r: SFBool) => (fun (b2_r: SFBool) => (fun (VV: SFBool_u) => ((SFBool_wf VV) /\ True)))) x_41925750 v_x_41925750))))).
Proof. 
	buildPackG andb andb_rel andb__andb_rel andb_rel_funct. 
Defined.
Definition andb'_spec (b1: SFBool) (b2: SFBool): Type := 
	SFBool. 
#[global] Hint Unfold andb'_spec : lia_unfold.
Definition andb' (b1: SFBool) (b2: SFBool): andb'_spec b1 b2. 
Proof. 
	destruct b1 as [b1 b1_p]. 
	destruct b2 as [b2 b2_p]. 
	let E := fresh "E" in 
	destruct (b1 ==? SFTrue_u) as [ | ] eqn:E; [refine (exist _ b2 _); 
	solver | refine (subsumptionCast _ _ SFFalse _); 
	solver]. 
Defined. 
Definition andb3_spec (b1: SFBool) (b2: SFBool) (b3: SFBool): Type := 
	SFBool. 
#[global] Hint Unfold andb3_spec : lia_unfold.
Definition andb3 (b1: SFBool) (b2: SFBool) (b3: SFBool): andb3_spec b1 b2 b3. 
Proof. 
	destruct b1 as [b1 b1_p]. 
	destruct b2 as [b2 b2_p]. 
	destruct b3 as [b3 b3_p]. 
	try revert b3_p; generalize dependent b3; try revert b2_p; generalize dependent b2; 
	induction b1 as [(*SFFalse*)  | (*SFTrue*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ SFFalse _); 
		solver.  
	  - intros . 
		induction b2 as [(*SFFalse*)  | (*SFTrue*) ]. 
		  -- intros . 
			refine (subsumptionCast _ _ SFFalse _); 
			solver.  
		  -- intros . 
			induction b3 as [(*SFFalse*)  | (*SFTrue*) ]. 
			  --- intros . 
				refine (subsumptionCast _ _ SFFalse _); 
				solver.  
			  --- intros . 
				refine (subsumptionCast _ _ SFTrue _); 
				solver.    
Defined. 
Inductive andb3_rel : (SFBool_u -> (SFBool_u -> (SFBool_u -> (SFBool_u -> Prop)))) := 
	 | andb3_SFTrue_SFTrue_SFTrue: andb3_rel SFTrue_u SFTrue_u SFTrue_u SFTrue_u
	 | andb3_SFTrue_SFTrue_SFFalse: andb3_rel SFTrue_u SFTrue_u SFFalse_u SFFalse_u
	 | andb3_SFTrue_SFFalse: (forall b3 , andb3_rel SFTrue_u SFFalse_u b3 SFFalse_u)
	 | andb3_SFFalse: (forall b2 b3 , andb3_rel SFFalse_u b2 b3 SFFalse_u). 
#[global] Hint Constructors andb3_rel : core_hint_db.
#[global] Instance andb3_lookup_rel : dictionary rel andb3 := { 
	lookup' := andb3_rel
}.
#[global] Instance andb3_getF : getFunc andb3_rel := { 
	getF' := andb3
}.
Theorem andb3_rel_funct [b1: SFBool_u] [b2: SFBool_u] [b3: SFBool_u]: (forall (VV: SFBool_u) (VV': SFBool_u) (H: andb3_rel b1 b2 b3 VV) (K: andb3_rel b1 b2 b3 VV') , VV = VV'). 
Proof. 
	try revert b3_p; generalize dependent b3; try revert b2_p; generalize dependent b2; 
	destruct b1 as [(*SFFalse*)  | (*SFTrue*) ]; 
	intros ; 
	[| 
	destruct b2 as [(*SFFalse*)  | (*SFTrue*) ]; 
	intros ; 
	[| 
	destruct b3 as [(*SFFalse*)  | (*SFTrue*) ]; 
	intros ]]; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve andb3_rel_funct : f_rel_funct_db.
Theorem andb3_SFTrue_SFTrue_SFTrue_lem: (andb3_rel SFTrue_u SFTrue_u SFTrue_u SFTrue_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite andb3_SFTrue_SFTrue_SFTrue_lem : f_rel_back.
Theorem andb3_SFTrue_SFTrue_SFFalse_lem: (andb3_rel SFTrue_u SFTrue_u SFFalse_u SFFalse_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite andb3_SFTrue_SFTrue_SFFalse_lem : f_rel_back.
Theorem andb3_SFTrue_SFFalse_lem (b3: _): (andb3_rel SFTrue_u SFFalse_u b3 SFFalse_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite andb3_SFTrue_SFFalse_lem : f_rel_back.
Theorem andb3_SFFalse_lem (b2: _) (b3: _): (andb3_rel SFFalse_u b2 b3 SFFalse_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite andb3_SFFalse_lem : f_rel_back.
Theorem andb3_rel_ex (b1: SFBool_u) (b2: SFBool_u) (b3: SFBool_u) (b1_p: (SFBool_wf b1) /\ True) (b2_p: (SFBool_wf b2) /\ True) (b3_p: (SFBool_wf b3) /\ True): andb3_rel b1 b2 b3 
		(⌊ andb3 (exist _ b1 b1_p) (exist _ b2 b2_p) (exist _ b3 b3_p) -⌋). 
Proof. 
	Opaque andb3.
	existence_lemma_pre andb3; 
	try revert b3_p; generalize dependent b3; try revert b2_p; generalize dependent b2; 
	destruct b1 as [(*SFFalse*)  | (*SFTrue*) ]; 
	intros ; 
	[fix_notations| 
	destruct b2 as [(*SFFalse*)  | (*SFTrue*) ]; 
	intros ; 
	[fix_notations| 
	destruct b3 as [(*SFFalse*)  | (*SFTrue*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations]]]; 
	simpl in *. 
	Transparent andb3.
	all: existence_lemma_quicksolve andb3; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve andb3_rel_ex : rel_ax_db.
#[global] Opaque andb3. 
Theorem andb3__andb3_rel_rw (b1: SFBool_u) (b2: SFBool_u) (b3: SFBool_u) (b1_p: (SFBool_wf b1) /\ True) (b2_p: (SFBool_wf b2) /\ True) (b3_p: (SFBool_wf b3) /\ True) (VV: SFBool_u): ((⌊ andb3 (exist _ b1 b1_p) (exist _ b2 b2_p) (exist _ b3 b3_p) -⌋) = VV) <-> (andb3_rel b1 b2 b3 VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite andb3__andb3_rel_rw : f_rel_funct_db.
#[global] Hint Resolve andb3__andb3_rel_rw : rel_ax_db.
#[global] Instance andb3_lookup_rw : dictionary rwLem andb3 := { 
	lookup' := andb3__andb3_rel_rw
}.
Theorem andb3__andb3_rel (b1_r: SFBool) (b2_r: SFBool) (b3_r: SFBool) (VV: SFBool_u): ((⌊ andb3 b1_r b2_r b3_r -⌋) = VV) <-> (andb3_rel (⌊ b1_r -⌋) (⌊ b2_r -⌋) (⌊ b3_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite andb3__andb3_rel : f_rel_funct_db.
Theorem andb3__andb3_rel' (b1: SFBool_u) (b2: SFBool_u) (b3: SFBool_u) (b1_r: SFBool) (b2_r: SFBool) (b3_r: SFBool) (VV: SFBool_u): (b1 = (⌊ b1_r -⌋)) -> ((b2 = (⌊ b2_r -⌋)) -> ((b3 = (⌊ b3_r -⌋)) -> (((⌊ andb3 b1_r b2_r b3_r -⌋) = VV) <-> (andb3_rel b1 b2 b3 VV)))). 
Proof. 
	intros -> -> ->. 
	refine (andb3__andb3_rel b1_r b2_r b3_r VV). 
Qed. 
#[global] Hint Resolve andb3__andb3_rel' : f_rel_funct_db.
Theorem andb3_rel_mk [b1: SFBool_u] [b2: SFBool_u] [b3: SFBool_u] (b1_p: (SFBool_wf b1) /\ True) (b2_p: (SFBool_wf b2) /\ True) (b3_p: (SFBool_wf b3) /\ True): {VV: _ | andb3_rel b1 b2 b3 VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (andb3_rel b1 b2 b3 VV)) 
		(andb3 (exist _ b1 b1_p) (exist _ b2 b2_p) (exist _ b3 b3_p)) _); 
	rewrite <- andb3__andb3_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve andb3_rel_mk : f_rel_funct_db.
#[global] Instance andb3Pack : (@Pack (SFBool ::RT (fun (b1_r: SFBool) => (SFBool ::RT (fun (b2_r: SFBool) => (SFBool ::RT (fun (b3_r: SFBool) => nilRT)))))) (SFBool_u ::UT (SFBool_u ::UT (SFBool_u ::UT nilUT))) (ltac: (mkProjectsArgListTG (SFBool ::RT (fun (b1_r: SFBool) => (SFBool ::RT (fun (b2_r: SFBool) => (SFBool ::RT (fun (b3_r: SFBool) => nilRT)))))) (SFBool_u ::UT (SFBool_u ::UT (SFBool_u ::UT nilUT))))) SFBool_u (fun (x_36837378: (ArgList SFBool ::RT (fun (b1_r: SFBool) => (SFBool ::RT (fun (b2_r: SFBool) => (SFBool ::RT (fun (b3_r: SFBool) => nilRT))))))) => (fun (v_x_36837378: SFBool_u) => (ltac: (flattenP (fun (b1_r: SFBool) => (fun (b2_r: SFBool) => (fun (b3_r: SFBool) => (fun (VV: SFBool_u) => ((SFBool_wf VV) /\ True))))) x_36837378 v_x_36837378))))).
Proof. 
	buildPackG andb3 andb3_rel andb3__andb3_rel andb3_rel_funct. 
Defined.
Definition test_andb31_spec: Type := 
	{{forall (andb3res: SFBool_u), (andb3_rel SFTrue_u SFTrue_u SFTrue_u andb3res) -> (andb3res = SFTrue_u)}}. 
#[global] Hint Unfold test_andb31_spec : lia_unfold.
Theorem test_andb31: test_andb31_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition test_andb32_spec: Type := 
	{{forall (andb3res: SFBool_u), (andb3_rel SFFalse_u SFTrue_u SFTrue_u andb3res) -> (andb3res = SFFalse_u)}}. 
#[global] Hint Unfold test_andb32_spec : lia_unfold.
Theorem test_andb32: test_andb32_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition test_andb33_spec: Type := 
	{{forall (andb3res: SFBool_u), (andb3_rel SFTrue_u SFFalse_u SFTrue_u andb3res) -> (andb3res = SFFalse_u)}}. 
#[global] Hint Unfold test_andb33_spec : lia_unfold.
Theorem test_andb33: test_andb33_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition test_andb34_spec: Type := 
	{{forall (andb3res: SFBool_u), (andb3_rel SFTrue_u SFTrue_u SFFalse_u andb3res) -> (andb3res = SFFalse_u)}}. 
#[global] Hint Unfold test_andb34_spec : lia_unfold.
Theorem test_andb34: test_andb34_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition andb_commutative_spec (b: SFBool) (c: SFBool): Type := 
	{{forall (andbres: SFBool_u), (andb_rel (⌊ b -⌋) (⌊ c -⌋) andbres) -> (forall (andb_res_2: SFBool_u), (andb_rel (⌊ c -⌋) (⌊ b -⌋) andb_res_2) -> (andbres == andb_res_2))}}. 
#[global] Hint Unfold andb_commutative_spec : lia_unfold.
Theorem andb_commutative (b: SFBool) (c: SFBool): andb_commutative_spec b c. 
Proof. 
	destruct b as [b b_p]. 
	destruct c as [c c_p]. 
	try revert c_p; generalize dependent c; 
	induction b as [(*SFFalse*)  | (*SFTrue*) ]. 
	  - intros . 
		induction c as [(*SFFalse*)  | (*SFTrue*) ]. 
		  -- intros . 
			refine (exist _ unit _); 
			solver.  
		  -- intros . 
			refine (exist _ unit _); 
			solver.   
	  - intros . 
		induction c as [(*SFFalse*)  | (*SFTrue*) ]. 
		  -- intros . 
			refine (exist _ unit _); 
			solver.  
		  -- intros . 
			refine (exist _ unit _); 
			solver.   
Qed. 
Definition andb_true_elim2_spec (b: SFBool) (c: SFBool) (p: {{forall (andbres: SFBool_u), (andb_rel (⌊ b -⌋) (⌊ c -⌋) andbres) -> (andbres = SFTrue_u)}}): Type := 
	{{(⌊ c -⌋) = SFTrue_u}}. 
#[global] Hint Unfold andb_true_elim2_spec : lia_unfold.
Theorem andb_true_elim2 (b: SFBool) (c: SFBool) (p: {{forall (andbres: SFBool_u), (andb_rel (⌊ b -⌋) (⌊ c -⌋) andbres) -> (andbres = SFTrue_u)}}): andb_true_elim2_spec b c p. 
Proof. 
	destruct b as [b b_p]. 
	destruct c as [c c_p]. 
	destruct p as [p p_p]. 
	try revert p_p; generalize dependent p; try revert c_p; generalize dependent c; 
	induction b as [(*SFFalse*)  | (*SFTrue*) ]. 
	  - intros . 
		induction c as [(*SFFalse*)  | (*SFTrue*) ]. 
		  -- intros . 
			refine (exist _ unit _); 
			solver.  
		  -- intros . 
			refine (exist _ unit _); 
			solver.   
	  - intros . 
		induction c as [(*SFFalse*)  | (*SFTrue*) ]. 
		  -- intros . 
			refine (exist _ unit _); 
			solver.  
		  -- intros . 
			refine (exist _ unit _); 
			solver.   
Qed. 
Definition identity_fn_applied_twice_spec (f: (@Pack (SFBool ::RT (fun (lq_tmp0: SFBool) => nilRT)) (SFBool_u ::UT nilUT) (ltac: (mkProjectsArgListTG (SFBool ::RT (fun (lq_tmp0: SFBool) => nilRT)) (SFBool_u ::UT nilUT))) SFBool_u (fun (x_24207487: (ArgList SFBool ::RT (fun (lq_tmp0: SFBool) => nilRT))) => (fun (v_x_24207487: SFBool_u) => (ltac: (flattenP (fun (lq_tmp0: SFBool) => (fun (VV: SFBool_u) => ((SFBool_wf VV) /\ True))) x_24207487 v_x_24207487)))))) (h: (forall (x: SFBool) , {{forall (fres: _), ((getPackRel f) (⌊ x -⌋) fres) -> (fres = (⌊ x -⌋))}})) (b: SFBool): Type := 
	{{forall (fres: _), ((getPackRel f) (⌊ b -⌋) fres) -> (forall (f_res_2: _), ((getPackRel f) fres f_res_2) -> (f_res_2 = (⌊ b -⌋)))}}. 
#[global] Hint Unfold identity_fn_applied_twice_spec : lia_unfold.
Theorem identity_fn_applied_twice (f: (@Pack (SFBool ::RT (fun (lq_tmp0: SFBool) => nilRT)) (SFBool_u ::UT nilUT) (ltac: (mkProjectsArgListTG (SFBool ::RT (fun (lq_tmp0: SFBool) => nilRT)) (SFBool_u ::UT nilUT))) SFBool_u (fun (x_24207487: (ArgList SFBool ::RT (fun (lq_tmp0: SFBool) => nilRT))) => (fun (v_x_24207487: SFBool_u) => (ltac: (flattenP (fun (lq_tmp0: SFBool) => (fun (VV: SFBool_u) => ((SFBool_wf VV) /\ True))) x_24207487 v_x_24207487)))))) (h: (forall (x: SFBool) , {{forall (fres: _), ((getPackRel f) (⌊ x -⌋) fres) -> (fres = (⌊ x -⌋))}})) (b: SFBool): identity_fn_applied_twice_spec f h b. 
Proof. 
	destruct b as [b b_p]. 
	pose proof (exist (fun (x: Unit) => True) unit (ltac: (solver))) as H_39899679. 
	simpl in H_39899679. 
	fix_notations. 
	pose proof (h 
		(exist (fun (x: SFBool_u) => ((SFBool_wf x) /\ True)) b (ltac: (solver)))) as H_42296745. 
	assert (H_42296745': forall (fres: _), ((getPackRel f) b fres) -> (True /\ (fres == b))) by solver. 
	simpl in H_42296745'. 
	pose proof (h 
		(subsumptionCast SFBool_u (fun (x: SFBool_u) => ((SFBool_wf x) /\ True)) 
		((getPackF f) 
		(exist (fun (lq_tmp0: SFBool_u) => ((SFBool_wf lq_tmp0) /\ True)) b (ltac: (solver)))) (ltac: (solver)))) as H_49965291; 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition nandb_spec (b1: SFBool) (b2: SFBool): Type := 
	SFBool. 
#[global] Hint Unfold nandb_spec : lia_unfold.
Definition nandb (b1: SFBool) (b2: SFBool): nandb_spec b1 b2. 
Proof. 
	destruct b1 as [b1 b1_p]. 
	destruct b2 as [b2 b2_p]. 
	try revert b2_p; generalize dependent b2; 
	induction b1 as [(*SFFalse*)  | (*SFTrue*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ SFTrue _); 
		solver.  
	  - intros . 
		induction b2 as [(*SFFalse*)  | (*SFTrue*) ]. 
		  -- intros . 
			refine (subsumptionCast _ _ SFTrue _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ SFFalse _); 
			solver.   
Defined. 
Inductive nandb_rel : (SFBool_u -> (SFBool_u -> (SFBool_u -> Prop))) := 
	 | nandb_SFTrue_SFTrue: nandb_rel SFTrue_u SFTrue_u SFFalse_u
	 | nandb_SFTrue_SFFalse: nandb_rel SFTrue_u SFFalse_u SFTrue_u
	 | nandb_SFFalse: (forall b2 , nandb_rel SFFalse_u b2 SFTrue_u). 
#[global] Hint Constructors nandb_rel : core_hint_db.
#[global] Instance nandb_lookup_rel : dictionary rel nandb := { 
	lookup' := nandb_rel
}.
#[global] Instance nandb_getF : getFunc nandb_rel := { 
	getF' := nandb
}.
Theorem nandb_rel_funct [b1: SFBool_u] [b2: SFBool_u]: (forall (VV: SFBool_u) (VV': SFBool_u) (H: nandb_rel b1 b2 VV) (K: nandb_rel b1 b2 VV') , VV = VV'). 
Proof. 
	try revert b2_p; generalize dependent b2; 
	destruct b1 as [(*SFFalse*)  | (*SFTrue*) ]; 
	intros ; 
	[| 
	destruct b2 as [(*SFFalse*)  | (*SFTrue*) ]; 
	intros ]; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve nandb_rel_funct : f_rel_funct_db.
Theorem nandb_SFTrue_SFTrue_lem: (nandb_rel SFTrue_u SFTrue_u SFFalse_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite nandb_SFTrue_SFTrue_lem : f_rel_back.
Theorem nandb_SFTrue_SFFalse_lem: (nandb_rel SFTrue_u SFFalse_u SFTrue_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite nandb_SFTrue_SFFalse_lem : f_rel_back.
Theorem nandb_SFFalse_lem (b2: _): (nandb_rel SFFalse_u b2 SFTrue_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite nandb_SFFalse_lem : f_rel_back.
Theorem nandb_rel_ex (b1: SFBool_u) (b2: SFBool_u) (b1_p: (SFBool_wf b1) /\ True) (b2_p: (SFBool_wf b2) /\ True): nandb_rel b1 b2 (⌊ nandb (exist _ b1 b1_p) (exist _ b2 b2_p) -⌋). 
Proof. 
	Opaque nandb.
	existence_lemma_pre nandb; 
	try revert b2_p; generalize dependent b2; 
	destruct b1 as [(*SFFalse*)  | (*SFTrue*) ]; 
	intros ; 
	[fix_notations| 
	destruct b2 as [(*SFFalse*)  | (*SFTrue*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations]]; 
	simpl in *. 
	Transparent nandb.
	all: existence_lemma_quicksolve nandb; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve nandb_rel_ex : rel_ax_db.
#[global] Opaque nandb. 
Theorem nandb__nandb_rel_rw (b1: SFBool_u) (b2: SFBool_u) (b1_p: (SFBool_wf b1) /\ True) (b2_p: (SFBool_wf b2) /\ True) (VV: SFBool_u): ((⌊ nandb (exist _ b1 b1_p) (exist _ b2 b2_p) -⌋) = VV) <-> (nandb_rel b1 b2 VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite nandb__nandb_rel_rw : f_rel_funct_db.
#[global] Hint Resolve nandb__nandb_rel_rw : rel_ax_db.
#[global] Instance nandb_lookup_rw : dictionary rwLem nandb := { 
	lookup' := nandb__nandb_rel_rw
}.
Theorem nandb__nandb_rel (b1_r: SFBool) (b2_r: SFBool) (VV: SFBool_u): ((⌊ nandb b1_r b2_r -⌋) = VV) <-> (nandb_rel (⌊ b1_r -⌋) (⌊ b2_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite nandb__nandb_rel : f_rel_funct_db.
Theorem nandb__nandb_rel' (b1: SFBool_u) (b2: SFBool_u) (b1_r: SFBool) (b2_r: SFBool) (VV: SFBool_u): (b1 = (⌊ b1_r -⌋)) -> ((b2 = (⌊ b2_r -⌋)) -> (((⌊ nandb b1_r b2_r -⌋) = VV) <-> (nandb_rel b1 b2 VV))). 
Proof. 
	intros -> ->. 
	refine (nandb__nandb_rel b1_r b2_r VV). 
Qed. 
#[global] Hint Resolve nandb__nandb_rel' : f_rel_funct_db.
Theorem nandb_rel_mk [b1: SFBool_u] [b2: SFBool_u] (b1_p: (SFBool_wf b1) /\ True) (b2_p: (SFBool_wf b2) /\ True): {VV: _ | nandb_rel b1 b2 VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (nandb_rel b1 b2 VV)) (nandb (exist _ b1 b1_p) (exist _ b2 b2_p)) _); 
	rewrite <- nandb__nandb_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve nandb_rel_mk : f_rel_funct_db.
#[global] Instance nandbPack : (@Pack (SFBool ::RT (fun (b1_r: SFBool) => (SFBool ::RT (fun (b2_r: SFBool) => nilRT)))) (SFBool_u ::UT (SFBool_u ::UT nilUT)) (ltac: (mkProjectsArgListTG (SFBool ::RT (fun (b1_r: SFBool) => (SFBool ::RT (fun (b2_r: SFBool) => nilRT)))) (SFBool_u ::UT (SFBool_u ::UT nilUT)))) SFBool_u (fun (x_41925750: (ArgList SFBool ::RT (fun (b1_r: SFBool) => (SFBool ::RT (fun (b2_r: SFBool) => nilRT))))) => (fun (v_x_41925750: SFBool_u) => (ltac: (flattenP (fun (b1_r: SFBool) => (fun (b2_r: SFBool) => (fun (VV: SFBool_u) => ((SFBool_wf VV) /\ True)))) x_41925750 v_x_41925750))))).
Proof. 
	buildPackG nandb nandb_rel nandb__nandb_rel nandb_rel_funct. 
Defined.
Definition test_nandb1_spec: Type := 
	{{forall (nandbres: SFBool_u), (nandb_rel SFTrue_u SFFalse_u nandbres) -> (nandbres = SFTrue_u)}}. 
#[global] Hint Unfold test_nandb1_spec : lia_unfold.
Theorem test_nandb1: test_nandb1_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition test_nandb2_spec: Type := 
	{{forall (nandbres: SFBool_u), (nandb_rel SFFalse_u SFFalse_u nandbres) -> (nandbres = SFTrue_u)}}. 
#[global] Hint Unfold test_nandb2_spec : lia_unfold.
Theorem test_nandb2: test_nandb2_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition test_nandb3_spec: Type := 
	{{forall (nandbres: SFBool_u), (nandb_rel SFFalse_u SFTrue_u nandbres) -> (nandbres = SFTrue_u)}}. 
#[global] Hint Unfold test_nandb3_spec : lia_unfold.
Theorem test_nandb3: test_nandb3_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition test_nandb4_spec: Type := 
	{{forall (nandbres: SFBool_u), (nandb_rel SFTrue_u SFTrue_u nandbres) -> (nandbres = SFFalse_u)}}. 
#[global] Hint Unfold test_nandb4_spec : lia_unfold.
Theorem test_nandb4: test_nandb4_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition negb_spec (lq_tmp0: SFBool): Type := 
	SFBool. 
#[global] Hint Unfold negb_spec : lia_unfold.
Definition negb (lq_tmp0: SFBool): negb_spec lq_tmp0. 
Proof. 
	destruct lq_tmp0 as [lq_tmp0 lq_tmp0_p]. 
	induction lq_tmp0 as [(*SFFalse*)  | (*SFTrue*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ SFTrue _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ SFFalse _); 
		solver.  
Defined. 
Inductive negb_rel : (SFBool_u -> (SFBool_u -> Prop)) := 
	 | negb_SFTrue: negb_rel SFTrue_u SFFalse_u
	 | negb_SFFalse: negb_rel SFFalse_u SFTrue_u. 
#[global] Hint Constructors negb_rel : core_hint_db.
#[global] Instance negb_lookup_rel : dictionary rel negb := { 
	lookup' := negb_rel
}.
#[global] Instance negb_getF : getFunc negb_rel := { 
	getF' := negb
}.
Theorem negb_rel_funct [lq_tmp0: SFBool_u]: (forall (VV: SFBool_u) (VV': SFBool_u) (H: negb_rel lq_tmp0 VV) (K: negb_rel lq_tmp0 VV') , VV = VV'). 
Proof. 
	destruct lq_tmp0 as [(*SFFalse*)  | (*SFTrue*) ]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve negb_rel_funct : f_rel_funct_db.
Theorem negb_SFTrue_lem: (negb_rel SFTrue_u SFFalse_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite negb_SFTrue_lem : f_rel_back.
Theorem negb_SFFalse_lem: (negb_rel SFFalse_u SFTrue_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite negb_SFFalse_lem : f_rel_back.
Theorem negb_rel_ex (lq_tmp0: SFBool_u) (lq_tmp0_p: (SFBool_wf lq_tmp0) /\ True): negb_rel lq_tmp0 (⌊ negb (exist _ lq_tmp0 lq_tmp0_p) -⌋). 
Proof. 
	Opaque negb.
	existence_lemma_pre negb; 
	destruct lq_tmp0 as [(*SFFalse*)  | (*SFTrue*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations]; 
	simpl in *. 
	Transparent negb.
	all: existence_lemma_quicksolve negb; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve negb_rel_ex : rel_ax_db.
#[global] Opaque negb. 
Theorem negb__negb_rel_rw (lq_tmp0: SFBool_u) (lq_tmp0_p: (SFBool_wf lq_tmp0) /\ True) (VV: SFBool_u): ((⌊ negb (exist _ lq_tmp0 lq_tmp0_p) -⌋) = VV) <-> (negb_rel lq_tmp0 VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite negb__negb_rel_rw : f_rel_funct_db.
#[global] Hint Resolve negb__negb_rel_rw : rel_ax_db.
#[global] Instance negb_lookup_rw : dictionary rwLem negb := { 
	lookup' := negb__negb_rel_rw
}.
Theorem negb__negb_rel (lq_tmp0_r: SFBool) (VV: SFBool_u): ((⌊ negb lq_tmp0_r -⌋) = VV) <-> (negb_rel (⌊ lq_tmp0_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite negb__negb_rel : f_rel_funct_db.
Theorem negb__negb_rel' (lq_tmp0: SFBool_u) (lq_tmp0_r: SFBool) (VV: SFBool_u): (lq_tmp0 = (⌊ lq_tmp0_r -⌋)) -> (((⌊ negb lq_tmp0_r -⌋) = VV) <-> (negb_rel lq_tmp0 VV)). 
Proof. 
	intros ->. 
	refine (negb__negb_rel lq_tmp0_r VV). 
Qed. 
#[global] Hint Resolve negb__negb_rel' : f_rel_funct_db.
Theorem negb_rel_mk [lq_tmp0: SFBool_u] (lq_tmp0_p: (SFBool_wf lq_tmp0) /\ True): {VV: _ | negb_rel lq_tmp0 VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (negb_rel lq_tmp0 VV)) (negb (exist _ lq_tmp0 lq_tmp0_p)) _); 
	rewrite <- negb__negb_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve negb_rel_mk : f_rel_funct_db.
#[global] Instance negbPack : (@Pack (SFBool ::RT (fun (lq_tmp0_r: SFBool) => nilRT)) (SFBool_u ::UT nilUT) (ltac: (mkProjectsArgListTG (SFBool ::RT (fun (lq_tmp0_r: SFBool) => nilRT)) (SFBool_u ::UT nilUT))) SFBool_u (fun (x_72936089: (ArgList SFBool ::RT (fun (lq_tmp0_r: SFBool) => nilRT))) => (fun (v_x_72936089: SFBool_u) => (ltac: (flattenP (fun (lq_tmp0_r: SFBool) => (fun (VV: SFBool_u) => ((SFBool_wf VV) /\ True))) x_72936089 v_x_72936089))))).
Proof. 
	buildPackG negb negb_rel negb__negb_rel negb_rel_funct. 
Defined.
Definition negb'_spec (b: SFBool): Type := 
	SFBool. 
#[global] Hint Unfold negb'_spec : lia_unfold.
Definition negb' (b: SFBool): negb'_spec b. 
Proof. 
	destruct b as [b b_p]. 
	let E := fresh "E" in 
	destruct (b ==? SFTrue_u) as [ | ] eqn:E; [refine (subsumptionCast _ _ SFFalse _); 
	solver | refine (subsumptionCast _ _ SFTrue _); 
	solver]. 
Defined. 
Definition negb_involutive_spec (b: SFBool): Type := 
	{{forall (negbres: SFBool_u), (negb_rel (⌊ b -⌋) negbres) -> (forall (negb_res_2: SFBool_u), (negb_rel negbres negb_res_2) -> (negb_res_2 = (⌊ b -⌋)))}}. 
#[global] Hint Unfold negb_involutive_spec : lia_unfold.
Theorem negb_involutive (b: SFBool): negb_involutive_spec b. 
Proof. 
	destruct b as [b b_p]. 
	induction b as [(*SFFalse*)  | (*SFTrue*) ]. 
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
Qed. 
Definition orb_spec (b1: SFBool) (b2: SFBool): Type := 
	SFBool. 
#[global] Hint Unfold orb_spec : lia_unfold.
Definition orb (b1: SFBool) (b2: SFBool): orb_spec b1 b2. 
Proof. 
	destruct b1 as [b1 b1_p]. 
	destruct b2 as [b2 b2_p]. 
	try revert b2_p; generalize dependent b2; 
	induction b1 as [(*SFFalse*)  | (*SFTrue*) ]. 
	  - intros . 
		refine (exist _ b2 _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ SFTrue _); 
		solver.  
Defined. 
Inductive orb_rel : (SFBool_u -> (SFBool_u -> (SFBool_u -> Prop))) := 
	 | orb_SFTrue: (forall b2 , orb_rel SFTrue_u b2 SFTrue_u)
	 | orb_SFFalse: (forall b2 , orb_rel SFFalse_u b2 b2). 
#[global] Hint Constructors orb_rel : core_hint_db.
#[global] Instance orb_lookup_rel : dictionary rel orb := { 
	lookup' := orb_rel
}.
#[global] Instance orb_getF : getFunc orb_rel := { 
	getF' := orb
}.
Theorem orb_rel_funct [b1: SFBool_u] [b2: SFBool_u]: (forall (VV: SFBool_u) (VV': SFBool_u) (H: orb_rel b1 b2 VV) (K: orb_rel b1 b2 VV') , VV = VV'). 
Proof. 
	try revert b2_p; generalize dependent b2; 
	destruct b1 as [(*SFFalse*)  | (*SFTrue*) ]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve orb_rel_funct : f_rel_funct_db.
Theorem orb_SFTrue_lem (b2: _): (orb_rel SFTrue_u b2 SFTrue_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite orb_SFTrue_lem : f_rel_back.
Theorem orb_SFFalse_lem (b2: _): (orb_rel SFFalse_u b2 b2) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite orb_SFFalse_lem : f_rel_back.
Theorem orb_rel_ex (b1: SFBool_u) (b2: SFBool_u) (b1_p: (SFBool_wf b1) /\ True) (b2_p: (SFBool_wf b2) /\ True): orb_rel b1 b2 (⌊ orb (exist _ b1 b1_p) (exist _ b2 b2_p) -⌋). 
Proof. 
	Opaque orb.
	existence_lemma_pre orb; 
	try revert b2_p; generalize dependent b2; 
	destruct b1 as [(*SFFalse*)  | (*SFTrue*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations]; 
	simpl in *. 
	Transparent orb.
	all: existence_lemma_quicksolve orb; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve orb_rel_ex : rel_ax_db.
#[global] Opaque orb. 
Theorem orb__orb_rel_rw (b1: SFBool_u) (b2: SFBool_u) (b1_p: (SFBool_wf b1) /\ True) (b2_p: (SFBool_wf b2) /\ True) (VV: SFBool_u): ((⌊ orb (exist _ b1 b1_p) (exist _ b2 b2_p) -⌋) = VV) <-> (orb_rel b1 b2 VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite orb__orb_rel_rw : f_rel_funct_db.
#[global] Hint Resolve orb__orb_rel_rw : rel_ax_db.
#[global] Instance orb_lookup_rw : dictionary rwLem orb := { 
	lookup' := orb__orb_rel_rw
}.
Theorem orb__orb_rel (b1_r: SFBool) (b2_r: SFBool) (VV: SFBool_u): ((⌊ orb b1_r b2_r -⌋) = VV) <-> (orb_rel (⌊ b1_r -⌋) (⌊ b2_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite orb__orb_rel : f_rel_funct_db.
Theorem orb__orb_rel' (b1: SFBool_u) (b2: SFBool_u) (b1_r: SFBool) (b2_r: SFBool) (VV: SFBool_u): (b1 = (⌊ b1_r -⌋)) -> ((b2 = (⌊ b2_r -⌋)) -> (((⌊ orb b1_r b2_r -⌋) = VV) <-> (orb_rel b1 b2 VV))). 
Proof. 
	intros -> ->. 
	refine (orb__orb_rel b1_r b2_r VV). 
Qed. 
#[global] Hint Resolve orb__orb_rel' : f_rel_funct_db.
Theorem orb_rel_mk [b1: SFBool_u] [b2: SFBool_u] (b1_p: (SFBool_wf b1) /\ True) (b2_p: (SFBool_wf b2) /\ True): {VV: _ | orb_rel b1 b2 VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (orb_rel b1 b2 VV)) (orb (exist _ b1 b1_p) (exist _ b2 b2_p)) _); 
	rewrite <- orb__orb_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve orb_rel_mk : f_rel_funct_db.
#[global] Instance orbPack : (@Pack (SFBool ::RT (fun (b1_r: SFBool) => (SFBool ::RT (fun (b2_r: SFBool) => nilRT)))) (SFBool_u ::UT (SFBool_u ::UT nilUT)) (ltac: (mkProjectsArgListTG (SFBool ::RT (fun (b1_r: SFBool) => (SFBool ::RT (fun (b2_r: SFBool) => nilRT)))) (SFBool_u ::UT (SFBool_u ::UT nilUT)))) SFBool_u (fun (x_41925750: (ArgList SFBool ::RT (fun (b1_r: SFBool) => (SFBool ::RT (fun (b2_r: SFBool) => nilRT))))) => (fun (v_x_41925750: SFBool_u) => (ltac: (flattenP (fun (b1_r: SFBool) => (fun (b2_r: SFBool) => (fun (VV: SFBool_u) => ((SFBool_wf VV) /\ True)))) x_41925750 v_x_41925750))))).
Proof. 
	buildPackG orb orb_rel orb__orb_rel orb_rel_funct. 
Defined.
Definition andb_eq_orb_spec (b: SFBool) (c: SFBool) (h: {{forall (andbres: SFBool_u), (andb_rel (⌊ b -⌋) (⌊ c -⌋) andbres) -> (forall (orbres: SFBool_u), (orb_rel (⌊ b -⌋) (⌊ c -⌋) orbres) -> (andbres == orbres))}}): Type := 
	{{(⌊ b -⌋) = (⌊ c -⌋)}}. 
#[global] Hint Unfold andb_eq_orb_spec : lia_unfold.
Theorem andb_eq_orb (b: SFBool) (c: SFBool) (h: {{forall (andbres: SFBool_u), (andb_rel (⌊ b -⌋) (⌊ c -⌋) andbres) -> (forall (orbres: SFBool_u), (orb_rel (⌊ b -⌋) (⌊ c -⌋) orbres) -> (andbres == orbres))}}): andb_eq_orb_spec b c h. 
Proof. 
	destruct b as [b b_p]. 
	destruct c as [c c_p]. 
	destruct h as [h h_p]. 
	try revert h_p; generalize dependent h; try revert c_p; generalize dependent c; 
	induction b as [(*SFFalse*)  | (*SFTrue*) ]. 
	  - intros . 
		induction c as [(*SFFalse*)  | (*SFTrue*) ]. 
		  -- intros . 
			refine (exist _ unit _); 
			solver.  
		  -- intros . 
			refine (exist _ unit _); 
			solver.   
	  - intros . 
		induction c as [(*SFFalse*)  | (*SFTrue*) ]. 
		  -- intros . 
			refine (exist _ unit _); 
			solver.  
		  -- intros . 
			refine (exist _ unit _); 
			solver.   
Qed. 
Definition test_orb1_spec: Type := 
	{{forall (orbres: SFBool_u), (orb_rel SFTrue_u SFFalse_u orbres) -> (orbres = SFTrue_u)}}. 
#[global] Hint Unfold test_orb1_spec : lia_unfold.
Theorem test_orb1: test_orb1_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition test_orb2_spec: Type := 
	{{forall (orbres: SFBool_u), (orb_rel SFFalse_u SFFalse_u orbres) -> (orbres = SFFalse_u)}}. 
#[global] Hint Unfold test_orb2_spec : lia_unfold.
Theorem test_orb2: test_orb2_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition test_orb3_spec: Type := 
	{{forall (orbres: SFBool_u), (orb_rel SFFalse_u SFTrue_u orbres) -> (orbres = SFTrue_u)}}. 
#[global] Hint Unfold test_orb3_spec : lia_unfold.
Theorem test_orb3: test_orb3_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition test_orb4_spec: Type := 
	{{forall (orbres: SFBool_u), (orb_rel SFTrue_u SFTrue_u orbres) -> (orbres = SFTrue_u)}}. 
#[global] Hint Unfold test_orb4_spec : lia_unfold.
Theorem test_orb4: test_orb4_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition test_orb5_spec: Type := 
	{{forall (orbres: SFBool_u), (orb_rel SFFalse_u SFTrue_u orbres) -> (forall (orb_res_2: SFBool_u), (orb_rel SFFalse_u orbres orb_res_2) -> (orb_res_2 = SFTrue_u))}}. 
#[global] Hint Unfold test_orb5_spec : lia_unfold.
Theorem test_orb5: test_orb5_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition orb'_spec (b1: SFBool) (b2: SFBool): Type := 
	SFBool. 
#[global] Hint Unfold orb'_spec : lia_unfold.
Definition orb' (b1: SFBool) (b2: SFBool): orb'_spec b1 b2. 
Proof. 
	destruct b1 as [b1 b1_p]. 
	destruct b2 as [b2 b2_p]. 
	let E := fresh "E" in 
	destruct (b1 ==? SFTrue_u) as [ | ] eqn:E; [refine (subsumptionCast _ _ SFTrue _); 
	solver | refine (exist _ b2 _); 
	solver]. 
Defined. 
Inductive SFBit_u : Type := 
	 | B0_u: SFBit_u
	 | B1_u: SFBit_u. 
Fixpoint SFBit_eq (x: SFBit_u) (y: SFBit_u): bool := 
	match (x, y) with (B0_u, B0_u) => true | (B1_u, B1_u) => true | (_, _) => false end. 
Theorem SFBit_eq_refl: (forall (x: SFBit_u) , is_true (SFBit_eq x x)). 
Proof. 
	eq_refl_rec. 
Qed. 
#[global] Hint Resolve SFBit_eq_refl : eq_hint_db.
Theorem SFBit_eqb_eq: (forall (s: SFBit_u) (t: SFBit_u) , (is_true (SFBit_eq s t)) -> (s = t)). 
Proof. 
	eqb_eq_lem. 
Qed. 
#[global] Hint Resolve SFBit_eqb_eq : eq_hint_db.
#[global] Instance leibnitz_eq_SFBit : LeibnitzEqB := { 
	equalB' := SFBit_eq;
	refl' := SFBit_eq_refl;
	eqb_eq' := SFBit_eqb_eq
}.
Fixpoint SFBit_wf (x: SFBit_u): Prop := 
	match x with B0_u => True | B1_u => True end. 
Theorem SFBit_wf_ref [p: SFBit_u -> Prop] (tm: {v: SFBit_u | (SFBit_wf v) /\ (p v)}): SFBit_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation SFBit := {x: SFBit_u | (SFBit_wf x) /\ True}. 
Definition B0_lem: (SFBit_wf B0_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition B0: SFBit := 
	exist _ B0_u B0_lem. 
Definition B1_lem: (SFBit_wf B1_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition B1: SFBit := 
	exist _ B1_u B1_lem. 
#[global] Hint Resolve SFBit_wf_ref : wf_constr_db.
#[global] Hint Unfold SFBit_wf : wf_constr_db.
#[global] Hint Resolve SFBit_eq : ref_constr_db.
#[global] Hint Unfold B0 : ref_constr_db.
#[global] Hint Unfold B1 : ref_constr_db.
Inductive SFBin_u : Type := 
	 | Bin0_u: SFBin_u -> SFBin_u
	 | Bin1_u: SFBin_u -> SFBin_u
	 | SoftwareFoundations__Z_u: SFBin_u. 
Fixpoint SFBin_eq (x: SFBin_u) (y: SFBin_u): bool := 
	match (x, y) with (Bin0_u x, Bin0_u x') => (true && (SFBin_eq x x')) | (Bin1_u x, Bin1_u x') => (true && (SFBin_eq x x')) | (SoftwareFoundations__Z_u, SoftwareFoundations__Z_u) => true | (_, _) => false end. 
Theorem SFBin_eq_refl: (forall (x: SFBin_u) , is_true (SFBin_eq x x)). 
Proof. 
	eq_refl_rec. 
Qed. 
#[global] Hint Resolve SFBin_eq_refl : eq_hint_db.
Theorem SFBin_eqb_eq: (forall (s: SFBin_u) (t: SFBin_u) , (is_true (SFBin_eq s t)) -> (s = t)). 
Proof. 
	eqb_eq_lem. 
Qed. 
#[global] Hint Resolve SFBin_eqb_eq : eq_hint_db.
#[global] Instance leibnitz_eq_SFBin : LeibnitzEqB := { 
	equalB' := SFBin_eq;
	refl' := SFBin_eq_refl;
	eqb_eq' := SFBin_eqb_eq
}.
Fixpoint SFBin_wf (x: SFBin_u): Prop := 
	match x with (Bin0_u n) => ((SFBin_wf n) /\ True) | (Bin1_u n) => ((SFBin_wf n) /\ True) | SoftwareFoundations__Z_u => True end. 
Theorem SFBin_wf_ref [p: SFBin_u -> Prop] (tm: {v: SFBin_u | (SFBin_wf v) /\ (p v)}): SFBin_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation SFBin := {x: SFBin_u | (SFBin_wf x) /\ True}. 
Definition Bin0_lem (n: SFBin): (SFBin_wf (Bin0_u (⌊ n -⌋))) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Bin0 (n: SFBin): SFBin := 
	exist _ (Bin0_u (⌊ n -⌋)) (Bin0_lem n). 
Definition Bin1_lem (n: SFBin): (SFBin_wf (Bin1_u (⌊ n -⌋))) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Bin1 (n: SFBin): SFBin := 
	exist _ (Bin1_u (⌊ n -⌋)) (Bin1_lem n). 
Definition SoftwareFoundations__Z_lem: (SFBin_wf SoftwareFoundations__Z_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition SoftwareFoundations__Z: SFBin := 
	exist _ SoftwareFoundations__Z_u SoftwareFoundations__Z_lem. 
Definition wf_Bin0_n [n: SFBin_u] (p: SFBin_wf (Bin0_u n)): SFBin_wf n. 
Proof. 
	quicksolve. 
Defined. 
Definition wf_Bin1_n [n: SFBin_u] (p: SFBin_wf (Bin1_u n)): SFBin_wf n. 
Proof. 
	quicksolve. 
Defined. 
#[global] Hint Resolve SFBin_wf_ref : wf_constr_db.
#[global] Hint Unfold SFBin_wf : wf_constr_db.
#[global] Hint Resolve SFBin_eq : ref_constr_db.
#[global] Hint Resolve wf_Bin0_n : ref_constr_db.
#[global] Hint Resolve wf_Bin1_n : ref_constr_db.
#[global] Hint Unfold Bin0 : ref_constr_db.
#[global] Hint Unfold Bin1 : ref_constr_db.
#[global] Hint Unfold SoftwareFoundations__Z : ref_constr_db.
Definition bin_to_nat_spec (m: SFBin): Type := 
	{VV: Z | True}. 
#[global] Hint Unfold bin_to_nat_spec : lia_unfold.
Definition bin_to_nat (m: SFBin): bin_to_nat_spec m. 
Proof. 
	destruct m as [m m_p]. 
	induction m as [(*Bin0*) m' IH_m' | (*Bin1*) m' IH_m' | (*SoftwareFoundations__Z*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ 
		((exist (fun (x_1: Z) => True) 2 (ltac: (solver))) *Z (subsumptionCast Z (fun (x_2: Z) => True) (IH_m' (ltac: (try clear IH_m'; 
	solver))) (ltac: (solver)))) _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ 
		((exist (fun (x_1: Z) => True) 1 (ltac: (solver))) +Z (subsumptionCast Z (fun (x_2: Z) => True) 
		((exist (fun (x_1: Z) => True) 2 (ltac: (solver))) *Z (subsumptionCast Z (fun (x_2: Z) => True) (IH_m' (ltac: (try clear IH_m'; 
	solver))) (ltac: (solver)))) (ltac: (solver)))) _); 
		solver.  
	  - intros . 
		refine (exist _ 0 _); 
		solver.  
Defined. 
Inductive bin_to_nat_rel : (SFBin_u -> (Z -> Prop)) := 
	 | bin_to_nat_SoftwareFoundations__Z: bin_to_nat_rel SoftwareFoundations__Z_u 0
	 | bin_to_nat_Bin0: (forall m' , forall (bin_to_natres: Z), (bin_to_nat_rel m' bin_to_natres) -> (forall (multZres: Z), (multZ_rel 2 bin_to_natres multZres) -> (bin_to_nat_rel (Bin0_u m') multZres)))
	 | bin_to_nat_Bin1: (forall m' , forall (bin_to_natres: Z), (bin_to_nat_rel m' bin_to_natres) -> (forall (multZres: Z), (multZ_rel 2 bin_to_natres multZres) -> (forall (addZres: Z), (addZ_rel 1 multZres addZres) -> (bin_to_nat_rel (Bin1_u m') addZres)))). 
#[global] Hint Constructors bin_to_nat_rel : core_hint_db.
#[global] Instance bin_to_nat_lookup_rel : dictionary rel bin_to_nat := { 
	lookup' := bin_to_nat_rel
}.
#[global] Instance bin_to_nat_getF : getFunc bin_to_nat_rel := { 
	getF' := bin_to_nat
}.
Theorem bin_to_nat_rel_funct [m: SFBin_u]: (forall (VV: Z) (VV': Z) (H: bin_to_nat_rel m VV) (K: bin_to_nat_rel m VV') , VV = VV'). 
Proof. 
	induction m as [(*Bin0*) m' IH_m' | (*Bin1*) m' IH_m' | (*SoftwareFoundations__Z*) ]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve bin_to_nat_rel_funct : f_rel_funct_db.
Theorem bin_to_nat_SoftwareFoundations__Z_lem (res: Z): (bin_to_nat_rel SoftwareFoundations__Z_u res) <-> (res = 0). 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite bin_to_nat_SoftwareFoundations__Z_lem : f_rel_back.
Theorem bin_to_nat_Bin0_lem (m': _) (multZres: Z): (bin_to_nat_rel (Bin0_u m') multZres) <-> (exists (bin_to_natres: Z), (bin_to_nat_rel m' bin_to_natres) /\ (multZ_rel 2 bin_to_natres multZres)). 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite bin_to_nat_Bin0_lem : f_rel_back.
Theorem bin_to_nat_Bin1_lem (m': _) (addZres: Z): (bin_to_nat_rel (Bin1_u m') addZres) <-> (exists (bin_to_natres: Z), (bin_to_nat_rel m' bin_to_natres) /\ (exists (multZres: Z), (multZ_rel 2 bin_to_natres multZres) /\ (addZ_rel 1 multZres addZres))). 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite bin_to_nat_Bin1_lem : f_rel_back.
Theorem bin_to_nat_rel_ex (m: SFBin_u) (m_p: (SFBin_wf m) /\ True): bin_to_nat_rel m (⌊ bin_to_nat (exist _ m m_p) -⌋). 
Proof. 
	Opaque bin_to_nat.
	existence_lemma_pre bin_to_nat; 
	induction m as [(*Bin0*) m' IH_m' | (*Bin1*) m' IH_m' | (*SoftwareFoundations__Z*) ]; 
	intros ; 
	[fix_notations; 
	pose proof (IH_m' (ltac: (try clear IH_m'; 
	solver))) as IH_40715420; 
	try clear IH_m'| 
	fix_notations; 
	pose proof (IH_m' (ltac: (try clear IH_m'; 
	solver))) as IH_40715420; 
	try clear IH_m'| 
	fix_notations]; 
	simpl in *. 
	Transparent bin_to_nat.
	all: existence_lemma_quicksolve bin_to_nat; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve bin_to_nat_rel_ex : rel_ax_db.
#[global] Opaque bin_to_nat. 
Theorem bin_to_nat__bin_to_nat_rel_rw (m: SFBin_u) (m_p: (SFBin_wf m) /\ True) (VV: Z): ((⌊ bin_to_nat (exist _ m m_p) -⌋) = VV) <-> (bin_to_nat_rel m VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite bin_to_nat__bin_to_nat_rel_rw : f_rel_funct_db.
#[global] Hint Resolve bin_to_nat__bin_to_nat_rel_rw : rel_ax_db.
#[global] Instance bin_to_nat_lookup_rw : dictionary rwLem bin_to_nat := { 
	lookup' := bin_to_nat__bin_to_nat_rel_rw
}.
Theorem bin_to_nat__bin_to_nat_rel (m_r: SFBin) (VV: Z): ((⌊ bin_to_nat m_r -⌋) = VV) <-> (bin_to_nat_rel (⌊ m_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite bin_to_nat__bin_to_nat_rel : f_rel_funct_db.
Theorem bin_to_nat__bin_to_nat_rel' (m: SFBin_u) (m_r: SFBin) (VV: Z): (m = (⌊ m_r -⌋)) -> (((⌊ bin_to_nat m_r -⌋) = VV) <-> (bin_to_nat_rel m VV)). 
Proof. 
	intros ->. 
	refine (bin_to_nat__bin_to_nat_rel m_r VV). 
Qed. 
#[global] Hint Resolve bin_to_nat__bin_to_nat_rel' : f_rel_funct_db.
Theorem bin_to_nat_rel_mk [m: SFBin_u] (m_p: (SFBin_wf m) /\ True): {VV: _ | bin_to_nat_rel m VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (bin_to_nat_rel m VV)) (bin_to_nat (exist _ m m_p)) _); 
	rewrite <- bin_to_nat__bin_to_nat_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve bin_to_nat_rel_mk : f_rel_funct_db.
#[global] Instance bin_to_natPack : (@Pack (SFBin ::RT (fun (m_r: SFBin) => nilRT)) (SFBin_u ::UT nilUT) (ltac: (mkProjectsArgListTG (SFBin ::RT (fun (m_r: SFBin) => nilRT)) (SFBin_u ::UT nilUT))) Z (fun (x_33798464: (ArgList SFBin ::RT (fun (m_r: SFBin) => nilRT))) => (fun (v_x_33798464: Z) => (ltac: (flattenP (fun (m_r: SFBin) => (fun (VV: Z) => True)) x_33798464 v_x_33798464))))).
Proof. 
	buildPackG bin_to_nat bin_to_nat_rel bin_to_nat__bin_to_nat_rel bin_to_nat_rel_funct. 
Defined.
Definition test_bin_incr4_spec: Type := 
	{{forall (bin_to_natres: Z), (bin_to_nat_rel (Bin0_u (Bin1_u SoftwareFoundations__Z_u)) bin_to_natres) -> (bin_to_natres == 2)}}. 
#[global] Hint Unfold test_bin_incr4_spec : lia_unfold.
Theorem test_bin_incr4: test_bin_incr4_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition incr_spec (m: SFBin): Type := 
	SFBin. 
#[global] Hint Unfold incr_spec : lia_unfold.
Definition incr (m: SFBin): incr_spec m. 
Proof. 
	destruct m as [m m_p]. 
	induction m as [(*Bin0*) m' IH_m' | (*Bin1*) m' IH_m' | (*SoftwareFoundations__Z*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ 
		(Bin1 
		(exist (fun (n: SFBin_u) => ((SFBin_wf n) /\ True)) m' (ltac: (solver)))) _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ 
		(Bin0 
		(subsumptionCast SFBin_u (fun (n: SFBin_u) => ((SFBin_wf n) /\ True)) (IH_m' (ltac: (try clear IH_m'; 
	solver))) (ltac: (solver)))) _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ 
		(Bin1 
		(subsumptionCast SFBin_u (fun (n: SFBin_u) => ((SFBin_wf n) /\ True)) SoftwareFoundations__Z (ltac: (solver)))) _); 
		solver.  
Defined. 
Inductive incr_rel : (SFBin_u -> (SFBin_u -> Prop)) := 
	 | incr_SoftwareFoundations__Z: incr_rel SoftwareFoundations__Z_u (Bin1_u SoftwareFoundations__Z_u)
	 | incr_Bin0: (forall m' , incr_rel (Bin0_u m') (Bin1_u m'))
	 | incr_Bin1: (forall m' , forall (incrres: SFBin_u), (incr_rel m' incrres) -> (incr_rel (Bin1_u m') (Bin0_u incrres))). 
#[global] Hint Constructors incr_rel : core_hint_db.
#[global] Instance incr_lookup_rel : dictionary rel incr := { 
	lookup' := incr_rel
}.
#[global] Instance incr_getF : getFunc incr_rel := { 
	getF' := incr
}.
Theorem incr_rel_funct [m: SFBin_u]: (forall (VV: SFBin_u) (VV': SFBin_u) (H: incr_rel m VV) (K: incr_rel m VV') , VV = VV'). 
Proof. 
	induction m as [(*Bin0*) m' IH_m' | (*Bin1*) m' IH_m' | (*SoftwareFoundations__Z*) ]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve incr_rel_funct : f_rel_funct_db.
Theorem incr_SoftwareFoundations__Z_lem: (incr_rel SoftwareFoundations__Z_u (Bin1_u SoftwareFoundations__Z_u)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite incr_SoftwareFoundations__Z_lem : f_rel_back.
Theorem incr_Bin0_lem (m': _): (incr_rel (Bin0_u m') (Bin1_u m')) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite incr_Bin0_lem : f_rel_back.
Theorem incr_Bin1_lem (m': _) (incrres: SFBin_u) (h_71748005: incr_rel m' incrres): (incr_rel (Bin1_u m') (Bin0_u incrres)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite incr_Bin1_lem : f_rel_back.
Theorem incr_rel_ex (m: SFBin_u) (m_p: (SFBin_wf m) /\ True): incr_rel m (⌊ incr (exist _ m m_p) -⌋). 
Proof. 
	Opaque incr.
	existence_lemma_pre incr; 
	induction m as [(*Bin0*) m' IH_m' | (*Bin1*) m' IH_m' | (*SoftwareFoundations__Z*) ]; 
	intros ; 
	[fix_notations; 
	try clear IH_m'| 
	fix_notations; 
	pose proof (IH_m' (ltac: (try clear IH_m'; 
	solver))) as IH_40715420; 
	try clear IH_m'| 
	fix_notations]; 
	simpl in *. 
	Transparent incr.
	all: existence_lemma_quicksolve incr; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve incr_rel_ex : rel_ax_db.
#[global] Opaque incr. 
Theorem incr__incr_rel_rw (m: SFBin_u) (m_p: (SFBin_wf m) /\ True) (VV: SFBin_u): ((⌊ incr (exist _ m m_p) -⌋) = VV) <-> (incr_rel m VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite incr__incr_rel_rw : f_rel_funct_db.
#[global] Hint Resolve incr__incr_rel_rw : rel_ax_db.
#[global] Instance incr_lookup_rw : dictionary rwLem incr := { 
	lookup' := incr__incr_rel_rw
}.
Theorem incr__incr_rel (m_r: SFBin) (VV: SFBin_u): ((⌊ incr m_r -⌋) = VV) <-> (incr_rel (⌊ m_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite incr__incr_rel : f_rel_funct_db.
Theorem incr__incr_rel' (m: SFBin_u) (m_r: SFBin) (VV: SFBin_u): (m = (⌊ m_r -⌋)) -> (((⌊ incr m_r -⌋) = VV) <-> (incr_rel m VV)). 
Proof. 
	intros ->. 
	refine (incr__incr_rel m_r VV). 
Qed. 
#[global] Hint Resolve incr__incr_rel' : f_rel_funct_db.
Theorem incr_rel_mk [m: SFBin_u] (m_p: (SFBin_wf m) /\ True): {VV: _ | incr_rel m VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (incr_rel m VV)) (incr (exist _ m m_p)) _); 
	rewrite <- incr__incr_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve incr_rel_mk : f_rel_funct_db.
#[global] Instance incrPack : (@Pack (SFBin ::RT (fun (m_r: SFBin) => nilRT)) (SFBin_u ::UT nilUT) (ltac: (mkProjectsArgListTG (SFBin ::RT (fun (m_r: SFBin) => nilRT)) (SFBin_u ::UT nilUT))) SFBin_u (fun (x_33798464: (ArgList SFBin ::RT (fun (m_r: SFBin) => nilRT))) => (fun (v_x_33798464: SFBin_u) => (ltac: (flattenP (fun (m_r: SFBin) => (fun (VV: SFBin_u) => ((SFBin_wf VV) /\ True))) x_33798464 v_x_33798464))))).
Proof. 
	buildPackG incr incr_rel incr__incr_rel incr_rel_funct. 
Defined.
Definition test_bin_incr1_spec: Type := 
	{{forall (incrres: SFBin_u), (incr_rel (Bin1_u SoftwareFoundations__Z_u) incrres) -> (incrres == (Bin0_u (Bin1_u SoftwareFoundations__Z_u)))}}. 
#[global] Hint Unfold test_bin_incr1_spec : lia_unfold.
Theorem test_bin_incr1: test_bin_incr1_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition test_bin_incr2_spec: Type := 
	{{forall (incrres: SFBin_u), (incr_rel (Bin0_u (Bin1_u SoftwareFoundations__Z_u)) incrres) -> (incrres == (Bin1_u (Bin1_u SoftwareFoundations__Z_u)))}}. 
#[global] Hint Unfold test_bin_incr2_spec : lia_unfold.
Theorem test_bin_incr2: test_bin_incr2_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition test_bin_incr3_spec: Type := 
	{{forall (incrres: SFBin_u), (incr_rel (Bin1_u (Bin1_u SoftwareFoundations__Z_u)) incrres) -> (incrres == (Bin0_u (Bin0_u (Bin1_u SoftwareFoundations__Z_u))))}}. 
#[global] Hint Unfold test_bin_incr3_spec : lia_unfold.
Theorem test_bin_incr3: test_bin_incr3_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition test_bin_incr5_spec: Type := 
	{{forall (incrres: SFBin_u), (incr_rel (Bin1_u SoftwareFoundations__Z_u) incrres) -> (forall (bin_to_natres: Z), (bin_to_nat_rel incrres bin_to_natres) -> (forall (bin_to_nat_res_2: Z), (bin_to_nat_rel (Bin1_u SoftwareFoundations__Z_u) bin_to_nat_res_2) -> (forall (addZres: Z), (addZ_rel 1 bin_to_nat_res_2 addZres) -> (bin_to_natres == addZres))))}}. 
#[global] Hint Unfold test_bin_incr5_spec : lia_unfold.
Theorem test_bin_incr5: test_bin_incr5_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition test_bin_incr6_spec: Type := 
	{{forall (incrres: SFBin_u), (incr_rel (Bin1_u SoftwareFoundations__Z_u) incrres) -> (forall (incr_res_2: SFBin_u), (incr_rel incrres incr_res_2) -> (forall (bin_to_natres: Z), (bin_to_nat_rel incr_res_2 bin_to_natres) -> (forall (bin_to_nat_res_2: Z), (bin_to_nat_rel (Bin1_u SoftwareFoundations__Z_u) bin_to_nat_res_2) -> (forall (addZres: Z), (addZ_rel 2 bin_to_nat_res_2 addZres) -> (bin_to_natres == addZres)))))}}. 
#[global] Hint Unfold test_bin_incr6_spec : lia_unfold.
Theorem test_bin_incr6: test_bin_incr6_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Inductive RGB_u : Type := 
	 | Blue_u: RGB_u
	 | Green_u: RGB_u
	 | Red_u: RGB_u. 
Fixpoint RGB_eq (x: RGB_u) (y: RGB_u): bool := 
	match (x, y) with (Blue_u, Blue_u) => true | (Green_u, Green_u) => true | (Red_u, Red_u) => true | (_, _) => false end. 
Theorem RGB_eq_refl: (forall (x: RGB_u) , is_true (RGB_eq x x)). 
Proof. 
	eq_refl_rec. 
Qed. 
#[global] Hint Resolve RGB_eq_refl : eq_hint_db.
Theorem RGB_eqb_eq: (forall (s: RGB_u) (t: RGB_u) , (is_true (RGB_eq s t)) -> (s = t)). 
Proof. 
	eqb_eq_lem. 
Qed. 
#[global] Hint Resolve RGB_eqb_eq : eq_hint_db.
#[global] Instance leibnitz_eq_RGB : LeibnitzEqB := { 
	equalB' := RGB_eq;
	refl' := RGB_eq_refl;
	eqb_eq' := RGB_eqb_eq
}.
Fixpoint RGB_wf (x: RGB_u): Prop := 
	match x with Blue_u => True | Green_u => True | Red_u => True end. 
Theorem RGB_wf_ref [p: RGB_u -> Prop] (tm: {v: RGB_u | (RGB_wf v) /\ (p v)}): RGB_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation RGB := {x: RGB_u | (RGB_wf x) /\ True}. 
Definition Blue_lem: (RGB_wf Blue_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Blue: RGB := 
	exist _ Blue_u Blue_lem. 
Definition Green_lem: (RGB_wf Green_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Green: RGB := 
	exist _ Green_u Green_lem. 
Definition Red_lem: (RGB_wf Red_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Red: RGB := 
	exist _ Red_u Red_lem. 
#[global] Hint Resolve RGB_wf_ref : wf_constr_db.
#[global] Hint Unfold RGB_wf : wf_constr_db.
#[global] Hint Resolve RGB_eq : ref_constr_db.
#[global] Hint Unfold Blue : ref_constr_db.
#[global] Hint Unfold Green : ref_constr_db.
#[global] Hint Unfold Red : ref_constr_db.
Inductive OtherNat_u : Type := 
	 | Stop_u: OtherNat_u
	 | Tick_u: OtherNat_u -> OtherNat_u. 
Fixpoint OtherNat_eq (x: OtherNat_u) (y: OtherNat_u): bool := 
	match (x, y) with (Stop_u, Stop_u) => true | (Tick_u x, Tick_u x') => (true && (OtherNat_eq x x')) | (_, _) => false end. 
Theorem OtherNat_eq_refl: (forall (x: OtherNat_u) , is_true (OtherNat_eq x x)). 
Proof. 
	eq_refl_rec. 
Qed. 
#[global] Hint Resolve OtherNat_eq_refl : eq_hint_db.
Theorem OtherNat_eqb_eq: (forall (s: OtherNat_u) (t: OtherNat_u) , (is_true (OtherNat_eq s t)) -> (s = t)). 
Proof. 
	eqb_eq_lem. 
Qed. 
#[global] Hint Resolve OtherNat_eqb_eq : eq_hint_db.
#[global] Instance leibnitz_eq_OtherNat : LeibnitzEqB := { 
	equalB' := OtherNat_eq;
	refl' := OtherNat_eq_refl;
	eqb_eq' := OtherNat_eqb_eq
}.
Fixpoint OtherNat_wf (x: OtherNat_u): Prop := 
	match x with Stop_u => True | (Tick_u VV) => ((OtherNat_wf VV) /\ True) end. 
Theorem OtherNat_wf_ref [p: OtherNat_u -> Prop] (tm: {v: OtherNat_u | (OtherNat_wf v) /\ (p v)}): OtherNat_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation OtherNat := {x: OtherNat_u | (OtherNat_wf x) /\ True}. 
Definition Stop_lem: (OtherNat_wf Stop_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Stop: OtherNat := 
	exist _ Stop_u Stop_lem. 
Definition Tick_lem (VV: OtherNat): (OtherNat_wf (Tick_u (⌊ VV -⌋))) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Tick (VV: OtherNat): OtherNat := 
	exist _ (Tick_u (⌊ VV -⌋)) (Tick_lem VV). 
Definition wf_Tick_VV [VV: OtherNat_u] (p: OtherNat_wf (Tick_u VV)): OtherNat_wf VV. 
Proof. 
	quicksolve. 
Defined. 
#[global] Hint Resolve OtherNat_wf_ref : wf_constr_db.
#[global] Hint Unfold OtherNat_wf : wf_constr_db.
#[global] Hint Resolve OtherNat_eq : ref_constr_db.
#[global] Hint Resolve wf_Tick_VV : ref_constr_db.
#[global] Hint Unfold Stop : ref_constr_db.
#[global] Hint Unfold Tick : ref_constr_db.
Inductive Nibble_u : Type := 
	 | Bits_u: SFBit_u -> (SFBit_u -> (SFBit_u -> (SFBit_u -> Nibble_u))). 
Fixpoint Nibble_eq (x: Nibble_u) (y: Nibble_u): bool := 
	match (x, y) with (Bits_u x x_1 x_2 x_3, Bits_u x' x_1' x_2' x_3') => ((((true && (x ==? x')) && (x_1 ==? x_1')) && (x_2 ==? x_2')) && (x_3 ==? x_3')) end. 
Theorem Nibble_eq_refl: (forall (x: Nibble_u) , is_true (Nibble_eq x x)). 
Proof. 
	eq_refl_rec. 
Qed. 
#[global] Hint Resolve Nibble_eq_refl : eq_hint_db.
Theorem Nibble_eqb_eq: (forall (s: Nibble_u) (t: Nibble_u) , (is_true (Nibble_eq s t)) -> (s = t)). 
Proof. 
	eqb_eq_lem. 
Qed. 
#[global] Hint Resolve Nibble_eqb_eq : eq_hint_db.
#[global] Instance leibnitz_eq_Nibble : LeibnitzEqB := { 
	equalB' := Nibble_eq;
	refl' := Nibble_eq_refl;
	eqb_eq' := Nibble_eqb_eq
}.
Fixpoint Nibble_wf (x: Nibble_u): Prop := 
	match x with (Bits_u VV VV_ VV__ VV___) => (((((SFBit_wf VV) /\ True) /\ ((SFBit_wf VV_) /\ True)) /\ ((SFBit_wf VV__) /\ True)) /\ ((SFBit_wf VV___) /\ True)) end. 
Theorem Nibble_wf_ref [p: Nibble_u -> Prop] (tm: {v: Nibble_u | (Nibble_wf v) /\ (p v)}): Nibble_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation Nibble := {x: Nibble_u | (Nibble_wf x) /\ True}. 
Definition Bits_lem (VV: SFBit) (VV_: SFBit) (VV__: SFBit) (VV___: SFBit): (Nibble_wf (Bits_u (⌊ VV -⌋) (⌊ VV_ -⌋) (⌊ VV__ -⌋) (⌊ VV___ -⌋))) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Bits (VV: SFBit) (VV_: SFBit) (VV__: SFBit) (VV___: SFBit): Nibble := 
	exist _ (Bits_u (⌊ VV -⌋) (⌊ VV_ -⌋) (⌊ VV__ -⌋) (⌊ VV___ -⌋)) (Bits_lem VV VV_ VV__ VV___). 
#[global] Hint Resolve Nibble_wf_ref : wf_constr_db.
#[global] Hint Unfold Nibble_wf : wf_constr_db.
#[global] Hint Resolve Nibble_eq : ref_constr_db.
#[global] Hint Unfold Bits : ref_constr_db.
Definition allzero_spec (lq_tmp0: Nibble): Type := 
	SFBool. 
#[global] Hint Unfold allzero_spec : lia_unfold.
Definition allzero (lq_tmp0: Nibble): allzero_spec lq_tmp0. 
Proof. 
	destruct lq_tmp0 as [lq_tmp0 lq_tmp0_p]. 
	induction lq_tmp0 as [(*Bits*) ds_d5TQ ds_d5TR ds_d5TS ds_d5TT]. 
	  - intros . 
		induction ds_d5TQ as [(*B0*)  | (*B1*) ]. 
		  -- intros . 
			induction ds_d5TR as [(*B0*)  | (*B1*) ]. 
			  --- intros . 
				induction ds_d5TS as [(*B0*)  | (*B1*) ]. 
				  ---- intros . 
					induction ds_d5TT as [(*B0*)  | (*B1*) ]. 
					  ----- intros . 
						refine (subsumptionCast _ _ SFTrue _); 
						solver.  
					  ----- intros . 
						refine (subsumptionCast _ _ SFFalse _); 
						solver.   
				  ---- intros . 
					refine (subsumptionCast _ _ SFFalse _); 
					solver.   
			  --- intros . 
				refine (subsumptionCast _ _ SFFalse _); 
				solver.   
		  -- intros . 
			refine (subsumptionCast _ _ SFFalse _); 
			solver.   
Defined. 
Inductive MyNat_u : Type := 
	 | O_u: MyNat_u
	 | S_u: MyNat_u -> MyNat_u. 
Fixpoint MyNat_eq (x: MyNat_u) (y: MyNat_u): bool := 
	match (x, y) with (O_u, O_u) => true | (S_u x, S_u x') => (true && (MyNat_eq x x')) | (_, _) => false end. 
Theorem MyNat_eq_refl: (forall (x: MyNat_u) , is_true (MyNat_eq x x)). 
Proof. 
	eq_refl_rec. 
Qed. 
#[global] Hint Resolve MyNat_eq_refl : eq_hint_db.
Theorem MyNat_eqb_eq: (forall (s: MyNat_u) (t: MyNat_u) , (is_true (MyNat_eq s t)) -> (s = t)). 
Proof. 
	eqb_eq_lem. 
Qed. 
#[global] Hint Resolve MyNat_eqb_eq : eq_hint_db.
#[global] Instance leibnitz_eq_MyNat : LeibnitzEqB := { 
	equalB' := MyNat_eq;
	refl' := MyNat_eq_refl;
	eqb_eq' := MyNat_eqb_eq
}.
Fixpoint MyNat_wf (x: MyNat_u): Prop := 
	match x with O_u => True | (S_u VV) => ((MyNat_wf VV) /\ True) end. 
Theorem MyNat_wf_ref [p: MyNat_u -> Prop] (tm: {v: MyNat_u | (MyNat_wf v) /\ (p v)}): MyNat_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation MyNat := {x: MyNat_u | (MyNat_wf x) /\ True}. 
Definition O_lem: (MyNat_wf O_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition O: MyNat := 
	exist _ O_u O_lem. 
Definition S_lem (VV: MyNat): (MyNat_wf (S_u (⌊ VV -⌋))) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition S (VV: MyNat): MyNat := 
	exist _ (S_u (⌊ VV -⌋)) (S_lem VV). 
Definition wf_S_VV [VV: MyNat_u] (p: MyNat_wf (S_u VV)): MyNat_wf VV. 
Proof. 
	quicksolve. 
Defined. 
#[global] Hint Resolve MyNat_wf_ref : wf_constr_db.
#[global] Hint Unfold MyNat_wf : wf_constr_db.
#[global] Hint Resolve MyNat_eq : ref_constr_db.
#[global] Hint Resolve wf_S_VV : ref_constr_db.
#[global] Hint Unfold O : ref_constr_db.
#[global] Hint Unfold S : ref_constr_db.
Inductive Natprod_u : Type := 
	 | Pair_u: MyNat_u -> (MyNat_u -> Natprod_u). 
Fixpoint Natprod_eq (x: Natprod_u) (y: Natprod_u): bool := 
	match (x, y) with (Pair_u x x_1, Pair_u x' x_1') => ((true && (x ==? x')) && (x_1 ==? x_1')) end. 
Theorem Natprod_eq_refl: (forall (x: Natprod_u) , is_true (Natprod_eq x x)). 
Proof. 
	eq_refl_rec. 
Qed. 
#[global] Hint Resolve Natprod_eq_refl : eq_hint_db.
Theorem Natprod_eqb_eq: (forall (s: Natprod_u) (t: Natprod_u) , (is_true (Natprod_eq s t)) -> (s = t)). 
Proof. 
	eqb_eq_lem. 
Qed. 
#[global] Hint Resolve Natprod_eqb_eq : eq_hint_db.
#[global] Instance leibnitz_eq_Natprod : LeibnitzEqB := { 
	equalB' := Natprod_eq;
	refl' := Natprod_eq_refl;
	eqb_eq' := Natprod_eqb_eq
}.
Fixpoint Natprod_wf (x: Natprod_u): Prop := 
	match x with (Pair_u n1 n2) => (((MyNat_wf n1) /\ True) /\ ((MyNat_wf n2) /\ True)) end. 
Theorem Natprod_wf_ref [p: Natprod_u -> Prop] (tm: {v: Natprod_u | (Natprod_wf v) /\ (p v)}): Natprod_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation Natprod := {x: Natprod_u | (Natprod_wf x) /\ True}. 
Definition Pair_lem (n1: MyNat) (n2: MyNat): (Natprod_wf (Pair_u (⌊ n1 -⌋) (⌊ n2 -⌋))) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Pair (n1: MyNat) (n2: MyNat): Natprod := 
	exist _ (Pair_u (⌊ n1 -⌋) (⌊ n2 -⌋)) (Pair_lem n1 n2). 
#[global] Hint Resolve Natprod_wf_ref : wf_constr_db.
#[global] Hint Unfold Natprod_wf : wf_constr_db.
#[global] Hint Resolve Natprod_eq : ref_constr_db.
#[global] Hint Unfold Pair : ref_constr_db.
Definition swap_pair_spec (p: Natprod): Type := 
	Natprod. 
#[global] Hint Unfold swap_pair_spec : lia_unfold.
Definition swap_pair (p: Natprod): swap_pair_spec p. 
Proof. 
	destruct p as [p p_p]. 
	induction p as [(*Pair*) x y]. 
	  - intros . 
		refine (subsumptionCast _ _ 
		(Pair 
		(exist (fun (n1: MyNat_u) => ((MyNat_wf n1) /\ True)) y (ltac: (solver))) 
		(exist (fun (n2: MyNat_u) => ((MyNat_wf n2) /\ True)) x (ltac: (solver)))) _); 
		solver.  
Defined. 
Inductive swap_pair_rel : (Natprod_u -> (Natprod_u -> Prop)) := 
	 | swap_pair_Pair: (forall x y , swap_pair_rel (Pair_u x y) (Pair_u y x)). 
#[global] Hint Constructors swap_pair_rel : core_hint_db.
#[global] Instance swap_pair_lookup_rel : dictionary rel swap_pair := { 
	lookup' := swap_pair_rel
}.
#[global] Instance swap_pair_getF : getFunc swap_pair_rel := { 
	getF' := swap_pair
}.
Theorem swap_pair_rel_funct [p: Natprod_u]: (forall (VV: Natprod_u) (VV': Natprod_u) (H: swap_pair_rel p VV) (K: swap_pair_rel p VV') , VV = VV'). 
Proof. 
	induction p as [(*Pair*) x y]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve swap_pair_rel_funct : f_rel_funct_db.
Theorem swap_pair_Pair_lem (x: _) (y: _): (swap_pair_rel (Pair_u x y) (Pair_u y x)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite swap_pair_Pair_lem : f_rel_back.
Theorem swap_pair_rel_ex (p: Natprod_u) (p_p: (Natprod_wf p) /\ True): swap_pair_rel p (⌊ swap_pair (exist _ p p_p) -⌋). 
Proof. 
	Opaque swap_pair.
	existence_lemma_pre swap_pair; 
	induction p as [(*Pair*) x y]; 
	intros ; 
	[fix_notations]; 
	simpl in *. 
	Transparent swap_pair.
	all: existence_lemma_quicksolve swap_pair; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve swap_pair_rel_ex : rel_ax_db.
#[global] Opaque swap_pair. 
Theorem swap_pair__swap_pair_rel_rw (p: Natprod_u) (p_p: (Natprod_wf p) /\ True) (VV: Natprod_u): ((⌊ swap_pair (exist _ p p_p) -⌋) = VV) <-> (swap_pair_rel p VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite swap_pair__swap_pair_rel_rw : f_rel_funct_db.
#[global] Hint Resolve swap_pair__swap_pair_rel_rw : rel_ax_db.
#[global] Instance swap_pair_lookup_rw : dictionary rwLem swap_pair := { 
	lookup' := swap_pair__swap_pair_rel_rw
}.
Theorem swap_pair__swap_pair_rel (p_r: Natprod) (VV: Natprod_u): ((⌊ swap_pair p_r -⌋) = VV) <-> (swap_pair_rel (⌊ p_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite swap_pair__swap_pair_rel : f_rel_funct_db.
Theorem swap_pair__swap_pair_rel' (p: Natprod_u) (p_r: Natprod) (VV: Natprod_u): (p = (⌊ p_r -⌋)) -> (((⌊ swap_pair p_r -⌋) = VV) <-> (swap_pair_rel p VV)). 
Proof. 
	intros ->. 
	refine (swap_pair__swap_pair_rel p_r VV). 
Qed. 
#[global] Hint Resolve swap_pair__swap_pair_rel' : f_rel_funct_db.
Theorem swap_pair_rel_mk [p: Natprod_u] (p_p: (Natprod_wf p) /\ True): {VV: _ | swap_pair_rel p VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (swap_pair_rel p VV)) (swap_pair (exist _ p p_p)) _); 
	rewrite <- swap_pair__swap_pair_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve swap_pair_rel_mk : f_rel_funct_db.
#[global] Instance swap_pairPack : (@Pack (Natprod ::RT (fun (p_r: Natprod) => nilRT)) (Natprod_u ::UT nilUT) (ltac: (mkProjectsArgListTG (Natprod ::RT (fun (p_r: Natprod) => nilRT)) (Natprod_u ::UT nilUT))) Natprod_u (fun (x_54217211: (ArgList Natprod ::RT (fun (p_r: Natprod) => nilRT))) => (fun (v_x_54217211: Natprod_u) => (ltac: (flattenP (fun (p_r: Natprod) => (fun (VV: Natprod_u) => ((Natprod_wf VV) /\ True))) x_54217211 v_x_54217211))))).
Proof. 
	buildPackG swap_pair swap_pair_rel swap_pair__swap_pair_rel swap_pair_rel_funct. 
Defined.
Definition eqb_spec (n: MyNat) (m: MyNat): Type := 
	SFBool. 
#[global] Hint Unfold eqb_spec : lia_unfold.
Definition eqb (n: MyNat) (m: MyNat): eqb_spec n m. 
Proof. 
	destruct n as [n n_p]. 
	destruct m as [m m_p]. 
	try revert m_p; generalize dependent m; 
	induction n as [(*O*)  | (*S*) n' IH_n']. 
	  - intros . 
		induction m as [(*O*)  | (*S*) m' IH_m']. 
		  -- intros . 
			refine (subsumptionCast _ _ SFTrue _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ SFFalse _); 
			solver.   
	  - intros . 
		induction m as [(*O*)  | (*S*) m' IH_m']. 
		  -- intros . 
			refine (subsumptionCast _ _ SFFalse _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ 
		(IH_n' (ltac: (try clear IH_n'; 
	solver)) m' (ltac: (try clear IH_n'; 
	solver))) _); 
			solver.   
Defined. 
Inductive eqb_rel : (MyNat_u -> (MyNat_u -> (SFBool_u -> Prop))) := 
	 | eqb_O_O: eqb_rel O_u O_u SFTrue_u
	 | eqb_O_S: (forall m' , eqb_rel O_u (S_u m') SFFalse_u)
	 | eqb_S_O: (forall n' , eqb_rel (S_u n') O_u SFFalse_u)
	 | eqb_S_S: (forall m' n' , forall (eqbres: SFBool_u), (eqb_rel n' m' eqbres) -> (eqb_rel (S_u n') (S_u m') eqbres)). 
#[global] Hint Constructors eqb_rel : core_hint_db.
#[global] Instance eqb_lookup_rel : dictionary rel eqb := { 
	lookup' := eqb_rel
}.
#[global] Instance eqb_getF : getFunc eqb_rel := { 
	getF' := eqb
}.
Theorem eqb_rel_funct [n: MyNat_u] [m: MyNat_u]: (forall (VV: SFBool_u) (VV': SFBool_u) (H: eqb_rel n m VV) (K: eqb_rel n m VV') , VV = VV'). 
Proof. 
	try revert m_p; generalize dependent m; 
	induction n as [(*O*)  | (*S*) n' IH_n']; 
	intros ; 
	[induction m as [(*O*)  | (*S*) m' IH_m']; 
	intros | 
	induction m as [(*O*)  | (*S*) m' IH_m']; 
	intros ]; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve eqb_rel_funct : f_rel_funct_db.
Theorem eqb_O_O_lem: (eqb_rel O_u O_u SFTrue_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite eqb_O_O_lem : f_rel_back.
Theorem eqb_O_S_lem (m': _): (eqb_rel O_u (S_u m') SFFalse_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite eqb_O_S_lem : f_rel_back.
Theorem eqb_S_O_lem (n': _): (eqb_rel (S_u n') O_u SFFalse_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite eqb_S_O_lem : f_rel_back.
Theorem eqb_S_S_lem (n': _) (m': _) (eqbres: SFBool_u) (h_60856709: eqb_rel n' m' eqbres): (eqb_rel (S_u n') (S_u m') eqbres) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite eqb_S_S_lem : f_rel_back.
Theorem eqb_rel_ex (n: MyNat_u) (m: MyNat_u) (n_p: (MyNat_wf n) /\ True) (m_p: (MyNat_wf m) /\ True): eqb_rel n m (⌊ eqb (exist _ n n_p) (exist _ m m_p) -⌋). 
Proof. 
	Opaque eqb.
	existence_lemma_pre eqb; 
	try revert m_p; generalize dependent m; 
	induction n as [(*O*)  | (*S*) n' IH_n']; 
	intros ; 
	[induction m as [(*O*)  | (*S*) m' IH_m']; 
	intros ; 
	[fix_notations| 
	fix_notations; 
	try clear IH_m']| 
	induction m as [(*O*)  | (*S*) m' IH_m']; 
	intros ; 
	[fix_notations; 
	try clear IH_n'| 
	fix_notations; 
	pose proof (IH_n' (ltac: (try clear IH_n'; 
	solver)) m' (ltac: (try clear IH_n'; 
	solver))) as IH_48190612; 
	try clear IH_n'; 
	try clear IH_m']]; 
	simpl in *. 
	Transparent eqb.
	all: existence_lemma_quicksolve eqb; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve eqb_rel_ex : rel_ax_db.
#[global] Opaque eqb. 
Theorem eqb__eqb_rel_rw (n: MyNat_u) (m: MyNat_u) (n_p: (MyNat_wf n) /\ True) (m_p: (MyNat_wf m) /\ True) (VV: SFBool_u): ((⌊ eqb (exist _ n n_p) (exist _ m m_p) -⌋) = VV) <-> (eqb_rel n m VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite eqb__eqb_rel_rw : f_rel_funct_db.
#[global] Hint Resolve eqb__eqb_rel_rw : rel_ax_db.
#[global] Instance eqb_lookup_rw : dictionary rwLem eqb := { 
	lookup' := eqb__eqb_rel_rw
}.
Theorem eqb__eqb_rel (n_r: MyNat) (m_r: MyNat) (VV: SFBool_u): ((⌊ eqb n_r m_r -⌋) = VV) <-> (eqb_rel (⌊ n_r -⌋) (⌊ m_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite eqb__eqb_rel : f_rel_funct_db.
Theorem eqb__eqb_rel' (n: MyNat_u) (m: MyNat_u) (n_r: MyNat) (m_r: MyNat) (VV: SFBool_u): (n = (⌊ n_r -⌋)) -> ((m = (⌊ m_r -⌋)) -> (((⌊ eqb n_r m_r -⌋) = VV) <-> (eqb_rel n m VV))). 
Proof. 
	intros -> ->. 
	refine (eqb__eqb_rel n_r m_r VV). 
Qed. 
#[global] Hint Resolve eqb__eqb_rel' : f_rel_funct_db.
Theorem eqb_rel_mk [n: MyNat_u] [m: MyNat_u] (n_p: (MyNat_wf n) /\ True) (m_p: (MyNat_wf m) /\ True): {VV: _ | eqb_rel n m VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (eqb_rel n m VV)) (eqb (exist _ n n_p) (exist _ m m_p)) _); 
	rewrite <- eqb__eqb_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve eqb_rel_mk : f_rel_funct_db.
#[global] Instance eqbPack : (@Pack (MyNat ::RT (fun (n_r: MyNat) => (MyNat ::RT (fun (m_r: MyNat) => nilRT)))) (MyNat_u ::UT (MyNat_u ::UT nilUT)) (ltac: (mkProjectsArgListTG (MyNat ::RT (fun (n_r: MyNat) => (MyNat ::RT (fun (m_r: MyNat) => nilRT)))) (MyNat_u ::UT (MyNat_u ::UT nilUT)))) SFBool_u (fun (x_29372127: (ArgList MyNat ::RT (fun (n_r: MyNat) => (MyNat ::RT (fun (m_r: MyNat) => nilRT))))) => (fun (v_x_29372127: SFBool_u) => (ltac: (flattenP (fun (n_r: MyNat) => (fun (m_r: MyNat) => (fun (VV: SFBool_u) => ((SFBool_wf VV) /\ True)))) x_29372127 v_x_29372127))))).
Proof. 
	buildPackG eqb eqb_rel eqb__eqb_rel eqb_rel_funct. 
Defined.
Definition fstSF_spec (p: Natprod): Type := 
	MyNat. 
#[global] Hint Unfold fstSF_spec : lia_unfold.
Definition fstSF (p: Natprod): fstSF_spec p. 
Proof. 
	destruct p as [p p_p]. 
	induction p as [(*Pair*) n1 n2]. 
	  - intros . 
		refine (exist _ n1 _); 
		solver.  
Defined. 
Inductive fstSF_rel : (Natprod_u -> (MyNat_u -> Prop)) := 
	 | fstSF_Pair: (forall n1 n2 , fstSF_rel (Pair_u n1 n2) n1). 
#[global] Hint Constructors fstSF_rel : core_hint_db.
#[global] Instance fstSF_lookup_rel : dictionary rel fstSF := { 
	lookup' := fstSF_rel
}.
#[global] Instance fstSF_getF : getFunc fstSF_rel := { 
	getF' := fstSF
}.
Theorem fstSF_rel_funct [p: Natprod_u]: (forall (VV: MyNat_u) (VV': MyNat_u) (H: fstSF_rel p VV) (K: fstSF_rel p VV') , VV = VV'). 
Proof. 
	induction p as [(*Pair*) n1 n2]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve fstSF_rel_funct : f_rel_funct_db.
Theorem fstSF_Pair_lem (n1: _) (n2: _): (fstSF_rel (Pair_u n1 n2) n1) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite fstSF_Pair_lem : f_rel_back.
Theorem fstSF_rel_ex (p: Natprod_u) (p_p: (Natprod_wf p) /\ True): fstSF_rel p (⌊ fstSF (exist _ p p_p) -⌋). 
Proof. 
	Opaque fstSF.
	existence_lemma_pre fstSF; 
	induction p as [(*Pair*) n1 n2]; 
	intros ; 
	[fix_notations]; 
	simpl in *. 
	Transparent fstSF.
	all: existence_lemma_quicksolve fstSF; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve fstSF_rel_ex : rel_ax_db.
#[global] Opaque fstSF. 
Theorem fstSF__fstSF_rel_rw (p: Natprod_u) (p_p: (Natprod_wf p) /\ True) (VV: MyNat_u): ((⌊ fstSF (exist _ p p_p) -⌋) = VV) <-> (fstSF_rel p VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite fstSF__fstSF_rel_rw : f_rel_funct_db.
#[global] Hint Resolve fstSF__fstSF_rel_rw : rel_ax_db.
#[global] Instance fstSF_lookup_rw : dictionary rwLem fstSF := { 
	lookup' := fstSF__fstSF_rel_rw
}.
Theorem fstSF__fstSF_rel (p_r: Natprod) (VV: MyNat_u): ((⌊ fstSF p_r -⌋) = VV) <-> (fstSF_rel (⌊ p_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite fstSF__fstSF_rel : f_rel_funct_db.
Theorem fstSF__fstSF_rel' (p: Natprod_u) (p_r: Natprod) (VV: MyNat_u): (p = (⌊ p_r -⌋)) -> (((⌊ fstSF p_r -⌋) = VV) <-> (fstSF_rel p VV)). 
Proof. 
	intros ->. 
	refine (fstSF__fstSF_rel p_r VV). 
Qed. 
#[global] Hint Resolve fstSF__fstSF_rel' : f_rel_funct_db.
Theorem fstSF_rel_mk [p: Natprod_u] (p_p: (Natprod_wf p) /\ True): {VV: _ | fstSF_rel p VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (fstSF_rel p VV)) (fstSF (exist _ p p_p)) _); 
	rewrite <- fstSF__fstSF_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve fstSF_rel_mk : f_rel_funct_db.
#[global] Instance fstSFPack : (@Pack (Natprod ::RT (fun (p_r: Natprod) => nilRT)) (Natprod_u ::UT nilUT) (ltac: (mkProjectsArgListTG (Natprod ::RT (fun (p_r: Natprod) => nilRT)) (Natprod_u ::UT nilUT))) MyNat_u (fun (x_54217211: (ArgList Natprod ::RT (fun (p_r: Natprod) => nilRT))) => (fun (v_x_54217211: MyNat_u) => (ltac: (flattenP (fun (p_r: Natprod) => (fun (VV: MyNat_u) => ((MyNat_wf VV) /\ True))) x_54217211 v_x_54217211))))).
Proof. 
	buildPackG fstSF fstSF_rel fstSF__fstSF_rel fstSF_rel_funct. 
Defined.
Definition leb_spec (n: MyNat) (m: MyNat): Type := 
	SFBool. 
#[global] Hint Unfold leb_spec : lia_unfold.
Definition leb (n: MyNat) (m: MyNat): leb_spec n m. 
Proof. 
	destruct n as [n n_p]. 
	destruct m as [m m_p]. 
	try revert m_p; generalize dependent m; 
	induction n as [(*O*)  | (*S*) n' IH_n']. 
	  - intros . 
		refine (subsumptionCast _ _ SFTrue _); 
		solver.  
	  - intros . 
		induction m as [(*O*)  | (*S*) m' IH_m']. 
		  -- intros . 
			refine (subsumptionCast _ _ SFFalse _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ 
		(IH_n' (ltac: (try clear IH_n'; 
	solver)) m' (ltac: (try clear IH_n'; 
	solver))) _); 
			solver.   
Defined. 
Inductive leb_rel : (MyNat_u -> (MyNat_u -> (SFBool_u -> Prop))) := 
	 | leb_O: (forall m , leb_rel O_u m SFTrue_u)
	 | leb_S_O: (forall n' , leb_rel (S_u n') O_u SFFalse_u)
	 | leb_S_S: (forall m' n' , forall (lebres: SFBool_u), (leb_rel n' m' lebres) -> (leb_rel (S_u n') (S_u m') lebres)). 
#[global] Hint Constructors leb_rel : core_hint_db.
#[global] Instance leb_lookup_rel : dictionary rel leb := { 
	lookup' := leb_rel
}.
#[global] Instance leb_getF : getFunc leb_rel := { 
	getF' := leb
}.
Theorem leb_rel_funct [n: MyNat_u] [m: MyNat_u]: (forall (VV: SFBool_u) (VV': SFBool_u) (H: leb_rel n m VV) (K: leb_rel n m VV') , VV = VV'). 
Proof. 
	try revert m_p; generalize dependent m; 
	induction n as [(*O*)  | (*S*) n' IH_n']; 
	intros ; 
	[| 
	induction m as [(*O*)  | (*S*) m' IH_m']; 
	intros ]; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve leb_rel_funct : f_rel_funct_db.
Theorem leb_O_lem (m: _): (leb_rel O_u m SFTrue_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite leb_O_lem : f_rel_back.
Theorem leb_S_O_lem (n': _): (leb_rel (S_u n') O_u SFFalse_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite leb_S_O_lem : f_rel_back.
Theorem leb_S_S_lem (n': _) (m': _) (lebres: SFBool_u) (h_77258034: leb_rel n' m' lebres): (leb_rel (S_u n') (S_u m') lebres) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite leb_S_S_lem : f_rel_back.
Theorem leb_rel_ex (n: MyNat_u) (m: MyNat_u) (n_p: (MyNat_wf n) /\ True) (m_p: (MyNat_wf m) /\ True): leb_rel n m (⌊ leb (exist _ n n_p) (exist _ m m_p) -⌋). 
Proof. 
	Opaque leb.
	existence_lemma_pre leb; 
	try revert m_p; generalize dependent m; 
	induction n as [(*O*)  | (*S*) n' IH_n']; 
	intros ; 
	[fix_notations| 
	induction m as [(*O*)  | (*S*) m' IH_m']; 
	intros ; 
	[fix_notations; 
	try clear IH_n'| 
	fix_notations; 
	pose proof (IH_n' (ltac: (try clear IH_n'; 
	solver)) m' (ltac: (try clear IH_n'; 
	solver))) as IH_48190612; 
	try clear IH_n'; 
	try clear IH_m']]; 
	simpl in *. 
	Transparent leb.
	all: existence_lemma_quicksolve leb; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve leb_rel_ex : rel_ax_db.
#[global] Opaque leb. 
Theorem leb__leb_rel_rw (n: MyNat_u) (m: MyNat_u) (n_p: (MyNat_wf n) /\ True) (m_p: (MyNat_wf m) /\ True) (VV: SFBool_u): ((⌊ leb (exist _ n n_p) (exist _ m m_p) -⌋) = VV) <-> (leb_rel n m VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite leb__leb_rel_rw : f_rel_funct_db.
#[global] Hint Resolve leb__leb_rel_rw : rel_ax_db.
#[global] Instance leb_lookup_rw : dictionary rwLem leb := { 
	lookup' := leb__leb_rel_rw
}.
Theorem leb__leb_rel (n_r: MyNat) (m_r: MyNat) (VV: SFBool_u): ((⌊ leb n_r m_r -⌋) = VV) <-> (leb_rel (⌊ n_r -⌋) (⌊ m_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite leb__leb_rel : f_rel_funct_db.
Theorem leb__leb_rel' (n: MyNat_u) (m: MyNat_u) (n_r: MyNat) (m_r: MyNat) (VV: SFBool_u): (n = (⌊ n_r -⌋)) -> ((m = (⌊ m_r -⌋)) -> (((⌊ leb n_r m_r -⌋) = VV) <-> (leb_rel n m VV))). 
Proof. 
	intros -> ->. 
	refine (leb__leb_rel n_r m_r VV). 
Qed. 
#[global] Hint Resolve leb__leb_rel' : f_rel_funct_db.
Theorem leb_rel_mk [n: MyNat_u] [m: MyNat_u] (n_p: (MyNat_wf n) /\ True) (m_p: (MyNat_wf m) /\ True): {VV: _ | leb_rel n m VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (leb_rel n m VV)) (leb (exist _ n n_p) (exist _ m m_p)) _); 
	rewrite <- leb__leb_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve leb_rel_mk : f_rel_funct_db.
#[global] Instance lebPack : (@Pack (MyNat ::RT (fun (n_r: MyNat) => (MyNat ::RT (fun (m_r: MyNat) => nilRT)))) (MyNat_u ::UT (MyNat_u ::UT nilUT)) (ltac: (mkProjectsArgListTG (MyNat ::RT (fun (n_r: MyNat) => (MyNat ::RT (fun (m_r: MyNat) => nilRT)))) (MyNat_u ::UT (MyNat_u ::UT nilUT)))) SFBool_u (fun (x_29372127: (ArgList MyNat ::RT (fun (n_r: MyNat) => (MyNat ::RT (fun (m_r: MyNat) => nilRT))))) => (fun (v_x_29372127: SFBool_u) => (ltac: (flattenP (fun (n_r: MyNat) => (fun (m_r: MyNat) => (fun (VV: SFBool_u) => ((SFBool_wf VV) /\ True)))) x_29372127 v_x_29372127))))).
Proof. 
	buildPackG leb leb_rel leb__leb_rel leb_rel_funct. 
Defined.
Definition ltb_spec (n: MyNat) (m: MyNat): Type := 
	SFBool. 
#[global] Hint Unfold ltb_spec : lia_unfold.
Definition ltb (n: MyNat) (m: MyNat): ltb_spec n m. 
Proof. 
	destruct n as [n n_p]. 
	destruct m as [m m_p]. 
	try revert m_p; generalize dependent m; 
	induction n as [(*O*)  | (*S*) n' IH_n']. 
	  - intros . 
		induction m as [(*O*)  | (*S*) m' IH_m']. 
		  -- intros . 
			refine (subsumptionCast _ _ SFFalse _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ SFTrue _); 
			solver.   
	  - intros . 
		induction m as [(*O*)  | (*S*) m' IH_m']. 
		  -- intros . 
			refine (subsumptionCast _ _ SFFalse _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ 
		(IH_n' (ltac: (try clear IH_n'; 
	solver)) m' (ltac: (try clear IH_n'; 
	solver))) _); 
			solver.   
Defined. 
Inductive ltb_rel : (MyNat_u -> (MyNat_u -> (SFBool_u -> Prop))) := 
	 | ltb_O_O: ltb_rel O_u O_u SFFalse_u
	 | ltb_O_S: (forall m' , ltb_rel O_u (S_u m') SFTrue_u)
	 | ltb_S_O: (forall n' , ltb_rel (S_u n') O_u SFFalse_u)
	 | ltb_S_S: (forall m' n' , forall (ltbres: SFBool_u), (ltb_rel n' m' ltbres) -> (ltb_rel (S_u n') (S_u m') ltbres)). 
#[global] Hint Constructors ltb_rel : core_hint_db.
#[global] Instance ltb_lookup_rel : dictionary rel ltb := { 
	lookup' := ltb_rel
}.
#[global] Instance ltb_getF : getFunc ltb_rel := { 
	getF' := ltb
}.
Theorem ltb_rel_funct [n: MyNat_u] [m: MyNat_u]: (forall (VV: SFBool_u) (VV': SFBool_u) (H: ltb_rel n m VV) (K: ltb_rel n m VV') , VV = VV'). 
Proof. 
	try revert m_p; generalize dependent m; 
	induction n as [(*O*)  | (*S*) n' IH_n']; 
	intros ; 
	[induction m as [(*O*)  | (*S*) m' IH_m']; 
	intros | 
	induction m as [(*O*)  | (*S*) m' IH_m']; 
	intros ]; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve ltb_rel_funct : f_rel_funct_db.
Theorem ltb_O_O_lem: (ltb_rel O_u O_u SFFalse_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite ltb_O_O_lem : f_rel_back.
Theorem ltb_O_S_lem (m': _): (ltb_rel O_u (S_u m') SFTrue_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite ltb_O_S_lem : f_rel_back.
Theorem ltb_S_O_lem (n': _): (ltb_rel (S_u n') O_u SFFalse_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite ltb_S_O_lem : f_rel_back.
Theorem ltb_S_S_lem (n': _) (m': _) (ltbres: SFBool_u) (h_85406348: ltb_rel n' m' ltbres): (ltb_rel (S_u n') (S_u m') ltbres) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite ltb_S_S_lem : f_rel_back.
Theorem ltb_rel_ex (n: MyNat_u) (m: MyNat_u) (n_p: (MyNat_wf n) /\ True) (m_p: (MyNat_wf m) /\ True): ltb_rel n m (⌊ ltb (exist _ n n_p) (exist _ m m_p) -⌋). 
Proof. 
	Opaque ltb.
	existence_lemma_pre ltb; 
	try revert m_p; generalize dependent m; 
	induction n as [(*O*)  | (*S*) n' IH_n']; 
	intros ; 
	[induction m as [(*O*)  | (*S*) m' IH_m']; 
	intros ; 
	[fix_notations| 
	fix_notations; 
	try clear IH_m']| 
	induction m as [(*O*)  | (*S*) m' IH_m']; 
	intros ; 
	[fix_notations; 
	try clear IH_n'| 
	fix_notations; 
	pose proof (IH_n' (ltac: (try clear IH_n'; 
	solver)) m' (ltac: (try clear IH_n'; 
	solver))) as IH_48190612; 
	try clear IH_n'; 
	try clear IH_m']]; 
	simpl in *. 
	Transparent ltb.
	all: existence_lemma_quicksolve ltb; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve ltb_rel_ex : rel_ax_db.
#[global] Opaque ltb. 
Theorem ltb__ltb_rel_rw (n: MyNat_u) (m: MyNat_u) (n_p: (MyNat_wf n) /\ True) (m_p: (MyNat_wf m) /\ True) (VV: SFBool_u): ((⌊ ltb (exist _ n n_p) (exist _ m m_p) -⌋) = VV) <-> (ltb_rel n m VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite ltb__ltb_rel_rw : f_rel_funct_db.
#[global] Hint Resolve ltb__ltb_rel_rw : rel_ax_db.
#[global] Instance ltb_lookup_rw : dictionary rwLem ltb := { 
	lookup' := ltb__ltb_rel_rw
}.
Theorem ltb__ltb_rel (n_r: MyNat) (m_r: MyNat) (VV: SFBool_u): ((⌊ ltb n_r m_r -⌋) = VV) <-> (ltb_rel (⌊ n_r -⌋) (⌊ m_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite ltb__ltb_rel : f_rel_funct_db.
Theorem ltb__ltb_rel' (n: MyNat_u) (m: MyNat_u) (n_r: MyNat) (m_r: MyNat) (VV: SFBool_u): (n = (⌊ n_r -⌋)) -> ((m = (⌊ m_r -⌋)) -> (((⌊ ltb n_r m_r -⌋) = VV) <-> (ltb_rel n m VV))). 
Proof. 
	intros -> ->. 
	refine (ltb__ltb_rel n_r m_r VV). 
Qed. 
#[global] Hint Resolve ltb__ltb_rel' : f_rel_funct_db.
Theorem ltb_rel_mk [n: MyNat_u] [m: MyNat_u] (n_p: (MyNat_wf n) /\ True) (m_p: (MyNat_wf m) /\ True): {VV: _ | ltb_rel n m VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (ltb_rel n m VV)) (ltb (exist _ n n_p) (exist _ m m_p)) _); 
	rewrite <- ltb__ltb_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve ltb_rel_mk : f_rel_funct_db.
#[global] Instance ltbPack : (@Pack (MyNat ::RT (fun (n_r: MyNat) => (MyNat ::RT (fun (m_r: MyNat) => nilRT)))) (MyNat_u ::UT (MyNat_u ::UT nilUT)) (ltac: (mkProjectsArgListTG (MyNat ::RT (fun (n_r: MyNat) => (MyNat ::RT (fun (m_r: MyNat) => nilRT)))) (MyNat_u ::UT (MyNat_u ::UT nilUT)))) SFBool_u (fun (x_29372127: (ArgList MyNat ::RT (fun (n_r: MyNat) => (MyNat ::RT (fun (m_r: MyNat) => nilRT))))) => (fun (v_x_29372127: SFBool_u) => (ltac: (flattenP (fun (n_r: MyNat) => (fun (m_r: MyNat) => (fun (VV: SFBool_u) => ((SFBool_wf VV) /\ True)))) x_29372127 v_x_29372127))))).
Proof. 
	buildPackG ltb ltb_rel ltb__ltb_rel ltb_rel_funct. 
Defined.
Definition minus_spec (n: MyNat) (m: MyNat): Type := 
	MyNat. 
#[global] Hint Unfold minus_spec : lia_unfold.
Definition minus (n: MyNat) (m: MyNat): minus_spec n m. 
Proof. 
	destruct n as [n n_p]. 
	destruct m as [m m_p]. 
	try revert m_p; generalize dependent m; 
	induction n as [(*O*)  | (*S*) ds_d5Tn IH_ds_d5Tn]. 
	  - intros . 
		refine (subsumptionCast _ _ O _); 
		solver.  
	  - intros . 
		induction m as [(*O*)  | (*S*) m' IH_m']. 
		  -- intros . 
			refine (subsumptionCast _ _ 
		(S 
		(exist (fun (VV: MyNat_u) => ((MyNat_wf VV) /\ True)) ds_d5Tn (ltac: (solver)))) _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ 
		(IH_ds_d5Tn (ltac: (try clear IH_ds_d5Tn; 
	solver)) m' (ltac: (try clear IH_ds_d5Tn; 
	solver))) _); 
			solver.   
Defined. 
Inductive minus_rel : (MyNat_u -> (MyNat_u -> (MyNat_u -> Prop))) := 
	 | minus_O: (forall m , minus_rel O_u m O_u)
	 | minus_S_O: (forall ds_d5Tn , minus_rel (S_u ds_d5Tn) O_u (S_u ds_d5Tn))
	 | minus_S_S: (forall ds_d5Tn m' , forall (minusres: MyNat_u), (minus_rel ds_d5Tn m' minusres) -> (minus_rel (S_u ds_d5Tn) (S_u m') minusres)). 
#[global] Hint Constructors minus_rel : core_hint_db.
#[global] Instance minus_lookup_rel : dictionary rel minus := { 
	lookup' := minus_rel
}.
#[global] Instance minus_getF : getFunc minus_rel := { 
	getF' := minus
}.
Theorem minus_rel_funct [n: MyNat_u] [m: MyNat_u]: (forall (VV: MyNat_u) (VV': MyNat_u) (H: minus_rel n m VV) (K: minus_rel n m VV') , VV = VV'). 
Proof. 
	try revert m_p; generalize dependent m; 
	induction n as [(*O*)  | (*S*) ds_d5Tn IH_ds_d5Tn]; 
	intros ; 
	[| 
	induction m as [(*O*)  | (*S*) m' IH_m']; 
	intros ]; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve minus_rel_funct : f_rel_funct_db.
Theorem minus_O_lem (m: _): (minus_rel O_u m O_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite minus_O_lem : f_rel_back.
Theorem minus_S_O_lem (ds_d5Tn: _): (minus_rel (S_u ds_d5Tn) O_u (S_u ds_d5Tn)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite minus_S_O_lem : f_rel_back.
Theorem minus_S_S_lem (ds_d5Tn: _) (m': _) (minusres: MyNat_u) (h_43612209: minus_rel ds_d5Tn m' minusres): (minus_rel (S_u ds_d5Tn) (S_u m') minusres) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite minus_S_S_lem : f_rel_back.
Theorem minus_rel_ex (n: MyNat_u) (m: MyNat_u) (n_p: (MyNat_wf n) /\ True) (m_p: (MyNat_wf m) /\ True): minus_rel n m (⌊ minus (exist _ n n_p) (exist _ m m_p) -⌋). 
Proof. 
	Opaque minus.
	existence_lemma_pre minus; 
	try revert m_p; generalize dependent m; 
	induction n as [(*O*)  | (*S*) ds_d5Tn IH_ds_d5Tn]; 
	intros ; 
	[fix_notations| 
	induction m as [(*O*)  | (*S*) m' IH_m']; 
	intros ; 
	[fix_notations; 
	try clear IH_ds_d5Tn| 
	fix_notations; 
	pose proof (IH_ds_d5Tn (ltac: (try clear IH_ds_d5Tn; 
	solver)) m' (ltac: (try clear IH_ds_d5Tn; 
	solver))) as IH_72709590; 
	try clear IH_ds_d5Tn; 
	try clear IH_m']]; 
	simpl in *. 
	Transparent minus.
	all: existence_lemma_quicksolve minus; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve minus_rel_ex : rel_ax_db.
#[global] Opaque minus. 
Theorem minus__minus_rel_rw (n: MyNat_u) (m: MyNat_u) (n_p: (MyNat_wf n) /\ True) (m_p: (MyNat_wf m) /\ True) (VV: MyNat_u): ((⌊ minus (exist _ n n_p) (exist _ m m_p) -⌋) = VV) <-> (minus_rel n m VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite minus__minus_rel_rw : f_rel_funct_db.
#[global] Hint Resolve minus__minus_rel_rw : rel_ax_db.
#[global] Instance minus_lookup_rw : dictionary rwLem minus := { 
	lookup' := minus__minus_rel_rw
}.
Theorem minus__minus_rel (n_r: MyNat) (m_r: MyNat) (VV: MyNat_u): ((⌊ minus n_r m_r -⌋) = VV) <-> (minus_rel (⌊ n_r -⌋) (⌊ m_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite minus__minus_rel : f_rel_funct_db.
Theorem minus__minus_rel' (n: MyNat_u) (m: MyNat_u) (n_r: MyNat) (m_r: MyNat) (VV: MyNat_u): (n = (⌊ n_r -⌋)) -> ((m = (⌊ m_r -⌋)) -> (((⌊ minus n_r m_r -⌋) = VV) <-> (minus_rel n m VV))). 
Proof. 
	intros -> ->. 
	refine (minus__minus_rel n_r m_r VV). 
Qed. 
#[global] Hint Resolve minus__minus_rel' : f_rel_funct_db.
Theorem minus_rel_mk [n: MyNat_u] [m: MyNat_u] (n_p: (MyNat_wf n) /\ True) (m_p: (MyNat_wf m) /\ True): {VV: _ | minus_rel n m VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (minus_rel n m VV)) (minus (exist _ n n_p) (exist _ m m_p)) _); 
	rewrite <- minus__minus_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve minus_rel_mk : f_rel_funct_db.
#[global] Instance minusPack : (@Pack (MyNat ::RT (fun (n_r: MyNat) => (MyNat ::RT (fun (m_r: MyNat) => nilRT)))) (MyNat_u ::UT (MyNat_u ::UT nilUT)) (ltac: (mkProjectsArgListTG (MyNat ::RT (fun (n_r: MyNat) => (MyNat ::RT (fun (m_r: MyNat) => nilRT)))) (MyNat_u ::UT (MyNat_u ::UT nilUT)))) MyNat_u (fun (x_29372127: (ArgList MyNat ::RT (fun (n_r: MyNat) => (MyNat ::RT (fun (m_r: MyNat) => nilRT))))) => (fun (v_x_29372127: MyNat_u) => (ltac: (flattenP (fun (n_r: MyNat) => (fun (m_r: MyNat) => (fun (VV: MyNat_u) => ((MyNat_wf VV) /\ True)))) x_29372127 v_x_29372127))))).
Proof. 
	buildPackG minus minus_rel minus__minus_rel minus_rel_funct. 
Defined.
Definition minus_n_n_spec (n: MyNat): Type := 
	{{forall (minusres: MyNat_u), (minus_rel (⌊ n -⌋) (⌊ n -⌋) minusres) -> (minusres = O_u)}}. 
#[global] Hint Unfold minus_n_n_spec : lia_unfold.
Theorem minus_n_n (n: MyNat): minus_n_n_spec n. 
Proof. 
	destruct n as [n n_p]. 
	induction n as [(*O*)  | (*S*) n' IH_n']. 
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ (IH_n' (ltac: (try clear IH_n'; 
	solver))) _); 
		solver.  
Qed. 
Definition minustwo_spec (lq_tmp0: MyNat): Type := 
	MyNat. 
#[global] Hint Unfold minustwo_spec : lia_unfold.
Definition minustwo (lq_tmp0: MyNat): minustwo_spec lq_tmp0. 
Proof. 
	destruct lq_tmp0 as [lq_tmp0 lq_tmp0_p]. 
	induction lq_tmp0 as [(*O*)  | (*S*) ds_d5TN IH_ds_d5TN]. 
	  - intros . 
		refine (subsumptionCast _ _ O _); 
		solver.  
	  - intros . 
		induction ds_d5TN as [(*O*)  | (*S*) n' IH_n']. 
		  -- intros . 
			refine (subsumptionCast _ _ O _); 
			solver.  
		  -- intros . 
			refine (exist _ n' _); 
			solver.   
Defined. 
Definition one_spec: Type := 
	MyNat. 
#[global] Hint Unfold one_spec : lia_unfold.
Definition one: one_spec. 
Proof. 
	refine (subsumptionCast _ _ 
		(S 
		(subsumptionCast MyNat_u (fun (VV: MyNat_u) => ((MyNat_wf VV) /\ True)) O (ltac: (solver)))) _); 
	solver. 
Defined. 
Inductive one_rel : (MyNat_u -> Prop) := 
	 | one_def: one_rel (S_u O_u). 
#[global] Hint Constructors one_rel : core_hint_db.
#[global] Instance one_lookup_rel : dictionary rel one := { 
	lookup' := one_rel
}.
#[global] Instance one_getF : getFunc one_rel := { 
	getF' := one
}.
Theorem one_rel_funct: (forall (VV: MyNat_u) (VV': MyNat_u) (H: one_rel VV) (K: one_rel VV') , VV = VV'). 
Proof. 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve one_rel_funct : f_rel_funct_db.
Theorem one_def_lem: (one_rel (S_u O_u)) <-> True. 
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
Theorem one__one_rel_rw (VV: MyNat_u): ((⌊ one -⌋) = VV) <-> (one_rel VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite one__one_rel_rw : f_rel_funct_db.
#[global] Hint Resolve one__one_rel_rw : rel_ax_db.
#[global] Instance one_lookup_rw : dictionary rwLem one := { 
	lookup' := one__one_rel_rw
}.
Theorem one__one_rel (VV: MyNat_u): ((⌊ one -⌋) = VV) <-> (one_rel VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite one__one_rel : f_rel_funct_db.
Theorem one__one_rel' (VV: MyNat_u): ((⌊ one -⌋) = VV) <-> (one_rel VV). 
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
Definition plus_spec (n: MyNat) (m: MyNat): Type := 
	MyNat. 
#[global] Hint Unfold plus_spec : lia_unfold.
Definition plus (n: MyNat) (m: MyNat): plus_spec n m. 
Proof. 
	destruct n as [n n_p]. 
	destruct m as [m m_p]. 
	try revert m_p; generalize dependent m; 
	induction n as [(*O*)  | (*S*) n' IH_n']. 
	  - intros . 
		refine (exist _ m _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ 
		(S 
		(IH_n' (ltac: (try clear IH_n'; 
	solver)) m (ltac: (try clear IH_n'; 
	solver)))) _); 
		solver.  
Defined. 
Inductive plus_rel : (MyNat_u -> (MyNat_u -> (MyNat_u -> Prop))) := 
	 | plus_O: (forall m , plus_rel O_u m m)
	 | plus_S: (forall m n' , forall (plusres: MyNat_u), (plus_rel n' m plusres) -> (plus_rel (S_u n') m (S_u plusres))). 
#[global] Hint Constructors plus_rel : core_hint_db.
#[global] Instance plus_lookup_rel : dictionary rel plus := { 
	lookup' := plus_rel
}.
#[global] Instance plus_getF : getFunc plus_rel := { 
	getF' := plus
}.
Theorem plus_rel_funct [n: MyNat_u] [m: MyNat_u]: (forall (VV: MyNat_u) (VV': MyNat_u) (H: plus_rel n m VV) (K: plus_rel n m VV') , VV = VV'). 
Proof. 
	try revert m_p; generalize dependent m; 
	induction n as [(*O*)  | (*S*) n' IH_n']; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve plus_rel_funct : f_rel_funct_db.
Theorem plus_O_lem (m: _): (plus_rel O_u m m) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite plus_O_lem : f_rel_back.
Theorem plus_S_lem (n': _) (m: _) (plusres: MyNat_u) (h_56226595: plus_rel n' m plusres): (plus_rel (S_u n') m (S_u plusres)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite plus_S_lem : f_rel_back.
Theorem plus_rel_ex (n: MyNat_u) (m: MyNat_u) (n_p: (MyNat_wf n) /\ True) (m_p: (MyNat_wf m) /\ True): plus_rel n m (⌊ plus (exist _ n n_p) (exist _ m m_p) -⌋). 
Proof. 
	Opaque plus.
	existence_lemma_pre plus; 
	try revert m_p; generalize dependent m; 
	induction n as [(*O*)  | (*S*) n' IH_n']; 
	intros ; 
	[fix_notations| 
	fix_notations; 
	pose proof (IH_n' (ltac: (try clear IH_n'; 
	solver)) m (ltac: (try clear IH_n'; 
	solver))) as IH_18143414; 
	try clear IH_n']; 
	simpl in *. 
	Transparent plus.
	all: existence_lemma_quicksolve plus; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve plus_rel_ex : rel_ax_db.
#[global] Opaque plus. 
Theorem plus__plus_rel_rw (n: MyNat_u) (m: MyNat_u) (n_p: (MyNat_wf n) /\ True) (m_p: (MyNat_wf m) /\ True) (VV: MyNat_u): ((⌊ plus (exist _ n n_p) (exist _ m m_p) -⌋) = VV) <-> (plus_rel n m VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite plus__plus_rel_rw : f_rel_funct_db.
#[global] Hint Resolve plus__plus_rel_rw : rel_ax_db.
#[global] Instance plus_lookup_rw : dictionary rwLem plus := { 
	lookup' := plus__plus_rel_rw
}.
Theorem plus__plus_rel (n_r: MyNat) (m_r: MyNat) (VV: MyNat_u): ((⌊ plus n_r m_r -⌋) = VV) <-> (plus_rel (⌊ n_r -⌋) (⌊ m_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite plus__plus_rel : f_rel_funct_db.
Theorem plus__plus_rel' (n: MyNat_u) (m: MyNat_u) (n_r: MyNat) (m_r: MyNat) (VV: MyNat_u): (n = (⌊ n_r -⌋)) -> ((m = (⌊ m_r -⌋)) -> (((⌊ plus n_r m_r -⌋) = VV) <-> (plus_rel n m VV))). 
Proof. 
	intros -> ->. 
	refine (plus__plus_rel n_r m_r VV). 
Qed. 
#[global] Hint Resolve plus__plus_rel' : f_rel_funct_db.
Theorem plus_rel_mk [n: MyNat_u] [m: MyNat_u] (n_p: (MyNat_wf n) /\ True) (m_p: (MyNat_wf m) /\ True): {VV: _ | plus_rel n m VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (plus_rel n m VV)) (plus (exist _ n n_p) (exist _ m m_p)) _); 
	rewrite <- plus__plus_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve plus_rel_mk : f_rel_funct_db.
#[global] Instance plusPack : (@Pack (MyNat ::RT (fun (n_r: MyNat) => (MyNat ::RT (fun (m_r: MyNat) => nilRT)))) (MyNat_u ::UT (MyNat_u ::UT nilUT)) (ltac: (mkProjectsArgListTG (MyNat ::RT (fun (n_r: MyNat) => (MyNat ::RT (fun (m_r: MyNat) => nilRT)))) (MyNat_u ::UT (MyNat_u ::UT nilUT)))) MyNat_u (fun (x_29372127: (ArgList MyNat ::RT (fun (n_r: MyNat) => (MyNat ::RT (fun (m_r: MyNat) => nilRT))))) => (fun (v_x_29372127: MyNat_u) => (ltac: (flattenP (fun (n_r: MyNat) => (fun (m_r: MyNat) => (fun (VV: MyNat_u) => ((MyNat_wf VV) /\ True)))) x_29372127 v_x_29372127))))).
Proof. 
	buildPackG plus plus_rel plus__plus_rel plus_rel_funct. 
Defined.
Definition add_0_r_spec (n: MyNat): Type := 
	{{forall (plusres: MyNat_u), (plus_rel (⌊ n -⌋) O_u plusres) -> (plusres = (⌊ n -⌋))}}. 
#[global] Hint Unfold add_0_r_spec : lia_unfold.
Theorem add_0_r (n: MyNat): add_0_r_spec n. 
Proof. 
	destruct n as [n n_p]. 
	induction n as [(*O*)  | (*S*) n' IH_n']. 
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ (IH_n' (ltac: (try clear IH_n'; 
	solver))) _); 
		solver.  
Qed. 
Definition add_assoc_spec (n: MyNat) (m: MyNat) (p: MyNat): Type := 
	{{forall (plusres: MyNat_u), (plus_rel (⌊ m -⌋) (⌊ p -⌋) plusres) -> (forall (plus_res_2: MyNat_u), (plus_rel (⌊ n -⌋) plusres plus_res_2) -> (forall (plus_res_3: MyNat_u), (plus_rel (⌊ n -⌋) (⌊ m -⌋) plus_res_3) -> (forall (plus_res_4: MyNat_u), (plus_rel plus_res_3 (⌊ p -⌋) plus_res_4) -> (plus_res_2 == plus_res_4))))}}. 
#[global] Hint Unfold add_assoc_spec : lia_unfold.
Theorem add_assoc (n: MyNat) (m: MyNat) (p: MyNat): add_assoc_spec n m p. 
Proof. 
	destruct n as [n n_p]. 
	destruct m as [m m_p]. 
	destruct p as [p p_p]. 
	try revert p_p; generalize dependent p; try revert m_p; generalize dependent m; 
	induction n as [(*O*)  | (*S*) n' IH_n']. 
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ 
		(IH_n' (ltac: (try clear IH_n'; 
	solver)) m (ltac: (try clear IH_n'; 
	solver)) p (ltac: (try clear IH_n'; 
	solver))) _); 
		solver.  
Qed. 
Definition add_succ_r_spec (n: MyNat) (m: MyNat): Type := 
	{{forall (plusres: MyNat_u), (plus_rel (⌊ n -⌋) (S_u (⌊ m -⌋)) plusres) -> (forall (plus_res_2: MyNat_u), (plus_rel (⌊ n -⌋) (⌊ m -⌋) plus_res_2) -> (plusres == (S_u plus_res_2)))}}. 
#[global] Hint Unfold add_succ_r_spec : lia_unfold.
Theorem add_succ_r (n: MyNat) (m: MyNat): add_succ_r_spec n m. 
Proof. 
	destruct n as [n n_p]. 
	destruct m as [m m_p]. 
	try revert m_p; generalize dependent m; 
	induction n as [(*O*)  | (*S*) n' IH_n']. 
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ 
		(IH_n' (ltac: (try clear IH_n'; 
	solver)) m (ltac: (try clear IH_n'; 
	solver))) _); 
		solver.  
Qed. 
Definition mult_spec (n: MyNat) (m: MyNat): Type := 
	MyNat. 
#[global] Hint Unfold mult_spec : lia_unfold.
Definition mult (n: MyNat) (m: MyNat): mult_spec n m. 
Proof. 
	destruct n as [n n_p]. 
	destruct m as [m m_p]. 
	try revert m_p; generalize dependent m; 
	induction n as [(*O*)  | (*S*) n' IH_n']. 
	  - intros . 
		refine (subsumptionCast _ _ O _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ 
		(plus 
		(exist (fun (n: MyNat_u) => ((MyNat_wf n) /\ True)) m (ltac: (solver))) 
		(subsumptionCast MyNat_u (fun (m: MyNat_u) => ((MyNat_wf m) /\ True)) 
		(IH_n' (ltac: (try clear IH_n'; 
	solver)) m (ltac: (try clear IH_n'; 
	solver))) (ltac: (solver)))) _); 
		solver.  
Defined. 
Inductive mult_rel : (MyNat_u -> (MyNat_u -> (MyNat_u -> Prop))) := 
	 | mult_O: (forall m , mult_rel O_u m O_u)
	 | mult_S: (forall m n' , forall (multres: MyNat_u), (mult_rel n' m multres) -> (forall (plusres: MyNat_u), (plus_rel m multres plusres) -> (mult_rel (S_u n') m plusres))). 
#[global] Hint Constructors mult_rel : core_hint_db.
#[global] Instance mult_lookup_rel : dictionary rel mult := { 
	lookup' := mult_rel
}.
#[global] Instance mult_getF : getFunc mult_rel := { 
	getF' := mult
}.
Theorem mult_rel_funct [n: MyNat_u] [m: MyNat_u]: (forall (VV: MyNat_u) (VV': MyNat_u) (H: mult_rel n m VV) (K: mult_rel n m VV') , VV = VV'). 
Proof. 
	try revert m_p; generalize dependent m; 
	induction n as [(*O*)  | (*S*) n' IH_n']; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve mult_rel_funct : f_rel_funct_db.
Theorem mult_O_lem (m: _): (mult_rel O_u m O_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite mult_O_lem : f_rel_back.
Theorem mult_S_lem (n': _) (m: _) (plusres: MyNat_u): (mult_rel (S_u n') m plusres) <-> (exists (multres: MyNat_u), (mult_rel n' m multres) /\ (plus_rel m multres plusres)). 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite mult_S_lem : f_rel_back.
Theorem mult_rel_ex (n: MyNat_u) (m: MyNat_u) (n_p: (MyNat_wf n) /\ True) (m_p: (MyNat_wf m) /\ True): mult_rel n m (⌊ mult (exist _ n n_p) (exist _ m m_p) -⌋). 
Proof. 
	Opaque mult.
	existence_lemma_pre mult; 
	try revert m_p; generalize dependent m; 
	induction n as [(*O*)  | (*S*) n' IH_n']; 
	intros ; 
	[fix_notations| 
	fix_notations; 
	pose proof (IH_n' (ltac: (try clear IH_n'; 
	solver)) m (ltac: (try clear IH_n'; 
	solver))) as IH_18143414; 
	try clear IH_n']; 
	simpl in *. 
	Transparent mult.
	all: existence_lemma_quicksolve mult; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve mult_rel_ex : rel_ax_db.
#[global] Opaque mult. 
Theorem mult__mult_rel_rw (n: MyNat_u) (m: MyNat_u) (n_p: (MyNat_wf n) /\ True) (m_p: (MyNat_wf m) /\ True) (VV: MyNat_u): ((⌊ mult (exist _ n n_p) (exist _ m m_p) -⌋) = VV) <-> (mult_rel n m VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite mult__mult_rel_rw : f_rel_funct_db.
#[global] Hint Resolve mult__mult_rel_rw : rel_ax_db.
#[global] Instance mult_lookup_rw : dictionary rwLem mult := { 
	lookup' := mult__mult_rel_rw
}.
Theorem mult__mult_rel (n_r: MyNat) (m_r: MyNat) (VV: MyNat_u): ((⌊ mult n_r m_r -⌋) = VV) <-> (mult_rel (⌊ n_r -⌋) (⌊ m_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite mult__mult_rel : f_rel_funct_db.
Theorem mult__mult_rel' (n: MyNat_u) (m: MyNat_u) (n_r: MyNat) (m_r: MyNat) (VV: MyNat_u): (n = (⌊ n_r -⌋)) -> ((m = (⌊ m_r -⌋)) -> (((⌊ mult n_r m_r -⌋) = VV) <-> (mult_rel n m VV))). 
Proof. 
	intros -> ->. 
	refine (mult__mult_rel n_r m_r VV). 
Qed. 
#[global] Hint Resolve mult__mult_rel' : f_rel_funct_db.
Theorem mult_rel_mk [n: MyNat_u] [m: MyNat_u] (n_p: (MyNat_wf n) /\ True) (m_p: (MyNat_wf m) /\ True): {VV: _ | mult_rel n m VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (mult_rel n m VV)) (mult (exist _ n n_p) (exist _ m m_p)) _); 
	rewrite <- mult__mult_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve mult_rel_mk : f_rel_funct_db.
#[global] Instance multPack : (@Pack (MyNat ::RT (fun (n_r: MyNat) => (MyNat ::RT (fun (m_r: MyNat) => nilRT)))) (MyNat_u ::UT (MyNat_u ::UT nilUT)) (ltac: (mkProjectsArgListTG (MyNat ::RT (fun (n_r: MyNat) => (MyNat ::RT (fun (m_r: MyNat) => nilRT)))) (MyNat_u ::UT (MyNat_u ::UT nilUT)))) MyNat_u (fun (x_29372127: (ArgList MyNat ::RT (fun (n_r: MyNat) => (MyNat ::RT (fun (m_r: MyNat) => nilRT))))) => (fun (v_x_29372127: MyNat_u) => (ltac: (flattenP (fun (n_r: MyNat) => (fun (m_r: MyNat) => (fun (VV: MyNat_u) => ((MyNat_wf VV) /\ True)))) x_29372127 v_x_29372127))))).
Proof. 
	buildPackG mult mult_rel mult__mult_rel mult_rel_funct. 
Defined.
Definition factorial_spec (lq_tmp0: MyNat): Type := 
	MyNat. 
#[global] Hint Unfold factorial_spec : lia_unfold.
Definition factorial (lq_tmp0: MyNat): factorial_spec lq_tmp0. 
Proof. 
	destruct lq_tmp0 as [lq_tmp0 lq_tmp0_p]. 
	induction lq_tmp0 as [(*O*)  | (*S*) n' IH_n']. 
	  - intros . 
		refine (subsumptionCast _ _ 
		(S 
		(subsumptionCast MyNat_u (fun (VV: MyNat_u) => ((MyNat_wf VV) /\ True)) O (ltac: (solver)))) _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ 
		(mult 
		(subsumptionCast MyNat_u (fun (n: MyNat_u) => ((MyNat_wf n) /\ True)) 
		(S 
		(exist (fun (VV: MyNat_u) => ((MyNat_wf VV) /\ True)) n' (ltac: (solver)))) (ltac: (solver))) 
		(subsumptionCast MyNat_u (fun (m: MyNat_u) => ((MyNat_wf m) /\ True)) (IH_n' (ltac: (try clear IH_n'; 
	solver))) (ltac: (solver)))) _); 
		solver.  
Defined. 
Inductive factorial_rel : (MyNat_u -> (MyNat_u -> Prop)) := 
	 | factorial_O: factorial_rel O_u (S_u O_u)
	 | factorial_S: (forall n' , forall (factorialres: MyNat_u), (factorial_rel n' factorialres) -> (forall (multres: MyNat_u), (mult_rel (S_u n') factorialres multres) -> (factorial_rel (S_u n') multres))). 
#[global] Hint Constructors factorial_rel : core_hint_db.
#[global] Instance factorial_lookup_rel : dictionary rel factorial := { 
	lookup' := factorial_rel
}.
#[global] Instance factorial_getF : getFunc factorial_rel := { 
	getF' := factorial
}.
Theorem factorial_rel_funct [lq_tmp0: MyNat_u]: (forall (VV: MyNat_u) (VV': MyNat_u) (H: factorial_rel lq_tmp0 VV) (K: factorial_rel lq_tmp0 VV') , VV = VV'). 
Proof. 
	induction lq_tmp0 as [(*O*)  | (*S*) n' IH_n']; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve factorial_rel_funct : f_rel_funct_db.
Theorem factorial_O_lem: (factorial_rel O_u (S_u O_u)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite factorial_O_lem : f_rel_back.
Theorem factorial_S_lem (n': _) (multres: MyNat_u): (factorial_rel (S_u n') multres) <-> (exists (factorialres: MyNat_u), (factorial_rel n' factorialres) /\ (mult_rel (S_u n') factorialres multres)). 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite factorial_S_lem : f_rel_back.
Theorem factorial_rel_ex (lq_tmp0: MyNat_u) (lq_tmp0_p: (MyNat_wf lq_tmp0) /\ True): factorial_rel lq_tmp0 (⌊ factorial (exist _ lq_tmp0 lq_tmp0_p) -⌋). 
Proof. 
	Opaque factorial.
	existence_lemma_pre factorial; 
	induction lq_tmp0 as [(*O*)  | (*S*) n' IH_n']; 
	intros ; 
	[fix_notations| 
	fix_notations; 
	pose proof (IH_n' (ltac: (try clear IH_n'; 
	solver))) as IH_87935079; 
	try clear IH_n']; 
	simpl in *. 
	Transparent factorial.
	all: existence_lemma_quicksolve factorial; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve factorial_rel_ex : rel_ax_db.
#[global] Opaque factorial. 
Theorem factorial__factorial_rel_rw (lq_tmp0: MyNat_u) (lq_tmp0_p: (MyNat_wf lq_tmp0) /\ True) (VV: MyNat_u): ((⌊ factorial (exist _ lq_tmp0 lq_tmp0_p) -⌋) = VV) <-> (factorial_rel lq_tmp0 VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite factorial__factorial_rel_rw : f_rel_funct_db.
#[global] Hint Resolve factorial__factorial_rel_rw : rel_ax_db.
#[global] Instance factorial_lookup_rw : dictionary rwLem factorial := { 
	lookup' := factorial__factorial_rel_rw
}.
Theorem factorial__factorial_rel (lq_tmp0_r: MyNat) (VV: MyNat_u): ((⌊ factorial lq_tmp0_r -⌋) = VV) <-> (factorial_rel (⌊ lq_tmp0_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite factorial__factorial_rel : f_rel_funct_db.
Theorem factorial__factorial_rel' (lq_tmp0: MyNat_u) (lq_tmp0_r: MyNat) (VV: MyNat_u): (lq_tmp0 = (⌊ lq_tmp0_r -⌋)) -> (((⌊ factorial lq_tmp0_r -⌋) = VV) <-> (factorial_rel lq_tmp0 VV)). 
Proof. 
	intros ->. 
	refine (factorial__factorial_rel lq_tmp0_r VV). 
Qed. 
#[global] Hint Resolve factorial__factorial_rel' : f_rel_funct_db.
Theorem factorial_rel_mk [lq_tmp0: MyNat_u] (lq_tmp0_p: (MyNat_wf lq_tmp0) /\ True): {VV: _ | factorial_rel lq_tmp0 VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (factorial_rel lq_tmp0 VV)) (factorial (exist _ lq_tmp0 lq_tmp0_p)) _); 
	rewrite <- factorial__factorial_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve factorial_rel_mk : f_rel_funct_db.
#[global] Instance factorialPack : (@Pack (MyNat ::RT (fun (lq_tmp0_r: MyNat) => nilRT)) (MyNat_u ::UT nilUT) (ltac: (mkProjectsArgListTG (MyNat ::RT (fun (lq_tmp0_r: MyNat) => nilRT)) (MyNat_u ::UT nilUT))) MyNat_u (fun (x_87229013: (ArgList MyNat ::RT (fun (lq_tmp0_r: MyNat) => nilRT))) => (fun (v_x_87229013: MyNat_u) => (ltac: (flattenP (fun (lq_tmp0_r: MyNat) => (fun (VV: MyNat_u) => ((MyNat_wf VV) /\ True))) x_87229013 v_x_87229013))))).
Proof. 
	buildPackG factorial factorial_rel factorial__factorial_rel factorial_rel_funct. 
Defined.
Definition mul_0_r_spec (n: MyNat): Type := 
	{{forall (multres: MyNat_u), (mult_rel (⌊ n -⌋) O_u multres) -> (multres = O_u)}}. 
#[global] Hint Unfold mul_0_r_spec : lia_unfold.
Theorem mul_0_r (n: MyNat): mul_0_r_spec n. 
Proof. 
	destruct n as [n n_p]. 
	induction n as [(*O*)  | (*S*) n' IH_n']. 
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ (IH_n' (ltac: (try clear IH_n'; 
	solver))) _); 
		solver.  
Qed. 
Definition mult_0_1_spec (n: MyNat): Type := 
	{{forall (multres: MyNat_u), (mult_rel O_u (⌊ n -⌋) multres) -> (multres = O_u)}}. 
#[global] Hint Unfold mult_0_1_spec : lia_unfold.
Theorem mult_0_1 (n: MyNat): mult_0_1_spec n. 
Proof. 
	destruct n as [n n_p]. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition mult_n_O_spec (n: MyNat): Type := 
	{{forall (multres: MyNat_u), (mult_rel (⌊ n -⌋) O_u multres) -> (O_u = multres)}}. 
#[global] Hint Unfold mult_n_O_spec : lia_unfold.
Theorem mult_n_O (n: MyNat): mult_n_O_spec n. 
Proof. 
	destruct n as [n n_p]. 
	induction n as [(*O*)  | (*S*) n' IH_n']. 
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ (IH_n' (ltac: (try clear IH_n'; 
	solver))) _); 
		solver.  
Qed. 
Definition mult_n_0_m_0_spec (p: MyNat) (q: MyNat): Type := 
	{{forall (multres: MyNat_u), (mult_rel (⌊ q -⌋) O_u multres) -> (forall (mult_res_2: MyNat_u), (mult_rel (⌊ p -⌋) O_u mult_res_2) -> (forall (plusres: MyNat_u), (plus_rel mult_res_2 multres plusres) -> (plusres = O_u)))}}. 
#[global] Hint Unfold mult_n_0_m_0_spec : lia_unfold.
Theorem mult_n_0_m_0 (p: MyNat) (q: MyNat): mult_n_0_m_0_spec p q. 
Proof. 
	destruct p as [p p_p]. 
	destruct q as [q q_p]. 
	pose proof (mult_n_O 
		(exist (fun (n: MyNat_u) => ((MyNat_wf n) /\ True)) q (ltac: (solver)))) as H_34880653. 
	simpl in H_34880653. 
	refine (subsumptionCast _ _ 
		(mult_n_O 
		(exist (fun (n: MyNat_u) => ((MyNat_wf n) /\ True)) p (ltac: (solver)))) _); 
	solver. 
Qed. 
Definition mult_n_Sm_spec (n: MyNat) (m: MyNat): Type := 
	{{forall (multres: MyNat_u), (mult_rel (⌊ n -⌋) (⌊ m -⌋) multres) -> (forall (plusres: MyNat_u), (plus_rel multres (⌊ n -⌋) plusres) -> (forall (mult_res_2: MyNat_u), (mult_rel (⌊ n -⌋) (S_u (⌊ m -⌋)) mult_res_2) -> (plusres == mult_res_2)))}}. 
#[global] Hint Unfold mult_n_Sm_spec : lia_unfold.
Theorem mult_n_Sm (n: MyNat) (m: MyNat): mult_n_Sm_spec n m. 
Proof. 
	destruct n as [n n_p]. 
	destruct m as [m m_p]. 
	try revert m_p; generalize dependent m; 
	induction n as [(*O*)  | (*S*) n' IH_n']. 
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		pose proof (add_assoc 
		(exist (fun (n: MyNat_u) => ((MyNat_wf n) /\ True)) m (ltac: (solver))) 
		(subsumptionCast MyNat_u (fun (m: MyNat_u) => ((MyNat_wf m) /\ True)) 
		(mult 
		(exist (fun (n: MyNat_u) => ((MyNat_wf n) /\ True)) n' (ltac: (solver))) 
		(exist (fun (m: MyNat_u) => ((MyNat_wf m) /\ True)) m (ltac: (solver)))) (ltac: (solver))) 
		(exist (fun (p: MyNat_u) => ((MyNat_wf p) /\ True)) n' (ltac: (solver)))) as H_28156190. 
		simpl in H_28156190. 
		pose proof (add_succ_r 
		(subsumptionCast MyNat_u (fun (n: MyNat_u) => ((MyNat_wf n) /\ True)) 
		(plus 
		(exist (fun (n: MyNat_u) => ((MyNat_wf n) /\ True)) m (ltac: (solver))) 
		(subsumptionCast MyNat_u (fun (m: MyNat_u) => ((MyNat_wf m) /\ True)) 
		(mult 
		(exist (fun (n: MyNat_u) => ((MyNat_wf n) /\ True)) n' (ltac: (solver))) 
		(exist (fun (m: MyNat_u) => ((MyNat_wf m) /\ True)) m (ltac: (solver)))) (ltac: (solver)))) (ltac: (solver))) 
		(exist (fun (m: MyNat_u) => ((MyNat_wf m) /\ True)) n' (ltac: (solver)))) as H_66800893. 
		simpl in H_66800893. 
		refine (subsumptionCast _ _ 
		(IH_n' (ltac: (try clear IH_n'; 
	solver)) m (ltac: (try clear IH_n'; 
	solver))) _); 
		solver.  
Qed. 
Definition mult_n_1_spec (p: MyNat): Type := 
	{{forall (multres: MyNat_u), (mult_rel (⌊ p -⌋) (⌊ one -⌋) multres) -> (multres = (⌊ p -⌋))}}. 
#[global] Hint Unfold mult_n_1_spec : lia_unfold.
Theorem mult_n_1 (p: MyNat): mult_n_1_spec p. 
Proof. 
	destruct p as [p p_p]. 
	pose proof (mult_n_O 
		(exist (fun (n: MyNat_u) => ((MyNat_wf n) /\ True)) p (ltac: (solver)))) as H_10188893. 
	simpl in H_10188893. 
	refine (subsumptionCast _ _ 
		(mult_n_Sm 
		(exist (fun (n: MyNat_u) => ((MyNat_wf n) /\ True)) p (ltac: (solver))) 
		(subsumptionCast MyNat_u (fun (m: MyNat_u) => ((MyNat_wf m) /\ True)) O (ltac: (solver)))) _); 
	solver. 
Qed. 
Definition plus_1_1_spec (n: MyNat): Type := 
	{{forall (plusres: MyNat_u), (plus_rel (⌊ one -⌋) (⌊ n -⌋) plusres) -> (plusres == (S_u (⌊ n -⌋)))}}. 
#[global] Hint Unfold plus_1_1_spec : lia_unfold.
Theorem plus_1_1 (n: MyNat): plus_1_1_spec n. 
Proof. 
	destruct n as [n n_p]. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition plus_1_neq_0_spec (n: MyNat): Type := 
	{{forall (plusres: MyNat_u), (plus_rel (⌊ n -⌋) (⌊ one -⌋) plusres) -> (plusres <> O_u)}}. 
#[global] Hint Unfold plus_1_neq_0_spec : lia_unfold.
Theorem plus_1_neq_0 (n: MyNat): plus_1_neq_0_spec n. 
Proof. 
	destruct n as [n n_p]. 
	induction n as [(*O*)  | (*S*) ds_d5T8 IH_ds_d5T8]. 
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
Qed. 
Definition plus_O_n_spec (n: MyNat): Type := 
	{{forall (plusres: MyNat_u), (plus_rel O_u (⌊ n -⌋) plusres) -> (plusres = (⌊ n -⌋))}}. 
#[global] Hint Unfold plus_O_n_spec : lia_unfold.
Theorem plus_O_n (n: MyNat): plus_O_n_spec n. 
Proof. 
	destruct n as [n n_p]. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition plus_id_example_spec (n: MyNat) (m: MyNat) (z: {{(⌊ n -⌋) = (⌊ m -⌋)}}): Type := 
	{{forall (plusres: MyNat_u), (plus_rel (⌊ n -⌋) (⌊ n -⌋) plusres) -> (forall (plus_res_2: MyNat_u), (plus_rel (⌊ m -⌋) (⌊ m -⌋) plus_res_2) -> (plusres == plus_res_2))}}. 
#[global] Hint Unfold plus_id_example_spec : lia_unfold.
Theorem plus_id_example (n: MyNat) (m: MyNat) (z: {{(⌊ n -⌋) = (⌊ m -⌋)}}): plus_id_example_spec n m z. 
Proof. 
	destruct n as [n n_p]. 
	destruct m as [m m_p]. 
	destruct z as [z z_p]. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition plus_id_exercise_spec (n: MyNat) (m: MyNat) (o: MyNat) (p: {{(⌊ n -⌋) = (⌊ m -⌋)}}) (q: {{(⌊ m -⌋) = (⌊ o -⌋)}}): Type := 
	{{forall (plusres: MyNat_u), (plus_rel (⌊ n -⌋) (⌊ m -⌋) plusres) -> (forall (plus_res_2: MyNat_u), (plus_rel (⌊ m -⌋) (⌊ o -⌋) plus_res_2) -> (plusres == plus_res_2))}}. 
#[global] Hint Unfold plus_id_exercise_spec : lia_unfold.
Theorem plus_id_exercise (n: MyNat) (m: MyNat) (o: MyNat) (p: {{(⌊ n -⌋) = (⌊ m -⌋)}}) (q: {{(⌊ m -⌋) = (⌊ o -⌋)}}): plus_id_exercise_spec n m o p q. 
Proof. 
	destruct n as [n n_p]. 
	destruct m as [m m_p]. 
	destruct o as [o o_p]. 
	destruct p as [p p_p]. 
	destruct q as [q q_p]. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition plus_n_Sm_spec (n: MyNat) (m: MyNat): Type := 
	{{forall (plusres: MyNat_u), (plus_rel (⌊ n -⌋) (⌊ m -⌋) plusres) -> (forall (plus_res_2: MyNat_u), (plus_rel (⌊ n -⌋) (S_u (⌊ m -⌋)) plus_res_2) -> ((S_u plusres) == plus_res_2))}}. 
#[global] Hint Unfold plus_n_Sm_spec : lia_unfold.
Theorem plus_n_Sm (n: MyNat) (m: MyNat): plus_n_Sm_spec n m. 
Proof. 
	destruct n as [n n_p]. 
	destruct m as [m m_p]. 
	try revert m_p; generalize dependent m; 
	induction n as [(*O*)  | (*S*) n' IH_n']. 
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ 
		(IH_n' (ltac: (try clear IH_n'; 
	solver)) m (ltac: (try clear IH_n'; 
	solver))) _); 
		solver.  
Qed. 
Definition add_comm_spec (n: MyNat) (m: MyNat): Type := 
	{{forall (plusres: MyNat_u), (plus_rel (⌊ n -⌋) (⌊ m -⌋) plusres) -> (forall (plus_res_2: MyNat_u), (plus_rel (⌊ m -⌋) (⌊ n -⌋) plus_res_2) -> (plusres == plus_res_2))}}. 
#[global] Hint Unfold add_comm_spec : lia_unfold.
Theorem add_comm (n: MyNat) (m: MyNat): add_comm_spec n m. 
Proof. 
	destruct n as [n n_p]. 
	destruct m as [m m_p]. 
	try revert m_p; generalize dependent m; 
	induction n as [(*O*)  | (*S*) n' IH_n']. 
	  - intros . 
		refine (subsumptionCast _ _ 
		(add_0_r 
		(exist (fun (n: MyNat_u) => ((MyNat_wf n) /\ True)) m (ltac: (solver)))) _); 
		solver.  
	  - intros . 
		pose proof (IH_n' (ltac: (try clear IH_n'; 
	solver)) m (ltac: (try clear IH_n'; 
	solver))) as H_75441852. 
		simpl in H_75441852. 
		refine (subsumptionCast _ _ 
		(plus_n_Sm 
		(exist (fun (n: MyNat_u) => ((MyNat_wf n) /\ True)) m (ltac: (solver))) 
		(exist (fun (m: MyNat_u) => ((MyNat_wf m) /\ True)) n' (ltac: (solver)))) _); 
		solver.  
Qed. 
Definition pred_spec (lq_tmp0: MyNat): Type := 
	MyNat. 
#[global] Hint Unfold pred_spec : lia_unfold.
Definition pred (lq_tmp0: MyNat): pred_spec lq_tmp0. 
Proof. 
	destruct lq_tmp0 as [lq_tmp0 lq_tmp0_p]. 
	induction lq_tmp0 as [(*O*)  | (*S*) n' IH_n']. 
	  - intros . 
		refine (subsumptionCast _ _ O _); 
		solver.  
	  - intros . 
		refine (exist _ n' _); 
		solver.  
Defined. 
Inductive pred_rel : (MyNat_u -> (MyNat_u -> Prop)) := 
	 | pred_O: pred_rel O_u O_u
	 | pred_S: (forall n' , pred_rel (S_u n') n'). 
#[global] Hint Constructors pred_rel : core_hint_db.
#[global] Instance pred_lookup_rel : dictionary rel pred := { 
	lookup' := pred_rel
}.
#[global] Instance pred_getF : getFunc pred_rel := { 
	getF' := pred
}.
Theorem pred_rel_funct [lq_tmp0: MyNat_u]: (forall (VV: MyNat_u) (VV': MyNat_u) (H: pred_rel lq_tmp0 VV) (K: pred_rel lq_tmp0 VV') , VV = VV'). 
Proof. 
	induction lq_tmp0 as [(*O*)  | (*S*) n' IH_n']; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve pred_rel_funct : f_rel_funct_db.
Theorem pred_O_lem: (pred_rel O_u O_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite pred_O_lem : f_rel_back.
Theorem pred_S_lem (n': _): (pred_rel (S_u n') n') <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite pred_S_lem : f_rel_back.
Theorem pred_rel_ex (lq_tmp0: MyNat_u) (lq_tmp0_p: (MyNat_wf lq_tmp0) /\ True): pred_rel lq_tmp0 (⌊ pred (exist _ lq_tmp0 lq_tmp0_p) -⌋). 
Proof. 
	Opaque pred.
	existence_lemma_pre pred; 
	induction lq_tmp0 as [(*O*)  | (*S*) n' IH_n']; 
	intros ; 
	[fix_notations| 
	fix_notations; 
	try clear IH_n']; 
	simpl in *. 
	Transparent pred.
	all: existence_lemma_quicksolve pred; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve pred_rel_ex : rel_ax_db.
#[global] Opaque pred. 
Theorem pred__pred_rel_rw (lq_tmp0: MyNat_u) (lq_tmp0_p: (MyNat_wf lq_tmp0) /\ True) (VV: MyNat_u): ((⌊ pred (exist _ lq_tmp0 lq_tmp0_p) -⌋) = VV) <-> (pred_rel lq_tmp0 VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite pred__pred_rel_rw : f_rel_funct_db.
#[global] Hint Resolve pred__pred_rel_rw : rel_ax_db.
#[global] Instance pred_lookup_rw : dictionary rwLem pred := { 
	lookup' := pred__pred_rel_rw
}.
Theorem pred__pred_rel (lq_tmp0_r: MyNat) (VV: MyNat_u): ((⌊ pred lq_tmp0_r -⌋) = VV) <-> (pred_rel (⌊ lq_tmp0_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite pred__pred_rel : f_rel_funct_db.
Theorem pred__pred_rel' (lq_tmp0: MyNat_u) (lq_tmp0_r: MyNat) (VV: MyNat_u): (lq_tmp0 = (⌊ lq_tmp0_r -⌋)) -> (((⌊ pred lq_tmp0_r -⌋) = VV) <-> (pred_rel lq_tmp0 VV)). 
Proof. 
	intros ->. 
	refine (pred__pred_rel lq_tmp0_r VV). 
Qed. 
#[global] Hint Resolve pred__pred_rel' : f_rel_funct_db.
Theorem pred_rel_mk [lq_tmp0: MyNat_u] (lq_tmp0_p: (MyNat_wf lq_tmp0) /\ True): {VV: _ | pred_rel lq_tmp0 VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (pred_rel lq_tmp0 VV)) (pred (exist _ lq_tmp0 lq_tmp0_p)) _); 
	rewrite <- pred__pred_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve pred_rel_mk : f_rel_funct_db.
#[global] Instance predPack : (@Pack (MyNat ::RT (fun (lq_tmp0_r: MyNat) => nilRT)) (MyNat_u ::UT nilUT) (ltac: (mkProjectsArgListTG (MyNat ::RT (fun (lq_tmp0_r: MyNat) => nilRT)) (MyNat_u ::UT nilUT))) MyNat_u (fun (x_87229013: (ArgList MyNat ::RT (fun (lq_tmp0_r: MyNat) => nilRT))) => (fun (v_x_87229013: MyNat_u) => (ltac: (flattenP (fun (lq_tmp0_r: MyNat) => (fun (VV: MyNat_u) => ((MyNat_wf VV) /\ True))) x_87229013 v_x_87229013))))).
Proof. 
	buildPackG pred pred_rel pred__pred_rel pred_rel_funct. 
Defined.
Definition sf_exp_spec (base: MyNat) (power: MyNat): Type := 
	MyNat. 
#[global] Hint Unfold sf_exp_spec : lia_unfold.
Definition sf_exp (base: MyNat) (power: MyNat): sf_exp_spec base power. 
Proof. 
	destruct base as [base base_p]. 
	destruct power as [power power_p]. 
	try revert base_p; generalize dependent base; 
	induction power as [(*O*)  | (*S*) p IH_p]. 
	  - intros . 
		refine (subsumptionCast _ _ 
		(S 
		(subsumptionCast MyNat_u (fun (VV: MyNat_u) => ((MyNat_wf VV) /\ True)) O (ltac: (solver)))) _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ 
		(mult 
		(exist (fun (n: MyNat_u) => ((MyNat_wf n) /\ True)) base (ltac: (solver))) 
		(subsumptionCast MyNat_u (fun (m: MyNat_u) => ((MyNat_wf m) /\ True)) 
		(IH_p (ltac: (try clear IH_p; 
	solver)) base (ltac: (try clear IH_p; 
	solver))) (ltac: (solver)))) _); 
		solver.  
Defined. 
Inductive sf_exp_rel : (MyNat_u -> (MyNat_u -> (MyNat_u -> Prop))) := 
	 | sf_exp_O: (forall base , sf_exp_rel base O_u (S_u O_u))
	 | sf_exp_S: (forall base p , forall (sf_expres: MyNat_u), (sf_exp_rel base p sf_expres) -> (forall (multres: MyNat_u), (mult_rel base sf_expres multres) -> (sf_exp_rel base (S_u p) multres))). 
#[global] Hint Constructors sf_exp_rel : core_hint_db.
#[global] Instance sf_exp_lookup_rel : dictionary rel sf_exp := { 
	lookup' := sf_exp_rel
}.
#[global] Instance sf_exp_getF : getFunc sf_exp_rel := { 
	getF' := sf_exp
}.
Theorem sf_exp_rel_funct [base: MyNat_u] [power: MyNat_u]: (forall (VV: MyNat_u) (VV': MyNat_u) (H: sf_exp_rel base power VV) (K: sf_exp_rel base power VV') , VV = VV'). 
Proof. 
	try revert base_p; generalize dependent base; 
	induction power as [(*O*)  | (*S*) p IH_p]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve sf_exp_rel_funct : f_rel_funct_db.
Theorem sf_exp_O_lem (base: _): (sf_exp_rel base O_u (S_u O_u)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite sf_exp_O_lem : f_rel_back.
Theorem sf_exp_S_lem (base: _) (p: _) (multres: MyNat_u): (sf_exp_rel base (S_u p) multres) <-> (exists (sf_expres: MyNat_u), (sf_exp_rel base p sf_expres) /\ (mult_rel base sf_expres multres)). 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite sf_exp_S_lem : f_rel_back.
Theorem sf_exp_rel_ex (base: MyNat_u) (power: MyNat_u) (base_p: (MyNat_wf base) /\ True) (power_p: (MyNat_wf power) /\ True): sf_exp_rel base power (⌊ sf_exp (exist _ base base_p) (exist _ power power_p) -⌋). 
Proof. 
	Opaque sf_exp.
	existence_lemma_pre sf_exp; 
	try revert base_p; generalize dependent base; 
	induction power as [(*O*)  | (*S*) p IH_p]; 
	intros ; 
	[fix_notations| 
	fix_notations; 
	pose proof (IH_p (ltac: (try clear IH_p; 
	solver)) base (ltac: (try clear IH_p; 
	solver))) as IH_37549769; 
	try clear IH_p]; 
	simpl in *. 
	Transparent sf_exp.
	all: existence_lemma_quicksolve sf_exp; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve sf_exp_rel_ex : rel_ax_db.
#[global] Opaque sf_exp. 
Theorem sf_exp__sf_exp_rel_rw (base: MyNat_u) (power: MyNat_u) (base_p: (MyNat_wf base) /\ True) (power_p: (MyNat_wf power) /\ True) (VV: MyNat_u): ((⌊ sf_exp (exist _ base base_p) (exist _ power power_p) -⌋) = VV) <-> (sf_exp_rel base power VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite sf_exp__sf_exp_rel_rw : f_rel_funct_db.
#[global] Hint Resolve sf_exp__sf_exp_rel_rw : rel_ax_db.
#[global] Instance sf_exp_lookup_rw : dictionary rwLem sf_exp := { 
	lookup' := sf_exp__sf_exp_rel_rw
}.
Theorem sf_exp__sf_exp_rel (base_r: MyNat) (power_r: MyNat) (VV: MyNat_u): ((⌊ sf_exp base_r power_r -⌋) = VV) <-> (sf_exp_rel (⌊ base_r -⌋) (⌊ power_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite sf_exp__sf_exp_rel : f_rel_funct_db.
Theorem sf_exp__sf_exp_rel' (base: MyNat_u) (power: MyNat_u) (base_r: MyNat) (power_r: MyNat) (VV: MyNat_u): (base = (⌊ base_r -⌋)) -> ((power = (⌊ power_r -⌋)) -> (((⌊ sf_exp base_r power_r -⌋) = VV) <-> (sf_exp_rel base power VV))). 
Proof. 
	intros -> ->. 
	refine (sf_exp__sf_exp_rel base_r power_r VV). 
Qed. 
#[global] Hint Resolve sf_exp__sf_exp_rel' : f_rel_funct_db.
Theorem sf_exp_rel_mk [base: MyNat_u] [power: MyNat_u] (base_p: (MyNat_wf base) /\ True) (power_p: (MyNat_wf power) /\ True): {VV: _ | sf_exp_rel base power VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (sf_exp_rel base power VV)) (sf_exp (exist _ base base_p) (exist _ power power_p)) _); 
	rewrite <- sf_exp__sf_exp_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve sf_exp_rel_mk : f_rel_funct_db.
#[global] Instance sf_expPack : (@Pack (MyNat ::RT (fun (base_r: MyNat) => (MyNat ::RT (fun (power_r: MyNat) => nilRT)))) (MyNat_u ::UT (MyNat_u ::UT nilUT)) (ltac: (mkProjectsArgListTG (MyNat ::RT (fun (base_r: MyNat) => (MyNat ::RT (fun (power_r: MyNat) => nilRT)))) (MyNat_u ::UT (MyNat_u ::UT nilUT)))) MyNat_u (fun (x_76897496: (ArgList MyNat ::RT (fun (base_r: MyNat) => (MyNat ::RT (fun (power_r: MyNat) => nilRT))))) => (fun (v_x_76897496: MyNat_u) => (ltac: (flattenP (fun (base_r: MyNat) => (fun (power_r: MyNat) => (fun (VV: MyNat_u) => ((MyNat_wf VV) /\ True)))) x_76897496 v_x_76897496))))).
Proof. 
	buildPackG sf_exp sf_exp_rel sf_exp__sf_exp_rel sf_exp_rel_funct. 
Defined.
Definition sndSF_spec (p: Natprod): Type := 
	MyNat. 
#[global] Hint Unfold sndSF_spec : lia_unfold.
Definition sndSF (p: Natprod): sndSF_spec p. 
Proof. 
	destruct p as [p p_p]. 
	induction p as [(*Pair*) n1 n2]. 
	  - intros . 
		refine (exist _ n2 _); 
		solver.  
Defined. 
Inductive sndSF_rel : (Natprod_u -> (MyNat_u -> Prop)) := 
	 | sndSF_Pair: (forall n1 n2 , sndSF_rel (Pair_u n1 n2) n2). 
#[global] Hint Constructors sndSF_rel : core_hint_db.
#[global] Instance sndSF_lookup_rel : dictionary rel sndSF := { 
	lookup' := sndSF_rel
}.
#[global] Instance sndSF_getF : getFunc sndSF_rel := { 
	getF' := sndSF
}.
Theorem sndSF_rel_funct [p: Natprod_u]: (forall (VV: MyNat_u) (VV': MyNat_u) (H: sndSF_rel p VV) (K: sndSF_rel p VV') , VV = VV'). 
Proof. 
	induction p as [(*Pair*) n1 n2]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve sndSF_rel_funct : f_rel_funct_db.
Theorem sndSF_Pair_lem (n1: _) (n2: _): (sndSF_rel (Pair_u n1 n2) n2) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite sndSF_Pair_lem : f_rel_back.
Theorem sndSF_rel_ex (p: Natprod_u) (p_p: (Natprod_wf p) /\ True): sndSF_rel p (⌊ sndSF (exist _ p p_p) -⌋). 
Proof. 
	Opaque sndSF.
	existence_lemma_pre sndSF; 
	induction p as [(*Pair*) n1 n2]; 
	intros ; 
	[fix_notations]; 
	simpl in *. 
	Transparent sndSF.
	all: existence_lemma_quicksolve sndSF; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve sndSF_rel_ex : rel_ax_db.
#[global] Opaque sndSF. 
Theorem sndSF__sndSF_rel_rw (p: Natprod_u) (p_p: (Natprod_wf p) /\ True) (VV: MyNat_u): ((⌊ sndSF (exist _ p p_p) -⌋) = VV) <-> (sndSF_rel p VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite sndSF__sndSF_rel_rw : f_rel_funct_db.
#[global] Hint Resolve sndSF__sndSF_rel_rw : rel_ax_db.
#[global] Instance sndSF_lookup_rw : dictionary rwLem sndSF := { 
	lookup' := sndSF__sndSF_rel_rw
}.
Theorem sndSF__sndSF_rel (p_r: Natprod) (VV: MyNat_u): ((⌊ sndSF p_r -⌋) = VV) <-> (sndSF_rel (⌊ p_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite sndSF__sndSF_rel : f_rel_funct_db.
Theorem sndSF__sndSF_rel' (p: Natprod_u) (p_r: Natprod) (VV: MyNat_u): (p = (⌊ p_r -⌋)) -> (((⌊ sndSF p_r -⌋) = VV) <-> (sndSF_rel p VV)). 
Proof. 
	intros ->. 
	refine (sndSF__sndSF_rel p_r VV). 
Qed. 
#[global] Hint Resolve sndSF__sndSF_rel' : f_rel_funct_db.
Theorem sndSF_rel_mk [p: Natprod_u] (p_p: (Natprod_wf p) /\ True): {VV: _ | sndSF_rel p VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (sndSF_rel p VV)) (sndSF (exist _ p p_p)) _); 
	rewrite <- sndSF__sndSF_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve sndSF_rel_mk : f_rel_funct_db.
#[global] Instance sndSFPack : (@Pack (Natprod ::RT (fun (p_r: Natprod) => nilRT)) (Natprod_u ::UT nilUT) (ltac: (mkProjectsArgListTG (Natprod ::RT (fun (p_r: Natprod) => nilRT)) (Natprod_u ::UT nilUT))) MyNat_u (fun (x_54217211: (ArgList Natprod ::RT (fun (p_r: Natprod) => nilRT))) => (fun (v_x_54217211: MyNat_u) => (ltac: (flattenP (fun (p_r: Natprod) => (fun (VV: MyNat_u) => ((MyNat_wf VV) /\ True))) x_54217211 v_x_54217211))))).
Proof. 
	buildPackG sndSF sndSF_rel sndSF__sndSF_rel sndSF_rel_funct. 
Defined.
Definition surjective_pairing_spec (p: Natprod): Type := 
	{{forall (sndSFres: MyNat_u), (sndSF_rel (⌊ p -⌋) sndSFres) -> (forall (fstSFres: MyNat_u), (fstSF_rel (⌊ p -⌋) fstSFres) -> ((⌊ p -⌋) = (Pair_u fstSFres sndSFres)))}}. 
#[global] Hint Unfold surjective_pairing_spec : lia_unfold.
Theorem surjective_pairing (p: Natprod): surjective_pairing_spec p. 
Proof. 
	destruct p as [p p_p]. 
	induction p as [(*Pair*) n m]. 
	  - intros . 
		refine (exist _ unit _); 
		solver.  
Qed. 
Definition surjective_pairing'_spec (n: MyNat) (m: MyNat): Type := 
	{{forall (sndSFres: MyNat_u), (sndSF_rel (Pair_u (⌊ n -⌋) (⌊ m -⌋)) sndSFres) -> (forall (fstSFres: MyNat_u), (fstSF_rel (Pair_u (⌊ n -⌋) (⌊ m -⌋)) fstSFres) -> ((Pair_u (⌊ n -⌋) (⌊ m -⌋)) == (Pair_u fstSFres sndSFres)))}}. 
#[global] Hint Unfold surjective_pairing'_spec : lia_unfold.
Theorem surjective_pairing' (n: MyNat) (m: MyNat): surjective_pairing'_spec n m. 
Proof. 
	destruct n as [n n_p]. 
	destruct m as [m m_p]. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition two_spec: Type := 
	MyNat. 
#[global] Hint Unfold two_spec : lia_unfold.
Definition two: two_spec. 
Proof. 
	refine (subsumptionCast _ _ 
		(S 
		(subsumptionCast MyNat_u (fun (VV: MyNat_u) => ((MyNat_wf VV) /\ True)) one (ltac: (solver)))) _); 
	solver. 
Defined. 
Inductive two_rel : (MyNat_u -> Prop) := 
	 | two_def: two_rel (S_u (⌊ one -⌋)). 
#[global] Hint Constructors two_rel : core_hint_db.
#[global] Instance two_lookup_rel : dictionary rel two := { 
	lookup' := two_rel
}.
#[global] Instance two_getF : getFunc two_rel := { 
	getF' := two
}.
Theorem two_rel_funct: (forall (VV: MyNat_u) (VV': MyNat_u) (H: two_rel VV) (K: two_rel VV') , VV = VV'). 
Proof. 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve two_rel_funct : f_rel_funct_db.
Theorem two_def_lem: (two_rel (S_u (⌊ one -⌋))) <-> True. 
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
Theorem two__two_rel_rw (VV: MyNat_u): ((⌊ two -⌋) = VV) <-> (two_rel VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite two__two_rel_rw : f_rel_funct_db.
#[global] Hint Resolve two__two_rel_rw : rel_ax_db.
#[global] Instance two_lookup_rw : dictionary rwLem two := { 
	lookup' := two__two_rel_rw
}.
Theorem two__two_rel (VV: MyNat_u): ((⌊ two -⌋) = VV) <-> (two_rel VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite two__two_rel : f_rel_funct_db.
Theorem two__two_rel' (VV: MyNat_u): ((⌊ two -⌋) = VV) <-> (two_rel VV). 
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
Definition test_leb1_spec: Type := 
	{{forall (lebres: SFBool_u), (leb_rel (⌊ two -⌋) (⌊ two -⌋) lebres) -> (lebres = SFTrue_u)}}. 
#[global] Hint Unfold test_leb1_spec : lia_unfold.
Theorem test_leb1: test_leb1_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition test_ltb1_spec: Type := 
	{{forall (ltbres: SFBool_u), (ltb_rel (⌊ two -⌋) (⌊ two -⌋) ltbres) -> (ltbres = SFFalse_u)}}. 
#[global] Hint Unfold test_ltb1_spec : lia_unfold.
Theorem test_ltb1: test_ltb1_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition three_spec: Type := 
	MyNat. 
#[global] Hint Unfold three_spec : lia_unfold.
Definition three: three_spec. 
Proof. 
	refine (subsumptionCast _ _ 
		(S 
		(subsumptionCast MyNat_u (fun (VV: MyNat_u) => ((MyNat_wf VV) /\ True)) two (ltac: (solver)))) _); 
	solver. 
Defined. 
Inductive three_rel : (MyNat_u -> Prop) := 
	 | three_def: three_rel (S_u (⌊ two -⌋)). 
#[global] Hint Constructors three_rel : core_hint_db.
#[global] Instance three_lookup_rel : dictionary rel three := { 
	lookup' := three_rel
}.
#[global] Instance three_getF : getFunc three_rel := { 
	getF' := three
}.
Theorem three_rel_funct: (forall (VV: MyNat_u) (VV': MyNat_u) (H: three_rel VV) (K: three_rel VV') , VV = VV'). 
Proof. 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve three_rel_funct : f_rel_funct_db.
Theorem three_def_lem: (three_rel (S_u (⌊ two -⌋))) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite three_def_lem : f_rel_back.
Theorem three_rel_ex: three_rel (⌊ three -⌋). 
Proof. 
	Opaque three.
	existence_lemma_pre three; 
	fix_notations; 
	simpl in *. 
	Transparent three.
	all: existence_lemma_quicksolve three; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve three_rel_ex : rel_ax_db.
#[global] Opaque three. 
Theorem three__three_rel_rw (VV: MyNat_u): ((⌊ three -⌋) = VV) <-> (three_rel VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite three__three_rel_rw : f_rel_funct_db.
#[global] Hint Resolve three__three_rel_rw : rel_ax_db.
#[global] Instance three_lookup_rw : dictionary rwLem three := { 
	lookup' := three__three_rel_rw
}.
Theorem three__three_rel (VV: MyNat_u): ((⌊ three -⌋) = VV) <-> (three_rel VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite three__three_rel : f_rel_funct_db.
Theorem three__three_rel' (VV: MyNat_u): ((⌊ three -⌋) = VV) <-> (three_rel VV). 
Proof. 
	intros . 
	refine (three__three_rel VV). 
Qed. 
#[global] Hint Resolve three__three_rel' : f_rel_funct_db.
Theorem three_rel_mk: {VV: _ | three_rel VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (three_rel VV)) three _); 
	rewrite <- three__three_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve three_rel_mk : f_rel_funct_db.
Definition four_spec: Type := 
	MyNat. 
#[global] Hint Unfold four_spec : lia_unfold.
Definition four: four_spec. 
Proof. 
	refine (subsumptionCast _ _ 
		(S 
		(subsumptionCast MyNat_u (fun (VV: MyNat_u) => ((MyNat_wf VV) /\ True)) three (ltac: (solver)))) _); 
	solver. 
Defined. 
Inductive four_rel : (MyNat_u -> Prop) := 
	 | four_def: four_rel (S_u (⌊ three -⌋)). 
#[global] Hint Constructors four_rel : core_hint_db.
#[global] Instance four_lookup_rel : dictionary rel four := { 
	lookup' := four_rel
}.
#[global] Instance four_getF : getFunc four_rel := { 
	getF' := four
}.
Theorem four_rel_funct: (forall (VV: MyNat_u) (VV': MyNat_u) (H: four_rel VV) (K: four_rel VV') , VV = VV'). 
Proof. 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve four_rel_funct : f_rel_funct_db.
Theorem four_def_lem: (four_rel (S_u (⌊ three -⌋))) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite four_def_lem : f_rel_back.
Theorem four_rel_ex: four_rel (⌊ four -⌋). 
Proof. 
	Opaque four.
	existence_lemma_pre four; 
	fix_notations; 
	simpl in *. 
	Transparent four.
	all: existence_lemma_quicksolve four; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve four_rel_ex : rel_ax_db.
#[global] Opaque four. 
Theorem four__four_rel_rw (VV: MyNat_u): ((⌊ four -⌋) = VV) <-> (four_rel VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite four__four_rel_rw : f_rel_funct_db.
#[global] Hint Resolve four__four_rel_rw : rel_ax_db.
#[global] Instance four_lookup_rw : dictionary rwLem four := { 
	lookup' := four__four_rel_rw
}.
Theorem four__four_rel (VV: MyNat_u): ((⌊ four -⌋) = VV) <-> (four_rel VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite four__four_rel : f_rel_funct_db.
Theorem four__four_rel' (VV: MyNat_u): ((⌊ four -⌋) = VV) <-> (four_rel VV). 
Proof. 
	intros . 
	refine (four__four_rel VV). 
Qed. 
#[global] Hint Resolve four__four_rel' : f_rel_funct_db.
Theorem four_rel_mk: {VV: _ | four_rel VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (four_rel VV)) four _); 
	rewrite <- four__four_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve four_rel_mk : f_rel_funct_db.
Definition five_spec: Type := 
	MyNat. 
#[global] Hint Unfold five_spec : lia_unfold.
Definition five: five_spec. 
Proof. 
	refine (subsumptionCast _ _ 
		(S 
		(subsumptionCast MyNat_u (fun (VV: MyNat_u) => ((MyNat_wf VV) /\ True)) four (ltac: (solver)))) _); 
	solver. 
Defined. 
Inductive five_rel : (MyNat_u -> Prop) := 
	 | five_def: five_rel (S_u (⌊ four -⌋)). 
#[global] Hint Constructors five_rel : core_hint_db.
#[global] Instance five_lookup_rel : dictionary rel five := { 
	lookup' := five_rel
}.
#[global] Instance five_getF : getFunc five_rel := { 
	getF' := five
}.
Theorem five_rel_funct: (forall (VV: MyNat_u) (VV': MyNat_u) (H: five_rel VV) (K: five_rel VV') , VV = VV'). 
Proof. 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve five_rel_funct : f_rel_funct_db.
Theorem five_def_lem: (five_rel (S_u (⌊ four -⌋))) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite five_def_lem : f_rel_back.
Theorem five_rel_ex: five_rel (⌊ five -⌋). 
Proof. 
	Opaque five.
	existence_lemma_pre five; 
	fix_notations; 
	simpl in *. 
	Transparent five.
	all: existence_lemma_quicksolve five; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve five_rel_ex : rel_ax_db.
#[global] Opaque five. 
Theorem five__five_rel_rw (VV: MyNat_u): ((⌊ five -⌋) = VV) <-> (five_rel VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite five__five_rel_rw : f_rel_funct_db.
#[global] Hint Resolve five__five_rel_rw : rel_ax_db.
#[global] Instance five_lookup_rw : dictionary rwLem five := { 
	lookup' := five__five_rel_rw
}.
Theorem five__five_rel (VV: MyNat_u): ((⌊ five -⌋) = VV) <-> (five_rel VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite five__five_rel : f_rel_funct_db.
Theorem five__five_rel' (VV: MyNat_u): ((⌊ five -⌋) = VV) <-> (five_rel VV). 
Proof. 
	intros . 
	refine (five__five_rel VV). 
Qed. 
#[global] Hint Resolve five__five_rel' : f_rel_funct_db.
Theorem five_rel_mk: {VV: _ | five_rel VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (five_rel VV)) five _); 
	rewrite <- five__five_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve five_rel_mk : f_rel_funct_db.
Definition six_spec: Type := 
	MyNat. 
#[global] Hint Unfold six_spec : lia_unfold.
Definition six: six_spec. 
Proof. 
	refine (subsumptionCast _ _ 
		(S 
		(subsumptionCast MyNat_u (fun (VV: MyNat_u) => ((MyNat_wf VV) /\ True)) five (ltac: (solver)))) _); 
	solver. 
Defined. 
Inductive six_rel : (MyNat_u -> Prop) := 
	 | six_def: six_rel (S_u (⌊ five -⌋)). 
#[global] Hint Constructors six_rel : core_hint_db.
#[global] Instance six_lookup_rel : dictionary rel six := { 
	lookup' := six_rel
}.
#[global] Instance six_getF : getFunc six_rel := { 
	getF' := six
}.
Theorem six_rel_funct: (forall (VV: MyNat_u) (VV': MyNat_u) (H: six_rel VV) (K: six_rel VV') , VV = VV'). 
Proof. 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve six_rel_funct : f_rel_funct_db.
Theorem six_def_lem: (six_rel (S_u (⌊ five -⌋))) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite six_def_lem : f_rel_back.
Theorem six_rel_ex: six_rel (⌊ six -⌋). 
Proof. 
	Opaque six.
	existence_lemma_pre six; 
	fix_notations; 
	simpl in *. 
	Transparent six.
	all: existence_lemma_quicksolve six; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve six_rel_ex : rel_ax_db.
#[global] Opaque six. 
Theorem six__six_rel_rw (VV: MyNat_u): ((⌊ six -⌋) = VV) <-> (six_rel VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite six__six_rel_rw : f_rel_funct_db.
#[global] Hint Resolve six__six_rel_rw : rel_ax_db.
#[global] Instance six_lookup_rw : dictionary rwLem six := { 
	lookup' := six__six_rel_rw
}.
Theorem six__six_rel (VV: MyNat_u): ((⌊ six -⌋) = VV) <-> (six_rel VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite six__six_rel : f_rel_funct_db.
Theorem six__six_rel' (VV: MyNat_u): ((⌊ six -⌋) = VV) <-> (six_rel VV). 
Proof. 
	intros . 
	refine (six__six_rel VV). 
Qed. 
#[global] Hint Resolve six__six_rel' : f_rel_funct_db.
Theorem six_rel_mk: {VV: _ | six_rel VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (six_rel VV)) six _); 
	rewrite <- six__six_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve six_rel_mk : f_rel_funct_db.
Definition seven_spec: Type := 
	MyNat. 
#[global] Hint Unfold seven_spec : lia_unfold.
Definition seven: seven_spec. 
Proof. 
	refine (subsumptionCast _ _ 
		(S 
		(subsumptionCast MyNat_u (fun (VV: MyNat_u) => ((MyNat_wf VV) /\ True)) six (ltac: (solver)))) _); 
	solver. 
Defined. 
Inductive seven_rel : (MyNat_u -> Prop) := 
	 | seven_def: seven_rel (S_u (⌊ six -⌋)). 
#[global] Hint Constructors seven_rel : core_hint_db.
#[global] Instance seven_lookup_rel : dictionary rel seven := { 
	lookup' := seven_rel
}.
#[global] Instance seven_getF : getFunc seven_rel := { 
	getF' := seven
}.
Theorem seven_rel_funct: (forall (VV: MyNat_u) (VV': MyNat_u) (H: seven_rel VV) (K: seven_rel VV') , VV = VV'). 
Proof. 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve seven_rel_funct : f_rel_funct_db.
Theorem seven_def_lem: (seven_rel (S_u (⌊ six -⌋))) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite seven_def_lem : f_rel_back.
Theorem seven_rel_ex: seven_rel (⌊ seven -⌋). 
Proof. 
	Opaque seven.
	existence_lemma_pre seven; 
	fix_notations; 
	simpl in *. 
	Transparent seven.
	all: existence_lemma_quicksolve seven; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve seven_rel_ex : rel_ax_db.
#[global] Opaque seven. 
Theorem seven__seven_rel_rw (VV: MyNat_u): ((⌊ seven -⌋) = VV) <-> (seven_rel VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite seven__seven_rel_rw : f_rel_funct_db.
#[global] Hint Resolve seven__seven_rel_rw : rel_ax_db.
#[global] Instance seven_lookup_rw : dictionary rwLem seven := { 
	lookup' := seven__seven_rel_rw
}.
Theorem seven__seven_rel (VV: MyNat_u): ((⌊ seven -⌋) = VV) <-> (seven_rel VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite seven__seven_rel : f_rel_funct_db.
Theorem seven__seven_rel' (VV: MyNat_u): ((⌊ seven -⌋) = VV) <-> (seven_rel VV). 
Proof. 
	intros . 
	refine (seven__seven_rel VV). 
Qed. 
#[global] Hint Resolve seven__seven_rel' : f_rel_funct_db.
Theorem seven_rel_mk: {VV: _ | seven_rel VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (seven_rel VV)) seven _); 
	rewrite <- seven__seven_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve seven_rel_mk : f_rel_funct_db.
Definition eight_spec: Type := 
	MyNat. 
#[global] Hint Unfold eight_spec : lia_unfold.
Definition eight: eight_spec. 
Proof. 
	refine (subsumptionCast _ _ 
		(S 
		(subsumptionCast MyNat_u (fun (VV: MyNat_u) => ((MyNat_wf VV) /\ True)) seven (ltac: (solver)))) _); 
	solver. 
Defined. 
Inductive eight_rel : (MyNat_u -> Prop) := 
	 | eight_def: eight_rel (S_u (⌊ seven -⌋)). 
#[global] Hint Constructors eight_rel : core_hint_db.
#[global] Instance eight_lookup_rel : dictionary rel eight := { 
	lookup' := eight_rel
}.
#[global] Instance eight_getF : getFunc eight_rel := { 
	getF' := eight
}.
Theorem eight_rel_funct: (forall (VV: MyNat_u) (VV': MyNat_u) (H: eight_rel VV) (K: eight_rel VV') , VV = VV'). 
Proof. 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve eight_rel_funct : f_rel_funct_db.
Theorem eight_def_lem: (eight_rel (S_u (⌊ seven -⌋))) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite eight_def_lem : f_rel_back.
Theorem eight_rel_ex: eight_rel (⌊ eight -⌋). 
Proof. 
	Opaque eight.
	existence_lemma_pre eight; 
	fix_notations; 
	simpl in *. 
	Transparent eight.
	all: existence_lemma_quicksolve eight; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve eight_rel_ex : rel_ax_db.
#[global] Opaque eight. 
Theorem eight__eight_rel_rw (VV: MyNat_u): ((⌊ eight -⌋) = VV) <-> (eight_rel VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite eight__eight_rel_rw : f_rel_funct_db.
#[global] Hint Resolve eight__eight_rel_rw : rel_ax_db.
#[global] Instance eight_lookup_rw : dictionary rwLem eight := { 
	lookup' := eight__eight_rel_rw
}.
Theorem eight__eight_rel (VV: MyNat_u): ((⌊ eight -⌋) = VV) <-> (eight_rel VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite eight__eight_rel : f_rel_funct_db.
Theorem eight__eight_rel' (VV: MyNat_u): ((⌊ eight -⌋) = VV) <-> (eight_rel VV). 
Proof. 
	intros . 
	refine (eight__eight_rel VV). 
Qed. 
#[global] Hint Resolve eight__eight_rel' : f_rel_funct_db.
Theorem eight_rel_mk: {VV: _ | eight_rel VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (eight_rel VV)) eight _); 
	rewrite <- eight__eight_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve eight_rel_mk : f_rel_funct_db.
Definition nine_spec: Type := 
	MyNat. 
#[global] Hint Unfold nine_spec : lia_unfold.
Definition nine: nine_spec. 
Proof. 
	refine (subsumptionCast _ _ 
		(S 
		(subsumptionCast MyNat_u (fun (VV: MyNat_u) => ((MyNat_wf VV) /\ True)) eight (ltac: (solver)))) _); 
	solver. 
Defined. 
Inductive nine_rel : (MyNat_u -> Prop) := 
	 | nine_def: nine_rel (S_u (⌊ eight -⌋)). 
#[global] Hint Constructors nine_rel : core_hint_db.
#[global] Instance nine_lookup_rel : dictionary rel nine := { 
	lookup' := nine_rel
}.
#[global] Instance nine_getF : getFunc nine_rel := { 
	getF' := nine
}.
Theorem nine_rel_funct: (forall (VV: MyNat_u) (VV': MyNat_u) (H: nine_rel VV) (K: nine_rel VV') , VV = VV'). 
Proof. 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve nine_rel_funct : f_rel_funct_db.
Theorem nine_def_lem: (nine_rel (S_u (⌊ eight -⌋))) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite nine_def_lem : f_rel_back.
Theorem nine_rel_ex: nine_rel (⌊ nine -⌋). 
Proof. 
	Opaque nine.
	existence_lemma_pre nine; 
	fix_notations; 
	simpl in *. 
	Transparent nine.
	all: existence_lemma_quicksolve nine; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve nine_rel_ex : rel_ax_db.
#[global] Opaque nine. 
Theorem nine__nine_rel_rw (VV: MyNat_u): ((⌊ nine -⌋) = VV) <-> (nine_rel VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite nine__nine_rel_rw : f_rel_funct_db.
#[global] Hint Resolve nine__nine_rel_rw : rel_ax_db.
#[global] Instance nine_lookup_rw : dictionary rwLem nine := { 
	lookup' := nine__nine_rel_rw
}.
Theorem nine__nine_rel (VV: MyNat_u): ((⌊ nine -⌋) = VV) <-> (nine_rel VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite nine__nine_rel : f_rel_funct_db.
Theorem nine__nine_rel' (VV: MyNat_u): ((⌊ nine -⌋) = VV) <-> (nine_rel VV). 
Proof. 
	intros . 
	refine (nine__nine_rel VV). 
Qed. 
#[global] Hint Resolve nine__nine_rel' : f_rel_funct_db.
Theorem nine_rel_mk: {VV: _ | nine_rel VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (nine_rel VV)) nine _); 
	rewrite <- nine__nine_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve nine_rel_mk : f_rel_funct_db.
Definition ten_spec: Type := 
	MyNat. 
#[global] Hint Unfold ten_spec : lia_unfold.
Definition ten: ten_spec. 
Proof. 
	refine (subsumptionCast _ _ 
		(S 
		(subsumptionCast MyNat_u (fun (VV: MyNat_u) => ((MyNat_wf VV) /\ True)) nine (ltac: (solver)))) _); 
	solver. 
Defined. 
Inductive ten_rel : (MyNat_u -> Prop) := 
	 | ten_def: ten_rel (S_u (⌊ nine -⌋)). 
#[global] Hint Constructors ten_rel : core_hint_db.
#[global] Instance ten_lookup_rel : dictionary rel ten := { 
	lookup' := ten_rel
}.
#[global] Instance ten_getF : getFunc ten_rel := { 
	getF' := ten
}.
Theorem ten_rel_funct: (forall (VV: MyNat_u) (VV': MyNat_u) (H: ten_rel VV) (K: ten_rel VV') , VV = VV'). 
Proof. 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve ten_rel_funct : f_rel_funct_db.
Theorem ten_def_lem: (ten_rel (S_u (⌊ nine -⌋))) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite ten_def_lem : f_rel_back.
Theorem ten_rel_ex: ten_rel (⌊ ten -⌋). 
Proof. 
	Opaque ten.
	existence_lemma_pre ten; 
	fix_notations; 
	simpl in *. 
	Transparent ten.
	all: existence_lemma_quicksolve ten; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve ten_rel_ex : rel_ax_db.
#[global] Opaque ten. 
Theorem ten__ten_rel_rw (VV: MyNat_u): ((⌊ ten -⌋) = VV) <-> (ten_rel VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite ten__ten_rel_rw : f_rel_funct_db.
#[global] Hint Resolve ten__ten_rel_rw : rel_ax_db.
#[global] Instance ten_lookup_rw : dictionary rwLem ten := { 
	lookup' := ten__ten_rel_rw
}.
Theorem ten__ten_rel (VV: MyNat_u): ((⌊ ten -⌋) = VV) <-> (ten_rel VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite ten__ten_rel : f_rel_funct_db.
Theorem ten__ten_rel' (VV: MyNat_u): ((⌊ ten -⌋) = VV) <-> (ten_rel VV). 
Proof. 
	intros . 
	refine (ten__ten_rel VV). 
Qed. 
#[global] Hint Resolve ten__ten_rel' : f_rel_funct_db.
Theorem ten_rel_mk: {VV: _ | ten_rel VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (ten_rel VV)) ten _); 
	rewrite <- ten__ten_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve ten_rel_mk : f_rel_funct_db.
Definition eleven_spec: Type := 
	MyNat. 
#[global] Hint Unfold eleven_spec : lia_unfold.
Definition eleven: eleven_spec. 
Proof. 
	refine (subsumptionCast _ _ 
		(S 
		(subsumptionCast MyNat_u (fun (VV: MyNat_u) => ((MyNat_wf VV) /\ True)) ten (ltac: (solver)))) _); 
	solver. 
Defined. 
Inductive eleven_rel : (MyNat_u -> Prop) := 
	 | eleven_def: eleven_rel (S_u (⌊ ten -⌋)). 
#[global] Hint Constructors eleven_rel : core_hint_db.
#[global] Instance eleven_lookup_rel : dictionary rel eleven := { 
	lookup' := eleven_rel
}.
#[global] Instance eleven_getF : getFunc eleven_rel := { 
	getF' := eleven
}.
Theorem eleven_rel_funct: (forall (VV: MyNat_u) (VV': MyNat_u) (H: eleven_rel VV) (K: eleven_rel VV') , VV = VV'). 
Proof. 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve eleven_rel_funct : f_rel_funct_db.
Theorem eleven_def_lem: (eleven_rel (S_u (⌊ ten -⌋))) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite eleven_def_lem : f_rel_back.
Theorem eleven_rel_ex: eleven_rel (⌊ eleven -⌋). 
Proof. 
	Opaque eleven.
	existence_lemma_pre eleven; 
	fix_notations; 
	simpl in *. 
	Transparent eleven.
	all: existence_lemma_quicksolve eleven; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve eleven_rel_ex : rel_ax_db.
#[global] Opaque eleven. 
Theorem eleven__eleven_rel_rw (VV: MyNat_u): ((⌊ eleven -⌋) = VV) <-> (eleven_rel VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite eleven__eleven_rel_rw : f_rel_funct_db.
#[global] Hint Resolve eleven__eleven_rel_rw : rel_ax_db.
#[global] Instance eleven_lookup_rw : dictionary rwLem eleven := { 
	lookup' := eleven__eleven_rel_rw
}.
Theorem eleven__eleven_rel (VV: MyNat_u): ((⌊ eleven -⌋) = VV) <-> (eleven_rel VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite eleven__eleven_rel : f_rel_funct_db.
Theorem eleven__eleven_rel' (VV: MyNat_u): ((⌊ eleven -⌋) = VV) <-> (eleven_rel VV). 
Proof. 
	intros . 
	refine (eleven__eleven_rel VV). 
Qed. 
#[global] Hint Resolve eleven__eleven_rel' : f_rel_funct_db.
Theorem eleven_rel_mk: {VV: _ | eleven_rel VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (eleven_rel VV)) eleven _); 
	rewrite <- eleven__eleven_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve eleven_rel_mk : f_rel_funct_db.
Definition twelve_spec: Type := 
	MyNat. 
#[global] Hint Unfold twelve_spec : lia_unfold.
Definition twelve: twelve_spec. 
Proof. 
	refine (subsumptionCast _ _ 
		(S 
		(subsumptionCast MyNat_u (fun (VV: MyNat_u) => ((MyNat_wf VV) /\ True)) eleven (ltac: (solver)))) _); 
	solver. 
Defined. 
Inductive twelve_rel : (MyNat_u -> Prop) := 
	 | twelve_def: twelve_rel (S_u (⌊ eleven -⌋)). 
#[global] Hint Constructors twelve_rel : core_hint_db.
#[global] Instance twelve_lookup_rel : dictionary rel twelve := { 
	lookup' := twelve_rel
}.
#[global] Instance twelve_getF : getFunc twelve_rel := { 
	getF' := twelve
}.
Theorem twelve_rel_funct: (forall (VV: MyNat_u) (VV': MyNat_u) (H: twelve_rel VV) (K: twelve_rel VV') , VV = VV'). 
Proof. 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve twelve_rel_funct : f_rel_funct_db.
Theorem twelve_def_lem: (twelve_rel (S_u (⌊ eleven -⌋))) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite twelve_def_lem : f_rel_back.
Theorem twelve_rel_ex: twelve_rel (⌊ twelve -⌋). 
Proof. 
	Opaque twelve.
	existence_lemma_pre twelve; 
	fix_notations; 
	simpl in *. 
	Transparent twelve.
	all: existence_lemma_quicksolve twelve; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve twelve_rel_ex : rel_ax_db.
#[global] Opaque twelve. 
Theorem twelve__twelve_rel_rw (VV: MyNat_u): ((⌊ twelve -⌋) = VV) <-> (twelve_rel VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite twelve__twelve_rel_rw : f_rel_funct_db.
#[global] Hint Resolve twelve__twelve_rel_rw : rel_ax_db.
#[global] Instance twelve_lookup_rw : dictionary rwLem twelve := { 
	lookup' := twelve__twelve_rel_rw
}.
Theorem twelve__twelve_rel (VV: MyNat_u): ((⌊ twelve -⌋) = VV) <-> (twelve_rel VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite twelve__twelve_rel : f_rel_funct_db.
Theorem twelve__twelve_rel' (VV: MyNat_u): ((⌊ twelve -⌋) = VV) <-> (twelve_rel VV). 
Proof. 
	intros . 
	refine (twelve__twelve_rel VV). 
Qed. 
#[global] Hint Resolve twelve__twelve_rel' : f_rel_funct_db.
Theorem twelve_rel_mk: {VV: _ | twelve_rel VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (twelve_rel VV)) twelve _); 
	rewrite <- twelve__twelve_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve twelve_rel_mk : f_rel_funct_db.
Definition test_leb2_spec: Type := 
	{{forall (lebres: SFBool_u), (leb_rel (⌊ two -⌋) (⌊ four -⌋) lebres) -> (lebres = SFTrue_u)}}. 
#[global] Hint Unfold test_leb2_spec : lia_unfold.
Theorem test_leb2: test_leb2_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition test_leb3_spec: Type := 
	{{forall (lebres: SFBool_u), (leb_rel (⌊ four -⌋) (⌊ two -⌋) lebres) -> (lebres = SFFalse_u)}}. 
#[global] Hint Unfold test_leb3_spec : lia_unfold.
Theorem test_leb3: test_leb3_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition test_ltb2_spec: Type := 
	{{forall (ltbres: SFBool_u), (ltb_rel (⌊ two -⌋) (⌊ four -⌋) ltbres) -> (ltbres = SFTrue_u)}}. 
#[global] Hint Unfold test_ltb2_spec : lia_unfold.
Theorem test_ltb2: test_ltb2_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition test_ltb3_spec: Type := 
	{{forall (ltbres: SFBool_u), (ltb_rel (⌊ four -⌋) (⌊ two -⌋) ltbres) -> (ltbres = SFFalse_u)}}. 
#[global] Hint Unfold test_ltb3_spec : lia_unfold.
Theorem test_ltb3: test_ltb3_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition test_factorial1_spec: Type := 
	{{forall (factorialres: MyNat_u), (factorial_rel (⌊ three -⌋) factorialres) -> (factorialres = (⌊ six -⌋))}}. 
#[global] Hint Unfold test_factorial1_spec : lia_unfold.
Theorem test_factorial1: test_factorial1_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition test_mult1_spec: Type := 
	{{forall (multres: MyNat_u), (mult_rel (⌊ three -⌋) (⌊ three -⌋) multres) -> (multres = (⌊ nine -⌋))}}. 
#[global] Hint Unfold test_mult1_spec : lia_unfold.
Theorem test_mult1: test_mult1_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition zero_nbeq_plus_1_spec (n: MyNat): Type := 
	{{forall (plusres: MyNat_u), (plus_rel (⌊ n -⌋) (⌊ one -⌋) plusres) -> (forall (eqbres: SFBool_u), (eqb_rel O_u plusres eqbres) -> (eqbres = SFFalse_u))}}. 
#[global] Hint Unfold zero_nbeq_plus_1_spec : lia_unfold.
Theorem zero_nbeq_plus_1 (n: MyNat): zero_nbeq_plus_1_spec n. 
Proof. 
	destruct n as [n n_p]. 
	induction n as [(*O*)  | (*S*) n' IH_n']. 
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
Qed. 
Inductive Modifier_u : Type := 
	 | Minus_u: Modifier_u
	 | Natural_u: Modifier_u
	 | Plus_u: Modifier_u. 
Fixpoint Modifier_eq (x: Modifier_u) (y: Modifier_u): bool := 
	match (x, y) with (Minus_u, Minus_u) => true | (Natural_u, Natural_u) => true | (Plus_u, Plus_u) => true | (_, _) => false end. 
Theorem Modifier_eq_refl: (forall (x: Modifier_u) , is_true (Modifier_eq x x)). 
Proof. 
	eq_refl_rec. 
Qed. 
#[global] Hint Resolve Modifier_eq_refl : eq_hint_db.
Theorem Modifier_eqb_eq: (forall (s: Modifier_u) (t: Modifier_u) , (is_true (Modifier_eq s t)) -> (s = t)). 
Proof. 
	eqb_eq_lem. 
Qed. 
#[global] Hint Resolve Modifier_eqb_eq : eq_hint_db.
#[global] Instance leibnitz_eq_Modifier : LeibnitzEqB := { 
	equalB' := Modifier_eq;
	refl' := Modifier_eq_refl;
	eqb_eq' := Modifier_eqb_eq
}.
Fixpoint Modifier_wf (x: Modifier_u): Prop := 
	match x with Minus_u => True | Natural_u => True | Plus_u => True end. 
Theorem Modifier_wf_ref [p: Modifier_u -> Prop] (tm: {v: Modifier_u | (Modifier_wf v) /\ (p v)}): Modifier_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation Modifier := {x: Modifier_u | (Modifier_wf x) /\ True}. 
Definition Minus_lem: (Modifier_wf Minus_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Minus: Modifier := 
	exist _ Minus_u Minus_lem. 
Definition Natural_lem: (Modifier_wf Natural_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Natural: Modifier := 
	exist _ Natural_u Natural_lem. 
Definition Plus_lem: (Modifier_wf Plus_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Plus: Modifier := 
	exist _ Plus_u Plus_lem. 
#[global] Hint Resolve Modifier_wf_ref : wf_constr_db.
#[global] Hint Unfold Modifier_wf : wf_constr_db.
#[global] Hint Resolve Modifier_eq : ref_constr_db.
#[global] Hint Unfold Minus : ref_constr_db.
#[global] Hint Unfold Natural : ref_constr_db.
#[global] Hint Unfold Plus : ref_constr_db.
Inductive Letter_u : Type := 
	 | A_u: Letter_u
	 | B_u: Letter_u
	 | C_u: Letter_u
	 | D_u: Letter_u
	 | F_u: Letter_u. 
Fixpoint Letter_eq (x: Letter_u) (y: Letter_u): bool := 
	match (x, y) with (A_u, A_u) => true | (B_u, B_u) => true | (C_u, C_u) => true | (D_u, D_u) => true | (F_u, F_u) => true | (_, _) => false end. 
Theorem Letter_eq_refl: (forall (x: Letter_u) , is_true (Letter_eq x x)). 
Proof. 
	eq_refl_rec. 
Qed. 
#[global] Hint Resolve Letter_eq_refl : eq_hint_db.
Theorem Letter_eqb_eq: (forall (s: Letter_u) (t: Letter_u) , (is_true (Letter_eq s t)) -> (s = t)). 
Proof. 
	eqb_eq_lem. 
Qed. 
#[global] Hint Resolve Letter_eqb_eq : eq_hint_db.
#[global] Instance leibnitz_eq_Letter : LeibnitzEqB := { 
	equalB' := Letter_eq;
	refl' := Letter_eq_refl;
	eqb_eq' := Letter_eqb_eq
}.
Fixpoint Letter_wf (x: Letter_u): Prop := 
	match x with A_u => True | B_u => True | C_u => True | D_u => True | F_u => True end. 
Theorem Letter_wf_ref [p: Letter_u -> Prop] (tm: {v: Letter_u | (Letter_wf v) /\ (p v)}): Letter_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation Letter := {x: Letter_u | (Letter_wf x) /\ True}. 
Definition A_lem: (Letter_wf A_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition A: Letter := 
	exist _ A_u A_lem. 
Definition B_lem: (Letter_wf B_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition B: Letter := 
	exist _ B_u B_lem. 
Definition C_lem: (Letter_wf C_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition C: Letter := 
	exist _ C_u C_lem. 
Definition D_lem: (Letter_wf D_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition D: Letter := 
	exist _ D_u D_lem. 
Definition F_lem: (Letter_wf F_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition F: Letter := 
	exist _ F_u F_lem. 
#[global] Hint Resolve Letter_wf_ref : wf_constr_db.
#[global] Hint Unfold Letter_wf : wf_constr_db.
#[global] Hint Resolve Letter_eq : ref_constr_db.
#[global] Hint Unfold A : ref_constr_db.
#[global] Hint Unfold B : ref_constr_db.
#[global] Hint Unfold C : ref_constr_db.
#[global] Hint Unfold D : ref_constr_db.
#[global] Hint Unfold F : ref_constr_db.
Definition lower_letter_spec (l: Letter): Type := 
	Letter. 
#[global] Hint Unfold lower_letter_spec : lia_unfold.
Definition lower_letter (l: Letter): lower_letter_spec l. 
Proof. 
	destruct l as [l l_p]. 
	induction l as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ B _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ C _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ D _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ F _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ F _); 
		solver.  
Defined. 
Inductive lower_letter_rel : (Letter_u -> (Letter_u -> Prop)) := 
	 | lower_letter_A: lower_letter_rel A_u B_u
	 | lower_letter_B: lower_letter_rel B_u C_u
	 | lower_letter_C: lower_letter_rel C_u D_u
	 | lower_letter_D: lower_letter_rel D_u F_u
	 | lower_letter_F: lower_letter_rel F_u F_u. 
#[global] Hint Constructors lower_letter_rel : core_hint_db.
#[global] Instance lower_letter_lookup_rel : dictionary rel lower_letter := { 
	lookup' := lower_letter_rel
}.
#[global] Instance lower_letter_getF : getFunc lower_letter_rel := { 
	getF' := lower_letter
}.
Theorem lower_letter_rel_funct [l: Letter_u]: (forall (VV: Letter_u) (VV': Letter_u) (H: lower_letter_rel l VV) (K: lower_letter_rel l VV') , VV = VV'). 
Proof. 
	destruct l as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve lower_letter_rel_funct : f_rel_funct_db.
Theorem lower_letter_A_lem: (lower_letter_rel A_u B_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite lower_letter_A_lem : f_rel_back.
Theorem lower_letter_B_lem: (lower_letter_rel B_u C_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite lower_letter_B_lem : f_rel_back.
Theorem lower_letter_C_lem: (lower_letter_rel C_u D_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite lower_letter_C_lem : f_rel_back.
Theorem lower_letter_D_lem: (lower_letter_rel D_u F_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite lower_letter_D_lem : f_rel_back.
Theorem lower_letter_F_lem: (lower_letter_rel F_u F_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite lower_letter_F_lem : f_rel_back.
Theorem lower_letter_rel_ex (l: Letter_u) (l_p: (Letter_wf l) /\ True): lower_letter_rel l (⌊ lower_letter (exist _ l l_p) -⌋). 
Proof. 
	Opaque lower_letter.
	existence_lemma_pre lower_letter; 
	destruct l as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations]; 
	simpl in *. 
	Transparent lower_letter.
	all: existence_lemma_quicksolve lower_letter; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve lower_letter_rel_ex : rel_ax_db.
#[global] Opaque lower_letter. 
Theorem lower_letter__lower_letter_rel_rw (l: Letter_u) (l_p: (Letter_wf l) /\ True) (VV: Letter_u): ((⌊ lower_letter (exist _ l l_p) -⌋) = VV) <-> (lower_letter_rel l VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite lower_letter__lower_letter_rel_rw : f_rel_funct_db.
#[global] Hint Resolve lower_letter__lower_letter_rel_rw : rel_ax_db.
#[global] Instance lower_letter_lookup_rw : dictionary rwLem lower_letter := { 
	lookup' := lower_letter__lower_letter_rel_rw
}.
Theorem lower_letter__lower_letter_rel (l_r: Letter) (VV: Letter_u): ((⌊ lower_letter l_r -⌋) = VV) <-> (lower_letter_rel (⌊ l_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite lower_letter__lower_letter_rel : f_rel_funct_db.
Theorem lower_letter__lower_letter_rel' (l: Letter_u) (l_r: Letter) (VV: Letter_u): (l = (⌊ l_r -⌋)) -> (((⌊ lower_letter l_r -⌋) = VV) <-> (lower_letter_rel l VV)). 
Proof. 
	intros ->. 
	refine (lower_letter__lower_letter_rel l_r VV). 
Qed. 
#[global] Hint Resolve lower_letter__lower_letter_rel' : f_rel_funct_db.
Theorem lower_letter_rel_mk [l: Letter_u] (l_p: (Letter_wf l) /\ True): {VV: _ | lower_letter_rel l VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (lower_letter_rel l VV)) (lower_letter (exist _ l l_p)) _); 
	rewrite <- lower_letter__lower_letter_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve lower_letter_rel_mk : f_rel_funct_db.
#[global] Instance lower_letterPack : (@Pack (Letter ::RT (fun (l_r: Letter) => nilRT)) (Letter_u ::UT nilUT) (ltac: (mkProjectsArgListTG (Letter ::RT (fun (l_r: Letter) => nilRT)) (Letter_u ::UT nilUT))) Letter_u (fun (x_49471188: (ArgList Letter ::RT (fun (l_r: Letter) => nilRT))) => (fun (v_x_49471188: Letter_u) => (ltac: (flattenP (fun (l_r: Letter) => (fun (VV: Letter_u) => ((Letter_wf VV) /\ True))) x_49471188 v_x_49471188))))).
Proof. 
	buildPackG lower_letter lower_letter_rel lower_letter__lower_letter_rel lower_letter_rel_funct. 
Defined.
Definition lower_letter_F_is_F_spec: Type := 
	{{forall (lower_letterres: Letter_u), (lower_letter_rel F_u lower_letterres) -> (lower_letterres = F_u)}}. 
#[global] Hint Unfold lower_letter_F_is_F_spec : lia_unfold.
Theorem lower_letter_F_is_F: lower_letter_F_is_F_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Inductive Grades_u : Type := 
	 | Grade_u: Letter_u -> (Modifier_u -> Grades_u). 
Fixpoint Grades_eq (x: Grades_u) (y: Grades_u): bool := 
	match (x, y) with (Grade_u x x_1, Grade_u x' x_1') => ((true && (x ==? x')) && (x_1 ==? x_1')) end. 
Theorem Grades_eq_refl: (forall (x: Grades_u) , is_true (Grades_eq x x)). 
Proof. 
	eq_refl_rec. 
Qed. 
#[global] Hint Resolve Grades_eq_refl : eq_hint_db.
Theorem Grades_eqb_eq: (forall (s: Grades_u) (t: Grades_u) , (is_true (Grades_eq s t)) -> (s = t)). 
Proof. 
	eqb_eq_lem. 
Qed. 
#[global] Hint Resolve Grades_eqb_eq : eq_hint_db.
#[global] Instance leibnitz_eq_Grades : LeibnitzEqB := { 
	equalB' := Grades_eq;
	refl' := Grades_eq_refl;
	eqb_eq' := Grades_eqb_eq
}.
Fixpoint Grades_wf (x: Grades_u): Prop := 
	match x with (Grade_u VV VV_) => (((Letter_wf VV) /\ True) /\ ((Modifier_wf VV_) /\ True)) end. 
Theorem Grades_wf_ref [p: Grades_u -> Prop] (tm: {v: Grades_u | (Grades_wf v) /\ (p v)}): Grades_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation Grades := {x: Grades_u | (Grades_wf x) /\ True}. 
Definition Grade_lem (VV: Letter) (VV_: Modifier): (Grades_wf (Grade_u (⌊ VV -⌋) (⌊ VV_ -⌋))) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Grade (VV: Letter) (VV_: Modifier): Grades := 
	exist _ (Grade_u (⌊ VV -⌋) (⌊ VV_ -⌋)) (Grade_lem VV VV_). 
#[global] Hint Resolve Grades_wf_ref : wf_constr_db.
#[global] Hint Unfold Grades_wf : wf_constr_db.
#[global] Hint Resolve Grades_eq : ref_constr_db.
#[global] Hint Unfold Grade : ref_constr_db.
Definition lower_grade_spec (g: Grades): Type := 
	Grades. 
#[global] Hint Unfold lower_grade_spec : lia_unfold.
Definition lower_grade (g: Grades): lower_grade_spec g. 
Proof. 
	destruct g as [g g_p]. 
	induction g as [(*Grade*) l m]. 
	  - intros . 
		induction m as [(*Minus*)  | (*Natural*)  | (*Plus*) ]. 
		  -- intros . 
			induction l as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]. 
			  --- intros . 
				refine (subsumptionCast _ _ 
		(Grade 
		(lower_letter 
		(subsumptionCast Letter_u (fun (l: Letter_u) => ((Letter_wf l) /\ True)) A (ltac: (solver)))) 
		(subsumptionCast Modifier_u (fun (VV: Modifier_u) => ((Modifier_wf VV) /\ True)) Plus (ltac: (solver)))) _); 
				solver.  
			  --- intros . 
				refine (subsumptionCast _ _ 
		(Grade 
		(lower_letter 
		(subsumptionCast Letter_u (fun (l: Letter_u) => ((Letter_wf l) /\ True)) B (ltac: (solver)))) 
		(subsumptionCast Modifier_u (fun (VV: Modifier_u) => ((Modifier_wf VV) /\ True)) Plus (ltac: (solver)))) _); 
				solver.  
			  --- intros . 
				refine (subsumptionCast _ _ 
		(Grade 
		(lower_letter 
		(subsumptionCast Letter_u (fun (l: Letter_u) => ((Letter_wf l) /\ True)) C (ltac: (solver)))) 
		(subsumptionCast Modifier_u (fun (VV: Modifier_u) => ((Modifier_wf VV) /\ True)) Plus (ltac: (solver)))) _); 
				solver.  
			  --- intros . 
				refine (subsumptionCast _ _ 
		(Grade 
		(lower_letter 
		(subsumptionCast Letter_u (fun (l: Letter_u) => ((Letter_wf l) /\ True)) D (ltac: (solver)))) 
		(subsumptionCast Modifier_u (fun (VV: Modifier_u) => ((Modifier_wf VV) /\ True)) Plus (ltac: (solver)))) _); 
				solver.  
			  --- intros . 
				refine (subsumptionCast _ _ (Grade F Minus) _); 
				solver.   
		  -- intros . 
			refine (subsumptionCast _ _ 
		(Grade 
		(exist (fun (VV: Letter_u) => ((Letter_wf VV) /\ True)) l (ltac: (solver))) 
		(subsumptionCast Modifier_u (fun (VV: Modifier_u) => ((Modifier_wf VV) /\ True)) Minus (ltac: (solver)))) _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ 
		(Grade 
		(exist (fun (VV: Letter_u) => ((Letter_wf VV) /\ True)) l (ltac: (solver))) 
		(subsumptionCast Modifier_u (fun (VV: Modifier_u) => ((Modifier_wf VV) /\ True)) Natural (ltac: (solver)))) _); 
			solver.   
Defined. 
Inductive lower_grade_rel : (Grades_u -> (Grades_u -> Prop)) := 
	 | lower_grade_Grade: (forall l , lower_grade_rel (Grade_u l Plus_u) (Grade_u l Natural_u))
	 | lower_grade_Grade_: (forall l , lower_grade_rel (Grade_u l Natural_u) (Grade_u l Minus_u))
	 | lower_grade_Grade__: forall (lower_letterres: Letter_u), (lower_letter_rel A_u lower_letterres) -> (lower_grade_rel (Grade_u A_u Minus_u) (Grade_u lower_letterres Plus_u))
	 | lower_grade_Grade___: forall (lower_letterres: Letter_u), (lower_letter_rel B_u lower_letterres) -> (lower_grade_rel (Grade_u B_u Minus_u) (Grade_u lower_letterres Plus_u))
	 | lower_grade_Grade____: forall (lower_letterres: Letter_u), (lower_letter_rel C_u lower_letterres) -> (lower_grade_rel (Grade_u C_u Minus_u) (Grade_u lower_letterres Plus_u))
	 | lower_grade_Grade_____: forall (lower_letterres: Letter_u), (lower_letter_rel D_u lower_letterres) -> (lower_grade_rel (Grade_u D_u Minus_u) (Grade_u lower_letterres Plus_u))
	 | lower_grade_Grade______: lower_grade_rel (Grade_u F_u Minus_u) (Grade_u F_u Minus_u). 
#[global] Hint Constructors lower_grade_rel : core_hint_db.
#[global] Instance lower_grade_lookup_rel : dictionary rel lower_grade := { 
	lookup' := lower_grade_rel
}.
#[global] Instance lower_grade_getF : getFunc lower_grade_rel := { 
	getF' := lower_grade
}.
Theorem lower_grade_rel_funct [g: Grades_u]: (forall (VV: Grades_u) (VV': Grades_u) (H: lower_grade_rel g VV) (K: lower_grade_rel g VV') , VV = VV'). 
Proof. 
	induction g as [(*Grade*) l m]; 
	intros ; 
	[destruct m as [(*Minus*)  | (*Natural*)  | (*Plus*) ]; 
	intros ; 
	[destruct l as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros | 
	| 
	]]; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve lower_grade_rel_funct : f_rel_funct_db.
Theorem lower_grade_Grade_lem (l: _): (lower_grade_rel (Grade_u l Plus_u) (Grade_u l Natural_u)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite lower_grade_Grade_lem : f_rel_back.
Theorem lower_grade_Grade__lem (l: _): (lower_grade_rel (Grade_u l Natural_u) (Grade_u l Minus_u)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite lower_grade_Grade__lem : f_rel_back.
Theorem lower_grade_Grade___lem (lower_letterres: Letter_u) (h_86531359: lower_letter_rel A_u lower_letterres): (lower_grade_rel (Grade_u A_u Minus_u) (Grade_u lower_letterres Plus_u)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite lower_grade_Grade___lem : f_rel_back.
Theorem lower_grade_Grade____lem (lower_letterres: Letter_u) (h_84928990: lower_letter_rel B_u lower_letterres): (lower_grade_rel (Grade_u B_u Minus_u) (Grade_u lower_letterres Plus_u)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite lower_grade_Grade____lem : f_rel_back.
Theorem lower_grade_Grade_____lem (lower_letterres: Letter_u) (h_61781460: lower_letter_rel C_u lower_letterres): (lower_grade_rel (Grade_u C_u Minus_u) (Grade_u lower_letterres Plus_u)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite lower_grade_Grade_____lem : f_rel_back.
Theorem lower_grade_Grade______lem (lower_letterres: Letter_u) (h_71379125: lower_letter_rel D_u lower_letterres): (lower_grade_rel (Grade_u D_u Minus_u) (Grade_u lower_letterres Plus_u)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite lower_grade_Grade______lem : f_rel_back.
Theorem lower_grade_Grade_______lem: (lower_grade_rel (Grade_u F_u Minus_u) (Grade_u F_u Minus_u)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite lower_grade_Grade_______lem : f_rel_back.
Theorem lower_grade_rel_ex (g: Grades_u) (g_p: (Grades_wf g) /\ True): lower_grade_rel g (⌊ lower_grade (exist _ g g_p) -⌋). 
Proof. 
	Opaque lower_grade.
	existence_lemma_pre lower_grade; 
	induction g as [(*Grade*) l m]; 
	intros ; 
	[destruct m as [(*Minus*)  | (*Natural*)  | (*Plus*) ]; 
	intros ; 
	[destruct l as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations]| 
	fix_notations| 
	fix_notations]]; 
	simpl in *. 
	Transparent lower_grade.
	all: existence_lemma_quicksolve lower_grade; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve lower_grade_rel_ex : rel_ax_db.
#[global] Opaque lower_grade. 
Theorem lower_grade__lower_grade_rel_rw (g: Grades_u) (g_p: (Grades_wf g) /\ True) (VV: Grades_u): ((⌊ lower_grade (exist _ g g_p) -⌋) = VV) <-> (lower_grade_rel g VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite lower_grade__lower_grade_rel_rw : f_rel_funct_db.
#[global] Hint Resolve lower_grade__lower_grade_rel_rw : rel_ax_db.
#[global] Instance lower_grade_lookup_rw : dictionary rwLem lower_grade := { 
	lookup' := lower_grade__lower_grade_rel_rw
}.
Theorem lower_grade__lower_grade_rel (g_r: Grades) (VV: Grades_u): ((⌊ lower_grade g_r -⌋) = VV) <-> (lower_grade_rel (⌊ g_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite lower_grade__lower_grade_rel : f_rel_funct_db.
Theorem lower_grade__lower_grade_rel' (g: Grades_u) (g_r: Grades) (VV: Grades_u): (g = (⌊ g_r -⌋)) -> (((⌊ lower_grade g_r -⌋) = VV) <-> (lower_grade_rel g VV)). 
Proof. 
	intros ->. 
	refine (lower_grade__lower_grade_rel g_r VV). 
Qed. 
#[global] Hint Resolve lower_grade__lower_grade_rel' : f_rel_funct_db.
Theorem lower_grade_rel_mk [g: Grades_u] (g_p: (Grades_wf g) /\ True): {VV: _ | lower_grade_rel g VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (lower_grade_rel g VV)) (lower_grade (exist _ g g_p)) _); 
	rewrite <- lower_grade__lower_grade_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve lower_grade_rel_mk : f_rel_funct_db.
#[global] Instance lower_gradePack : (@Pack (Grades ::RT (fun (g_r: Grades) => nilRT)) (Grades_u ::UT nilUT) (ltac: (mkProjectsArgListTG (Grades ::RT (fun (g_r: Grades) => nilRT)) (Grades_u ::UT nilUT))) Grades_u (fun (x_69925386: (ArgList Grades ::RT (fun (g_r: Grades) => nilRT))) => (fun (v_x_69925386: Grades_u) => (ltac: (flattenP (fun (g_r: Grades) => (fun (VV: Grades_u) => ((Grades_wf VV) /\ True))) x_69925386 v_x_69925386))))).
Proof. 
	buildPackG lower_grade lower_grade_rel lower_grade__lower_grade_rel lower_grade_rel_funct. 
Defined.
Definition apply_late_policy_spec (late_days: {late_days: Z | True}) (g: Grades): Type := 
	Grades. 
#[global] Hint Unfold apply_late_policy_spec : lia_unfold.
Definition apply_late_policy (late_days: {late_days: Z | True}) (g: Grades): apply_late_policy_spec late_days g. 
Proof. 
	destruct late_days as [late_days late_days_p]. 
	destruct g as [g g_p]. 
	let E := fresh "E" in 
	destruct (late_days <? 9) as [ | ] eqn:E; [refine (exist _ g _); 
	solver | let E := fresh "E" in 
	destruct (late_days <? 17) as [ | ] eqn:E; [refine (subsumptionCast _ _ 
		(lower_grade 
		(exist (fun (g: Grades_u) => ((Grades_wf g) /\ True)) g (ltac: (solver)))) _); 
	solver | let E := fresh "E" in 
	destruct (late_days <? 21) as [ | ] eqn:E; [refine (subsumptionCast _ _ 
		(lower_grade 
		(subsumptionCast Grades_u (fun (g: Grades_u) => ((Grades_wf g) /\ True)) 
		(lower_grade 
		(exist (fun (g: Grades_u) => ((Grades_wf g) /\ True)) g (ltac: (solver)))) (ltac: (solver)))) _); 
	solver | refine (subsumptionCast _ _ 
		(lower_grade 
		(subsumptionCast Grades_u (fun (g: Grades_u) => ((Grades_wf g) /\ True)) 
		(lower_grade 
		(subsumptionCast Grades_u (fun (g: Grades_u) => ((Grades_wf g) /\ True)) 
		(lower_grade 
		(exist (fun (g: Grades_u) => ((Grades_wf g) /\ True)) g (ltac: (solver)))) (ltac: (solver)))) (ltac: (solver)))) _); 
	solver]]]. 
Defined. 
Inductive apply_late_policy_rel : (Z -> (Grades_u -> (Grades_u -> Prop))) := 
	 | apply_late_policy_false_false_false: (forall g late_days , (ltbZ_rel late_days 9 false) -> ((ltbZ_rel late_days 17 false) -> ((ltbZ_rel late_days 21 false) -> (forall (lower_graderes: Grades_u), (lower_grade_rel g lower_graderes) -> (forall (lower_grade_res_2: Grades_u), (lower_grade_rel lower_graderes lower_grade_res_2) -> (forall (lower_grade_res_3: Grades_u), (lower_grade_rel lower_grade_res_2 lower_grade_res_3) -> (apply_late_policy_rel late_days g lower_grade_res_3)))))))
	 | apply_late_policy_false_false_true: (forall g late_days , (ltbZ_rel late_days 9 false) -> ((ltbZ_rel late_days 17 false) -> ((ltbZ_rel late_days 21 true) -> (forall (lower_graderes: Grades_u), (lower_grade_rel g lower_graderes) -> (forall (lower_grade_res_2: Grades_u), (lower_grade_rel lower_graderes lower_grade_res_2) -> (apply_late_policy_rel late_days g lower_grade_res_2))))))
	 | apply_late_policy_false_true: (forall g late_days , (ltbZ_rel late_days 9 false) -> ((ltbZ_rel late_days 17 true) -> (forall (lower_graderes: Grades_u), (lower_grade_rel g lower_graderes) -> (apply_late_policy_rel late_days g lower_graderes))))
	 | apply_late_policy_true: (forall g late_days , (ltbZ_rel late_days 9 true) -> (apply_late_policy_rel late_days g g)). 
#[global] Hint Constructors apply_late_policy_rel : core_hint_db.
#[global] Instance apply_late_policy_lookup_rel : dictionary rel apply_late_policy := { 
	lookup' := apply_late_policy_rel
}.
#[global] Instance apply_late_policy_getF : getFunc apply_late_policy_rel := { 
	getF' := apply_late_policy
}.
Theorem apply_late_policy_rel_funct [late_days: Z] [g: Grades_u]: (forall (VV: Grades_u) (VV': Grades_u) (H: apply_late_policy_rel late_days g VV) (K: apply_late_policy_rel late_days g VV') , VV = VV'). 
Proof. 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve apply_late_policy_rel_funct : f_rel_funct_db.
Theorem apply_late_policy_false_false_false_late_policy_false_false_true_late_policy_false_true_late_policy_true_lem (late_days: _) (g: _) (x_3: _): (apply_late_policy_rel late_days g x_3) <-> (((((((ltbZ_rel late_days 9 false) /\ (ltbZ_rel late_days 17 false)) /\ (ltbZ_rel late_days 21 false)) /\ (exists (lower_graderes: Grades_u), (lower_grade_rel g lower_graderes) /\ (exists (lower_grade_res_2: Grades_u), (lower_grade_rel lower_graderes lower_grade_res_2) /\ (exists (lower_grade_res_3: Grades_u), (lower_grade_rel lower_grade_res_2 x_3) /\ (x_3 = lower_grade_res_3))))) \/ ((((ltbZ_rel late_days 9 false) /\ (ltbZ_rel late_days 17 false)) /\ (ltbZ_rel late_days 21 true)) /\ (exists (lower_graderes: Grades_u), (lower_grade_rel g lower_graderes) /\ (exists (lower_grade_res_2: Grades_u), (lower_grade_rel lower_graderes x_3) /\ (x_3 = lower_grade_res_2))))) \/ (((ltbZ_rel late_days 9 false) /\ (ltbZ_rel late_days 17 true)) /\ (exists (lower_graderes: Grades_u), (lower_grade_rel g x_3) /\ (x_3 = lower_graderes)))) \/ ((ltbZ_rel late_days 9 true) /\ (x_3 = g))). 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite apply_late_policy_false_false_false_late_policy_false_false_true_late_policy_false_true_late_policy_true_lem : f_rel_back.
Theorem apply_late_policy_rel_ex (late_days: Z) (g: Grades_u) (late_days_p: True) (g_p: (Grades_wf g) /\ True): apply_late_policy_rel late_days g 
		(⌊ apply_late_policy (exist _ late_days late_days_p) (exist _ g g_p) -⌋). 
Proof. 
	Opaque apply_late_policy.
	existence_lemma_pre apply_late_policy; 
	let E := fresh "E" in 
	destruct (late_days <? 9) as [ | ] eqn:E; [fix_notations | let E := fresh "E" in 
	destruct (late_days <? 17) as [ | ] eqn:E; [fix_notations | let E := fresh "E" in 
	destruct (late_days <? 21) as [ | ] eqn:E; [fix_notations | fix_notations]]]; 
	simpl in *. 
	Transparent apply_late_policy.
	all: existence_lemma_quicksolve apply_late_policy; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve apply_late_policy_rel_ex : rel_ax_db.
#[global] Opaque apply_late_policy. 
Theorem apply_late_policy__apply_late_policy_rel_rw (late_days: Z) (g: Grades_u) (late_days_p: True) (g_p: (Grades_wf g) /\ True) (VV: Grades_u): ((⌊ apply_late_policy (exist _ late_days late_days_p) (exist _ g g_p) -⌋) = VV) <-> (apply_late_policy_rel late_days g VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite apply_late_policy__apply_late_policy_rel_rw : f_rel_funct_db.
#[global] Hint Resolve apply_late_policy__apply_late_policy_rel_rw : rel_ax_db.
#[global] Instance apply_late_policy_lookup_rw : dictionary rwLem apply_late_policy := { 
	lookup' := apply_late_policy__apply_late_policy_rel_rw
}.
Theorem apply_late_policy__apply_late_policy_rel (late_days_r: {late_days: Z | True}) (g_r: Grades) (VV: Grades_u): ((⌊ apply_late_policy late_days_r g_r -⌋) = VV) <-> (apply_late_policy_rel (⌊ late_days_r -⌋) (⌊ g_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite apply_late_policy__apply_late_policy_rel : f_rel_funct_db.
Theorem apply_late_policy__apply_late_policy_rel' (late_days: Z) (g: Grades_u) (late_days_r: {late_days: Z | True}) (g_r: Grades) (VV: Grades_u): (late_days = (⌊ late_days_r -⌋)) -> ((g = (⌊ g_r -⌋)) -> (((⌊ apply_late_policy late_days_r g_r -⌋) = VV) <-> (apply_late_policy_rel late_days g VV))). 
Proof. 
	intros -> ->. 
	refine (apply_late_policy__apply_late_policy_rel late_days_r g_r VV). 
Qed. 
#[global] Hint Resolve apply_late_policy__apply_late_policy_rel' : f_rel_funct_db.
Theorem apply_late_policy_rel_mk [late_days: Z] [g: Grades_u] (late_days_p: True) (g_p: (Grades_wf g) /\ True): {VV: _ | apply_late_policy_rel late_days g VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (apply_late_policy_rel late_days g VV)) 
		(apply_late_policy (exist _ late_days late_days_p) (exist _ g g_p)) _); 
	rewrite <- apply_late_policy__apply_late_policy_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve apply_late_policy_rel_mk : f_rel_funct_db.
#[global] Instance apply_late_policyPack : (@Pack ({late_days: Z | True} ::RT (fun (late_days_r: {late_days: Z | True}) => (Grades ::RT (fun (g_r: Grades) => nilRT)))) (Z ::UT (Grades_u ::UT nilUT)) (ltac: (mkProjectsArgListTG ({late_days: Z | True} ::RT (fun (late_days_r: {late_days: Z | True}) => (Grades ::RT (fun (g_r: Grades) => nilRT)))) (Z ::UT (Grades_u ::UT nilUT)))) Grades_u (fun (x_27090246: (ArgList {late_days: Z | True} ::RT (fun (late_days_r: {late_days: Z | True}) => (Grades ::RT (fun (g_r: Grades) => nilRT))))) => (fun (v_x_27090246: Grades_u) => (ltac: (flattenP (fun (late_days_r: {late_days: Z | True}) => (fun (g_r: Grades) => (fun (VV: Grades_u) => ((Grades_wf VV) /\ True)))) x_27090246 v_x_27090246))))).
Proof. 
	buildPackG apply_late_policy apply_late_policy_rel apply_late_policy__apply_late_policy_rel apply_late_policy_rel_funct. 
Defined.
Definition lower_grade_F_Minus_spec: Type := 
	{{forall (lower_graderes: Grades_u), (lower_grade_rel (Grade_u F_u Minus_u) lower_graderes) -> (lower_graderes == (Grade_u F_u Minus_u))}}. 
#[global] Hint Unfold lower_grade_F_Minus_spec : lia_unfold.
Theorem lower_grade_F_Minus: lower_grade_F_Minus_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition lower_grade_thrice_spec: Type := 
	{{forall (lower_graderes: Grades_u), (lower_grade_rel (Grade_u B_u Minus_u) lower_graderes) -> (forall (lower_grade_res_2: Grades_u), (lower_grade_rel lower_graderes lower_grade_res_2) -> (forall (lower_grade_res_3: Grades_u), (lower_grade_rel lower_grade_res_2 lower_grade_res_3) -> (lower_grade_res_3 == (Grade_u C_u Minus_u))))}}. 
#[global] Hint Unfold lower_grade_thrice_spec : lia_unfold.
Theorem lower_grade_thrice: lower_grade_thrice_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition lower_grade_twice_spec: Type := 
	{{forall (lower_graderes: Grades_u), (lower_grade_rel (Grade_u B_u Minus_u) lower_graderes) -> (forall (lower_grade_res_2: Grades_u), (lower_grade_rel lower_graderes lower_grade_res_2) -> (lower_grade_res_2 == (Grade_u C_u Natural_u)))}}. 
#[global] Hint Unfold lower_grade_twice_spec : lia_unfold.
Theorem lower_grade_twice: lower_grade_twice_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition no_penalty_for_mostly_on_time_spec (late_days: {late_days: Z | True}) (g: Grades) (h: {{ltbZ_rel (⌊ late_days -⌋) 9 true}}): Type := 
	{{forall (apply_late_policyres: Grades_u), (apply_late_policy_rel (⌊ late_days -⌋) (⌊ g -⌋) apply_late_policyres) -> (apply_late_policyres = (⌊ g -⌋))}}. 
#[global] Hint Unfold no_penalty_for_mostly_on_time_spec : lia_unfold.
Theorem no_penalty_for_mostly_on_time (late_days: {late_days: Z | True}) (g: Grades) (h: {{ltbZ_rel (⌊ late_days -⌋) 9 true}}): no_penalty_for_mostly_on_time_spec late_days g h. 
Proof. 
	destruct late_days as [late_days late_days_p]. 
	destruct g as [g g_p]. 
	destruct h as [h h_p]. 
	let E := fresh "E" in 
	destruct (late_days <? 9) as [ | ] eqn:E; [refine (exist _ unit _); 
	solver | refine (exist _ h _); 
	solver]. 
Qed. 
Inductive Day_u : Type := 
	 | Friday_u: Day_u
	 | Monday_u: Day_u
	 | Saturday_u: Day_u
	 | Sunday_u: Day_u
	 | Thursday_u: Day_u
	 | Tuesday_u: Day_u
	 | Wednesday_u: Day_u. 
Fixpoint Day_eq (x: Day_u) (y: Day_u): bool := 
	match (x, y) with (Friday_u, Friday_u) => true | (Monday_u, Monday_u) => true | (Saturday_u, Saturday_u) => true | (Sunday_u, Sunday_u) => true | (Thursday_u, Thursday_u) => true | (Tuesday_u, Tuesday_u) => true | (Wednesday_u, Wednesday_u) => true | (_, _) => false end. 
Theorem Day_eq_refl: (forall (x: Day_u) , is_true (Day_eq x x)). 
Proof. 
	eq_refl_rec. 
Qed. 
#[global] Hint Resolve Day_eq_refl : eq_hint_db.
Theorem Day_eqb_eq: (forall (s: Day_u) (t: Day_u) , (is_true (Day_eq s t)) -> (s = t)). 
Proof. 
	eqb_eq_lem. 
Qed. 
#[global] Hint Resolve Day_eqb_eq : eq_hint_db.
#[global] Instance leibnitz_eq_Day : LeibnitzEqB := { 
	equalB' := Day_eq;
	refl' := Day_eq_refl;
	eqb_eq' := Day_eqb_eq
}.
Fixpoint Day_wf (x: Day_u): Prop := 
	match x with Friday_u => True | Monday_u => True | Saturday_u => True | Sunday_u => True | Thursday_u => True | Tuesday_u => True | Wednesday_u => True end. 
Theorem Day_wf_ref [p: Day_u -> Prop] (tm: {v: Day_u | (Day_wf v) /\ (p v)}): Day_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation Day := {x: Day_u | (Day_wf x) /\ True}. 
Definition Friday_lem: (Day_wf Friday_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Friday: Day := 
	exist _ Friday_u Friday_lem. 
Definition Monday_lem: (Day_wf Monday_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Monday: Day := 
	exist _ Monday_u Monday_lem. 
Definition Saturday_lem: (Day_wf Saturday_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Saturday: Day := 
	exist _ Saturday_u Saturday_lem. 
Definition Sunday_lem: (Day_wf Sunday_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Sunday: Day := 
	exist _ Sunday_u Sunday_lem. 
Definition Thursday_lem: (Day_wf Thursday_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Thursday: Day := 
	exist _ Thursday_u Thursday_lem. 
Definition Tuesday_lem: (Day_wf Tuesday_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Tuesday: Day := 
	exist _ Tuesday_u Tuesday_lem. 
Definition Wednesday_lem: (Day_wf Wednesday_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Wednesday: Day := 
	exist _ Wednesday_u Wednesday_lem. 
#[global] Hint Resolve Day_wf_ref : wf_constr_db.
#[global] Hint Unfold Day_wf : wf_constr_db.
#[global] Hint Resolve Day_eq : ref_constr_db.
#[global] Hint Unfold Friday : ref_constr_db.
#[global] Hint Unfold Monday : ref_constr_db.
#[global] Hint Unfold Saturday : ref_constr_db.
#[global] Hint Unfold Sunday : ref_constr_db.
#[global] Hint Unfold Thursday : ref_constr_db.
#[global] Hint Unfold Tuesday : ref_constr_db.
#[global] Hint Unfold Wednesday : ref_constr_db.
Definition next_weekday_spec (d: Day): Type := 
	Day. 
#[global] Hint Unfold next_weekday_spec : lia_unfold.
Definition next_weekday (d: Day): next_weekday_spec d. 
Proof. 
	destruct d as [d d_p]. 
	induction d as [(*Friday*)  | (*Monday*)  | (*Saturday*)  | (*Sunday*)  | (*Thursday*)  | (*Tuesday*)  | (*Wednesday*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ Monday _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ Tuesday _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ Monday _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ Monday _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ Friday _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ Wednesday _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ Thursday _); 
		solver.  
Defined. 
Inductive next_weekday_rel : (Day_u -> (Day_u -> Prop)) := 
	 | next_weekday_Monday: next_weekday_rel Monday_u Tuesday_u
	 | next_weekday_Tuesday: next_weekday_rel Tuesday_u Wednesday_u
	 | next_weekday_Wednesday: next_weekday_rel Wednesday_u Thursday_u
	 | next_weekday_Thursday: next_weekday_rel Thursday_u Friday_u
	 | next_weekday_Friday: next_weekday_rel Friday_u Monday_u
	 | next_weekday_Saturday: next_weekday_rel Saturday_u Monday_u
	 | next_weekday_Sunday: next_weekday_rel Sunday_u Monday_u. 
#[global] Hint Constructors next_weekday_rel : core_hint_db.
#[global] Instance next_weekday_lookup_rel : dictionary rel next_weekday := { 
	lookup' := next_weekday_rel
}.
#[global] Instance next_weekday_getF : getFunc next_weekday_rel := { 
	getF' := next_weekday
}.
Theorem next_weekday_rel_funct [d: Day_u]: (forall (VV: Day_u) (VV': Day_u) (H: next_weekday_rel d VV) (K: next_weekday_rel d VV') , VV = VV'). 
Proof. 
	destruct d as [(*Friday*)  | (*Monday*)  | (*Saturday*)  | (*Sunday*)  | (*Thursday*)  | (*Tuesday*)  | (*Wednesday*) ]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve next_weekday_rel_funct : f_rel_funct_db.
Theorem next_weekday_Monday_lem: (next_weekday_rel Monday_u Tuesday_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite next_weekday_Monday_lem : f_rel_back.
Theorem next_weekday_Tuesday_lem: (next_weekday_rel Tuesday_u Wednesday_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite next_weekday_Tuesday_lem : f_rel_back.
Theorem next_weekday_Wednesday_lem: (next_weekday_rel Wednesday_u Thursday_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite next_weekday_Wednesday_lem : f_rel_back.
Theorem next_weekday_Thursday_lem: (next_weekday_rel Thursday_u Friday_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite next_weekday_Thursday_lem : f_rel_back.
Theorem next_weekday_Friday_lem: (next_weekday_rel Friday_u Monday_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite next_weekday_Friday_lem : f_rel_back.
Theorem next_weekday_Saturday_lem: (next_weekday_rel Saturday_u Monday_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite next_weekday_Saturday_lem : f_rel_back.
Theorem next_weekday_Sunday_lem: (next_weekday_rel Sunday_u Monday_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite next_weekday_Sunday_lem : f_rel_back.
Theorem next_weekday_rel_ex (d: Day_u) (d_p: (Day_wf d) /\ True): next_weekday_rel d (⌊ next_weekday (exist _ d d_p) -⌋). 
Proof. 
	Opaque next_weekday.
	existence_lemma_pre next_weekday; 
	destruct d as [(*Friday*)  | (*Monday*)  | (*Saturday*)  | (*Sunday*)  | (*Thursday*)  | (*Tuesday*)  | (*Wednesday*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations]; 
	simpl in *. 
	Transparent next_weekday.
	all: existence_lemma_quicksolve next_weekday; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve next_weekday_rel_ex : rel_ax_db.
#[global] Opaque next_weekday. 
Theorem next_weekday__next_weekday_rel_rw (d: Day_u) (d_p: (Day_wf d) /\ True) (VV: Day_u): ((⌊ next_weekday (exist _ d d_p) -⌋) = VV) <-> (next_weekday_rel d VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite next_weekday__next_weekday_rel_rw : f_rel_funct_db.
#[global] Hint Resolve next_weekday__next_weekday_rel_rw : rel_ax_db.
#[global] Instance next_weekday_lookup_rw : dictionary rwLem next_weekday := { 
	lookup' := next_weekday__next_weekday_rel_rw
}.
Theorem next_weekday__next_weekday_rel (d_r: Day) (VV: Day_u): ((⌊ next_weekday d_r -⌋) = VV) <-> (next_weekday_rel (⌊ d_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite next_weekday__next_weekday_rel : f_rel_funct_db.
Theorem next_weekday__next_weekday_rel' (d: Day_u) (d_r: Day) (VV: Day_u): (d = (⌊ d_r -⌋)) -> (((⌊ next_weekday d_r -⌋) = VV) <-> (next_weekday_rel d VV)). 
Proof. 
	intros ->. 
	refine (next_weekday__next_weekday_rel d_r VV). 
Qed. 
#[global] Hint Resolve next_weekday__next_weekday_rel' : f_rel_funct_db.
Theorem next_weekday_rel_mk [d: Day_u] (d_p: (Day_wf d) /\ True): {VV: _ | next_weekday_rel d VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (next_weekday_rel d VV)) (next_weekday (exist _ d d_p)) _); 
	rewrite <- next_weekday__next_weekday_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve next_weekday_rel_mk : f_rel_funct_db.
#[global] Instance next_weekdayPack : (@Pack (Day ::RT (fun (d_r: Day) => nilRT)) (Day_u ::UT nilUT) (ltac: (mkProjectsArgListTG (Day ::RT (fun (d_r: Day) => nilRT)) (Day_u ::UT nilUT))) Day_u (fun (x_61116501: (ArgList Day ::RT (fun (d_r: Day) => nilRT))) => (fun (v_x_61116501: Day_u) => (ltac: (flattenP (fun (d_r: Day) => (fun (VV: Day_u) => ((Day_wf VV) /\ True))) x_61116501 v_x_61116501))))).
Proof. 
	buildPackG next_weekday next_weekday_rel next_weekday__next_weekday_rel next_weekday_rel_funct. 
Defined.
Definition test_next_weekday_spec: Type := 
	{{forall (next_weekdayres: Day_u), (next_weekday_rel Saturday_u next_weekdayres) -> (forall (next_weekday_res_2: Day_u), (next_weekday_rel next_weekdayres next_weekday_res_2) -> (next_weekday_res_2 = Tuesday_u))}}. 
#[global] Hint Unfold test_next_weekday_spec : lia_unfold.
Theorem test_next_weekday: test_next_weekday_spec. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Inductive Comparison_u : Type := 
	 | Eq_u: Comparison_u
	 | Gt_u: Comparison_u
	 | Lt_u: Comparison_u. 
Fixpoint Comparison_eq (x: Comparison_u) (y: Comparison_u): bool := 
	match (x, y) with (Eq_u, Eq_u) => true | (Gt_u, Gt_u) => true | (Lt_u, Lt_u) => true | (_, _) => false end. 
Theorem Comparison_eq_refl: (forall (x: Comparison_u) , is_true (Comparison_eq x x)). 
Proof. 
	eq_refl_rec. 
Qed. 
#[global] Hint Resolve Comparison_eq_refl : eq_hint_db.
Theorem Comparison_eqb_eq: (forall (s: Comparison_u) (t: Comparison_u) , (is_true (Comparison_eq s t)) -> (s = t)). 
Proof. 
	eqb_eq_lem. 
Qed. 
#[global] Hint Resolve Comparison_eqb_eq : eq_hint_db.
#[global] Instance leibnitz_eq_Comparison : LeibnitzEqB := { 
	equalB' := Comparison_eq;
	refl' := Comparison_eq_refl;
	eqb_eq' := Comparison_eqb_eq
}.
Fixpoint Comparison_wf (x: Comparison_u): Prop := 
	match x with Eq_u => True | Gt_u => True | Lt_u => True end. 
Theorem Comparison_wf_ref [p: Comparison_u -> Prop] (tm: {v: Comparison_u | (Comparison_wf v) /\ (p v)}): Comparison_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation Comparison := {x: Comparison_u | (Comparison_wf x) /\ True}. 
Definition Eq_lem: (Comparison_wf Eq_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Eq: Comparison := 
	exist _ Eq_u Eq_lem. 
Definition Gt_lem: (Comparison_wf Gt_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Gt: Comparison := 
	exist _ Gt_u Gt_lem. 
Definition Lt_lem: (Comparison_wf Lt_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Lt: Comparison := 
	exist _ Lt_u Lt_lem. 
#[global] Hint Resolve Comparison_wf_ref : wf_constr_db.
#[global] Hint Unfold Comparison_wf : wf_constr_db.
#[global] Hint Resolve Comparison_eq : ref_constr_db.
#[global] Hint Unfold Eq : ref_constr_db.
#[global] Hint Unfold Gt : ref_constr_db.
#[global] Hint Unfold Lt : ref_constr_db.
Definition letter_comparison_spec (l1: Letter) (l2: Letter): Type := 
	Comparison. 
#[global] Hint Unfold letter_comparison_spec : lia_unfold.
Definition letter_comparison (l1: Letter) (l2: Letter): letter_comparison_spec l1 l2. 
Proof. 
	destruct l1 as [l1 l1_p]. 
	destruct l2 as [l2 l2_p]. 
	try revert l2_p; generalize dependent l2; 
	induction l1 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]. 
	  - intros . 
		induction l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]. 
		  -- intros . 
			refine (subsumptionCast _ _ Eq _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Gt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Gt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Gt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Gt _); 
			solver.   
	  - intros . 
		induction l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]. 
		  -- intros . 
			refine (subsumptionCast _ _ Lt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Eq _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Gt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Gt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Gt _); 
			solver.   
	  - intros . 
		induction l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]. 
		  -- intros . 
			refine (subsumptionCast _ _ Lt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Lt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Eq _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Gt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Gt _); 
			solver.   
	  - intros . 
		induction l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]. 
		  -- intros . 
			refine (subsumptionCast _ _ Lt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Lt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Lt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Eq _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Gt _); 
			solver.   
	  - intros . 
		induction l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]. 
		  -- intros . 
			refine (subsumptionCast _ _ Lt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Lt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Lt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Lt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Eq _); 
			solver.   
Defined. 
Inductive letter_comparison_rel : (Letter_u -> (Letter_u -> (Comparison_u -> Prop))) := 
	 | letter_comparison_A_A: letter_comparison_rel A_u A_u Eq_u
	 | letter_comparison_A_B: letter_comparison_rel A_u B_u Gt_u
	 | letter_comparison_A_C: letter_comparison_rel A_u C_u Gt_u
	 | letter_comparison_A_D: letter_comparison_rel A_u D_u Gt_u
	 | letter_comparison_A_F: letter_comparison_rel A_u F_u Gt_u
	 | letter_comparison_B_A: letter_comparison_rel B_u A_u Lt_u
	 | letter_comparison_B_B: letter_comparison_rel B_u B_u Eq_u
	 | letter_comparison_B_C: letter_comparison_rel B_u C_u Gt_u
	 | letter_comparison_B_D: letter_comparison_rel B_u D_u Gt_u
	 | letter_comparison_B_F: letter_comparison_rel B_u F_u Gt_u
	 | letter_comparison_C_A: letter_comparison_rel C_u A_u Lt_u
	 | letter_comparison_C_B: letter_comparison_rel C_u B_u Lt_u
	 | letter_comparison_C_C: letter_comparison_rel C_u C_u Eq_u
	 | letter_comparison_C_D: letter_comparison_rel C_u D_u Gt_u
	 | letter_comparison_C_F: letter_comparison_rel C_u F_u Gt_u
	 | letter_comparison_D_A: letter_comparison_rel D_u A_u Lt_u
	 | letter_comparison_D_B: letter_comparison_rel D_u B_u Lt_u
	 | letter_comparison_D_C: letter_comparison_rel D_u C_u Lt_u
	 | letter_comparison_D_D: letter_comparison_rel D_u D_u Eq_u
	 | letter_comparison_D_F: letter_comparison_rel D_u F_u Gt_u
	 | letter_comparison_F_A: letter_comparison_rel F_u A_u Lt_u
	 | letter_comparison_F_B: letter_comparison_rel F_u B_u Lt_u
	 | letter_comparison_F_C: letter_comparison_rel F_u C_u Lt_u
	 | letter_comparison_F_D: letter_comparison_rel F_u D_u Lt_u
	 | letter_comparison_F_F: letter_comparison_rel F_u F_u Eq_u. 
#[global] Hint Constructors letter_comparison_rel : core_hint_db.
#[global] Instance letter_comparison_lookup_rel : dictionary rel letter_comparison := { 
	lookup' := letter_comparison_rel
}.
#[global] Instance letter_comparison_getF : getFunc letter_comparison_rel := { 
	getF' := letter_comparison
}.
Theorem letter_comparison_rel_funct [l1: Letter_u] [l2: Letter_u]: (forall (VV: Comparison_u) (VV': Comparison_u) (H: letter_comparison_rel l1 l2 VV) (K: letter_comparison_rel l1 l2 VV') , VV = VV'). 
Proof. 
	try revert l2_p; generalize dependent l2; 
	destruct l1 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros ; 
	[destruct l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros | 
	destruct l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros | 
	destruct l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros | 
	destruct l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros | 
	destruct l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros ]; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve letter_comparison_rel_funct : f_rel_funct_db.
Theorem letter_comparison_A_A_lem: (letter_comparison_rel A_u A_u Eq_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letter_comparison_A_A_lem : f_rel_back.
Theorem letter_comparison_A_B_lem: (letter_comparison_rel A_u B_u Gt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letter_comparison_A_B_lem : f_rel_back.
Theorem letter_comparison_A_C_lem: (letter_comparison_rel A_u C_u Gt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letter_comparison_A_C_lem : f_rel_back.
Theorem letter_comparison_A_D_lem: (letter_comparison_rel A_u D_u Gt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letter_comparison_A_D_lem : f_rel_back.
Theorem letter_comparison_A_F_lem: (letter_comparison_rel A_u F_u Gt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letter_comparison_A_F_lem : f_rel_back.
Theorem letter_comparison_B_A_lem: (letter_comparison_rel B_u A_u Lt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letter_comparison_B_A_lem : f_rel_back.
Theorem letter_comparison_B_B_lem: (letter_comparison_rel B_u B_u Eq_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letter_comparison_B_B_lem : f_rel_back.
Theorem letter_comparison_B_C_lem: (letter_comparison_rel B_u C_u Gt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letter_comparison_B_C_lem : f_rel_back.
Theorem letter_comparison_B_D_lem: (letter_comparison_rel B_u D_u Gt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letter_comparison_B_D_lem : f_rel_back.
Theorem letter_comparison_B_F_lem: (letter_comparison_rel B_u F_u Gt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letter_comparison_B_F_lem : f_rel_back.
Theorem letter_comparison_C_A_lem: (letter_comparison_rel C_u A_u Lt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letter_comparison_C_A_lem : f_rel_back.
Theorem letter_comparison_C_B_lem: (letter_comparison_rel C_u B_u Lt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letter_comparison_C_B_lem : f_rel_back.
Theorem letter_comparison_C_C_lem: (letter_comparison_rel C_u C_u Eq_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letter_comparison_C_C_lem : f_rel_back.
Theorem letter_comparison_C_D_lem: (letter_comparison_rel C_u D_u Gt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letter_comparison_C_D_lem : f_rel_back.
Theorem letter_comparison_C_F_lem: (letter_comparison_rel C_u F_u Gt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letter_comparison_C_F_lem : f_rel_back.
Theorem letter_comparison_D_A_lem: (letter_comparison_rel D_u A_u Lt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letter_comparison_D_A_lem : f_rel_back.
Theorem letter_comparison_D_B_lem: (letter_comparison_rel D_u B_u Lt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letter_comparison_D_B_lem : f_rel_back.
Theorem letter_comparison_D_C_lem: (letter_comparison_rel D_u C_u Lt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letter_comparison_D_C_lem : f_rel_back.
Theorem letter_comparison_D_D_lem: (letter_comparison_rel D_u D_u Eq_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letter_comparison_D_D_lem : f_rel_back.
Theorem letter_comparison_D_F_lem: (letter_comparison_rel D_u F_u Gt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letter_comparison_D_F_lem : f_rel_back.
Theorem letter_comparison_F_A_lem: (letter_comparison_rel F_u A_u Lt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letter_comparison_F_A_lem : f_rel_back.
Theorem letter_comparison_F_B_lem: (letter_comparison_rel F_u B_u Lt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letter_comparison_F_B_lem : f_rel_back.
Theorem letter_comparison_F_C_lem: (letter_comparison_rel F_u C_u Lt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letter_comparison_F_C_lem : f_rel_back.
Theorem letter_comparison_F_D_lem: (letter_comparison_rel F_u D_u Lt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letter_comparison_F_D_lem : f_rel_back.
Theorem letter_comparison_F_F_lem: (letter_comparison_rel F_u F_u Eq_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letter_comparison_F_F_lem : f_rel_back.
Theorem letter_comparison_rel_ex (l1: Letter_u) (l2: Letter_u) (l1_p: (Letter_wf l1) /\ True) (l2_p: (Letter_wf l2) /\ True): letter_comparison_rel l1 l2 (⌊ letter_comparison (exist _ l1 l1_p) (exist _ l2 l2_p) -⌋). 
Proof. 
	Opaque letter_comparison.
	existence_lemma_pre letter_comparison; 
	try revert l2_p; generalize dependent l2; 
	destruct l1 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros ; 
	[destruct l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations]| 
	destruct l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations]| 
	destruct l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations]| 
	destruct l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations]| 
	destruct l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations]]; 
	simpl in *. 
	Transparent letter_comparison.
	all: existence_lemma_quicksolve letter_comparison; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve letter_comparison_rel_ex : rel_ax_db.
#[global] Opaque letter_comparison. 
Theorem letter_comparison__letter_comparison_rel_rw (l1: Letter_u) (l2: Letter_u) (l1_p: (Letter_wf l1) /\ True) (l2_p: (Letter_wf l2) /\ True) (VV: Comparison_u): ((⌊ letter_comparison (exist _ l1 l1_p) (exist _ l2 l2_p) -⌋) = VV) <-> (letter_comparison_rel l1 l2 VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite letter_comparison__letter_comparison_rel_rw : f_rel_funct_db.
#[global] Hint Resolve letter_comparison__letter_comparison_rel_rw : rel_ax_db.
#[global] Instance letter_comparison_lookup_rw : dictionary rwLem letter_comparison := { 
	lookup' := letter_comparison__letter_comparison_rel_rw
}.
Theorem letter_comparison__letter_comparison_rel (l1_r: Letter) (l2_r: Letter) (VV: Comparison_u): ((⌊ letter_comparison l1_r l2_r -⌋) = VV) <-> (letter_comparison_rel (⌊ l1_r -⌋) (⌊ l2_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite letter_comparison__letter_comparison_rel : f_rel_funct_db.
Theorem letter_comparison__letter_comparison_rel' (l1: Letter_u) (l2: Letter_u) (l1_r: Letter) (l2_r: Letter) (VV: Comparison_u): (l1 = (⌊ l1_r -⌋)) -> ((l2 = (⌊ l2_r -⌋)) -> (((⌊ letter_comparison l1_r l2_r -⌋) = VV) <-> (letter_comparison_rel l1 l2 VV))). 
Proof. 
	intros -> ->. 
	refine (letter_comparison__letter_comparison_rel l1_r l2_r VV). 
Qed. 
#[global] Hint Resolve letter_comparison__letter_comparison_rel' : f_rel_funct_db.
Theorem letter_comparison_rel_mk [l1: Letter_u] [l2: Letter_u] (l1_p: (Letter_wf l1) /\ True) (l2_p: (Letter_wf l2) /\ True): {VV: _ | letter_comparison_rel l1 l2 VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (letter_comparison_rel l1 l2 VV)) (letter_comparison (exist _ l1 l1_p) (exist _ l2 l2_p)) _); 
	rewrite <- letter_comparison__letter_comparison_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve letter_comparison_rel_mk : f_rel_funct_db.
#[global] Instance letter_comparisonPack : (@Pack (Letter ::RT (fun (l1_r: Letter) => (Letter ::RT (fun (l2_r: Letter) => nilRT)))) (Letter_u ::UT (Letter_u ::UT nilUT)) (ltac: (mkProjectsArgListTG (Letter ::RT (fun (l1_r: Letter) => (Letter ::RT (fun (l2_r: Letter) => nilRT)))) (Letter_u ::UT (Letter_u ::UT nilUT)))) Comparison_u (fun (x_74941377: (ArgList Letter ::RT (fun (l1_r: Letter) => (Letter ::RT (fun (l2_r: Letter) => nilRT))))) => (fun (v_x_74941377: Comparison_u) => (ltac: (flattenP (fun (l1_r: Letter) => (fun (l2_r: Letter) => (fun (VV: Comparison_u) => ((Comparison_wf VV) /\ True)))) x_74941377 v_x_74941377))))).
Proof. 
	buildPackG letter_comparison letter_comparison_rel letter_comparison__letter_comparison_rel letter_comparison_rel_funct. 
Defined.
Definition letter_comparison_eq_spec (l: Letter): Type := 
	{{forall (letter_comparisonres: Comparison_u), (letter_comparison_rel (⌊ l -⌋) (⌊ l -⌋) letter_comparisonres) -> (letter_comparisonres = Eq_u)}}. 
#[global] Hint Unfold letter_comparison_eq_spec : lia_unfold.
Theorem letter_comparison_eq (l: Letter): letter_comparison_eq_spec l. 
Proof. 
	destruct l as [l l_p]. 
	induction l as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]. 
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
Qed. 
Definition lower_letter_lowers_spec (l: Letter) (p: {{forall (letter_comparisonres: Comparison_u), (letter_comparison_rel F_u (⌊ l -⌋) letter_comparisonres) -> (letter_comparisonres = Lt_u)}}): Type := 
	{{forall (lower_letterres: Letter_u), (lower_letter_rel (⌊ l -⌋) lower_letterres) -> (forall (letter_comparisonres: Comparison_u), (letter_comparison_rel lower_letterres (⌊ l -⌋) letter_comparisonres) -> (letter_comparisonres = Lt_u))}}. 
#[global] Hint Unfold lower_letter_lowers_spec : lia_unfold.
Theorem lower_letter_lowers (l: Letter) (p: {{forall (letter_comparisonres: Comparison_u), (letter_comparison_rel F_u (⌊ l -⌋) letter_comparisonres) -> (letter_comparisonres = Lt_u)}}): lower_letter_lowers_spec l p. 
Proof. 
	destruct l as [l l_p]. 
	destruct p as [p p_p]. 
	try revert p_p; generalize dependent p; 
	induction l as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]. 
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		refine (exist _ p _); 
		solver.  
Qed. 
Definition modifier_comparison_spec (m1: Modifier) (m2: Modifier): Type := 
	Comparison. 
#[global] Hint Unfold modifier_comparison_spec : lia_unfold.
Definition modifier_comparison (m1: Modifier) (m2: Modifier): modifier_comparison_spec m1 m2. 
Proof. 
	destruct m1 as [m1 m1_p]. 
	destruct m2 as [m2 m2_p]. 
	try revert m2_p; generalize dependent m2; 
	induction m1 as [(*Minus*)  | (*Natural*)  | (*Plus*) ]. 
	  - intros . 
		induction m2 as [(*Minus*)  | (*Natural*)  | (*Plus*) ]. 
		  -- intros . 
			refine (subsumptionCast _ _ Eq _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Lt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Lt _); 
			solver.   
	  - intros . 
		induction m2 as [(*Minus*)  | (*Natural*)  | (*Plus*) ]. 
		  -- intros . 
			refine (subsumptionCast _ _ Gt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Eq _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Lt _); 
			solver.   
	  - intros . 
		induction m2 as [(*Minus*)  | (*Natural*)  | (*Plus*) ]. 
		  -- intros . 
			refine (subsumptionCast _ _ Gt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Gt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Eq _); 
			solver.   
Defined. 
Inductive modifier_comparison_rel : (Modifier_u -> (Modifier_u -> (Comparison_u -> Prop))) := 
	 | modifier_comparison_Plus_Plus: modifier_comparison_rel Plus_u Plus_u Eq_u
	 | modifier_comparison_Plus_Natural: modifier_comparison_rel Plus_u Natural_u Gt_u
	 | modifier_comparison_Plus_Minus: modifier_comparison_rel Plus_u Minus_u Gt_u
	 | modifier_comparison_Natural_Plus: modifier_comparison_rel Natural_u Plus_u Lt_u
	 | modifier_comparison_Natural_Natural: modifier_comparison_rel Natural_u Natural_u Eq_u
	 | modifier_comparison_Natural_Minus: modifier_comparison_rel Natural_u Minus_u Gt_u
	 | modifier_comparison_Minus_Plus: modifier_comparison_rel Minus_u Plus_u Lt_u
	 | modifier_comparison_Minus_Natural: modifier_comparison_rel Minus_u Natural_u Lt_u
	 | modifier_comparison_Minus_Minus: modifier_comparison_rel Minus_u Minus_u Eq_u. 
#[global] Hint Constructors modifier_comparison_rel : core_hint_db.
#[global] Instance modifier_comparison_lookup_rel : dictionary rel modifier_comparison := { 
	lookup' := modifier_comparison_rel
}.
#[global] Instance modifier_comparison_getF : getFunc modifier_comparison_rel := { 
	getF' := modifier_comparison
}.
Theorem modifier_comparison_rel_funct [m1: Modifier_u] [m2: Modifier_u]: (forall (VV: Comparison_u) (VV': Comparison_u) (H: modifier_comparison_rel m1 m2 VV) (K: modifier_comparison_rel m1 m2 VV') , VV = VV'). 
Proof. 
	try revert m2_p; generalize dependent m2; 
	destruct m1 as [(*Minus*)  | (*Natural*)  | (*Plus*) ]; 
	intros ; 
	[destruct m2 as [(*Minus*)  | (*Natural*)  | (*Plus*) ]; 
	intros | 
	destruct m2 as [(*Minus*)  | (*Natural*)  | (*Plus*) ]; 
	intros | 
	destruct m2 as [(*Minus*)  | (*Natural*)  | (*Plus*) ]; 
	intros ]; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve modifier_comparison_rel_funct : f_rel_funct_db.
Theorem modifier_comparison_Plus_Plus_lem: (modifier_comparison_rel Plus_u Plus_u Eq_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite modifier_comparison_Plus_Plus_lem : f_rel_back.
Theorem modifier_comparison_Plus_Natural_lem: (modifier_comparison_rel Plus_u Natural_u Gt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite modifier_comparison_Plus_Natural_lem : f_rel_back.
Theorem modifier_comparison_Plus_Minus_lem: (modifier_comparison_rel Plus_u Minus_u Gt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite modifier_comparison_Plus_Minus_lem : f_rel_back.
Theorem modifier_comparison_Natural_Plus_lem: (modifier_comparison_rel Natural_u Plus_u Lt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite modifier_comparison_Natural_Plus_lem : f_rel_back.
Theorem modifier_comparison_Natural_Natural_lem: (modifier_comparison_rel Natural_u Natural_u Eq_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite modifier_comparison_Natural_Natural_lem : f_rel_back.
Theorem modifier_comparison_Natural_Minus_lem: (modifier_comparison_rel Natural_u Minus_u Gt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite modifier_comparison_Natural_Minus_lem : f_rel_back.
Theorem modifier_comparison_Minus_Plus_lem: (modifier_comparison_rel Minus_u Plus_u Lt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite modifier_comparison_Minus_Plus_lem : f_rel_back.
Theorem modifier_comparison_Minus_Natural_lem: (modifier_comparison_rel Minus_u Natural_u Lt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite modifier_comparison_Minus_Natural_lem : f_rel_back.
Theorem modifier_comparison_Minus_Minus_lem: (modifier_comparison_rel Minus_u Minus_u Eq_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite modifier_comparison_Minus_Minus_lem : f_rel_back.
Theorem modifier_comparison_rel_ex (m1: Modifier_u) (m2: Modifier_u) (m1_p: (Modifier_wf m1) /\ True) (m2_p: (Modifier_wf m2) /\ True): modifier_comparison_rel m1 m2 
		(⌊ modifier_comparison (exist _ m1 m1_p) (exist _ m2 m2_p) -⌋). 
Proof. 
	Opaque modifier_comparison.
	existence_lemma_pre modifier_comparison; 
	try revert m2_p; generalize dependent m2; 
	destruct m1 as [(*Minus*)  | (*Natural*)  | (*Plus*) ]; 
	intros ; 
	[destruct m2 as [(*Minus*)  | (*Natural*)  | (*Plus*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations| 
	fix_notations]| 
	destruct m2 as [(*Minus*)  | (*Natural*)  | (*Plus*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations| 
	fix_notations]| 
	destruct m2 as [(*Minus*)  | (*Natural*)  | (*Plus*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations| 
	fix_notations]]; 
	simpl in *. 
	Transparent modifier_comparison.
	all: existence_lemma_quicksolve modifier_comparison; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve modifier_comparison_rel_ex : rel_ax_db.
#[global] Opaque modifier_comparison. 
Theorem modifier_comparison__modifier_comparison_rel_rw (m1: Modifier_u) (m2: Modifier_u) (m1_p: (Modifier_wf m1) /\ True) (m2_p: (Modifier_wf m2) /\ True) (VV: Comparison_u): ((⌊ modifier_comparison (exist _ m1 m1_p) (exist _ m2 m2_p) -⌋) = VV) <-> (modifier_comparison_rel m1 m2 VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite modifier_comparison__modifier_comparison_rel_rw : f_rel_funct_db.
#[global] Hint Resolve modifier_comparison__modifier_comparison_rel_rw : rel_ax_db.
#[global] Instance modifier_comparison_lookup_rw : dictionary rwLem modifier_comparison := { 
	lookup' := modifier_comparison__modifier_comparison_rel_rw
}.
Theorem modifier_comparison__modifier_comparison_rel (m1_r: Modifier) (m2_r: Modifier) (VV: Comparison_u): ((⌊ modifier_comparison m1_r m2_r -⌋) = VV) <-> (modifier_comparison_rel (⌊ m1_r -⌋) (⌊ m2_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite modifier_comparison__modifier_comparison_rel : f_rel_funct_db.
Theorem modifier_comparison__modifier_comparison_rel' (m1: Modifier_u) (m2: Modifier_u) (m1_r: Modifier) (m2_r: Modifier) (VV: Comparison_u): (m1 = (⌊ m1_r -⌋)) -> ((m2 = (⌊ m2_r -⌋)) -> (((⌊ modifier_comparison m1_r m2_r -⌋) = VV) <-> (modifier_comparison_rel m1 m2 VV))). 
Proof. 
	intros -> ->. 
	refine (modifier_comparison__modifier_comparison_rel m1_r m2_r VV). 
Qed. 
#[global] Hint Resolve modifier_comparison__modifier_comparison_rel' : f_rel_funct_db.
Theorem modifier_comparison_rel_mk [m1: Modifier_u] [m2: Modifier_u] (m1_p: (Modifier_wf m1) /\ True) (m2_p: (Modifier_wf m2) /\ True): {VV: _ | modifier_comparison_rel m1 m2 VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (modifier_comparison_rel m1 m2 VV)) (modifier_comparison (exist _ m1 m1_p) (exist _ m2 m2_p)) _); 
	rewrite <- modifier_comparison__modifier_comparison_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve modifier_comparison_rel_mk : f_rel_funct_db.
#[global] Instance modifier_comparisonPack : (@Pack (Modifier ::RT (fun (m1_r: Modifier) => (Modifier ::RT (fun (m2_r: Modifier) => nilRT)))) (Modifier_u ::UT (Modifier_u ::UT nilUT)) (ltac: (mkProjectsArgListTG (Modifier ::RT (fun (m1_r: Modifier) => (Modifier ::RT (fun (m2_r: Modifier) => nilRT)))) (Modifier_u ::UT (Modifier_u ::UT nilUT)))) Comparison_u (fun (x_13952235: (ArgList Modifier ::RT (fun (m1_r: Modifier) => (Modifier ::RT (fun (m2_r: Modifier) => nilRT))))) => (fun (v_x_13952235: Comparison_u) => (ltac: (flattenP (fun (m1_r: Modifier) => (fun (m2_r: Modifier) => (fun (VV: Comparison_u) => ((Comparison_wf VV) /\ True)))) x_13952235 v_x_13952235))))).
Proof. 
	buildPackG modifier_comparison modifier_comparison_rel modifier_comparison__modifier_comparison_rel modifier_comparison_rel_funct. 
Defined.
Inductive Color_u : Type := 
	 | Black_u: Color_u
	 | Primary_u: RGB_u -> Color_u
	 | White_u: Color_u. 
Fixpoint Color_eq (x: Color_u) (y: Color_u): bool := 
	match (x, y) with (Black_u, Black_u) => true | (Primary_u x, Primary_u x') => (true && (x ==? x')) | (White_u, White_u) => true | (_, _) => false end. 
Theorem Color_eq_refl: (forall (x: Color_u) , is_true (Color_eq x x)). 
Proof. 
	eq_refl_rec. 
Qed. 
#[global] Hint Resolve Color_eq_refl : eq_hint_db.
Theorem Color_eqb_eq: (forall (s: Color_u) (t: Color_u) , (is_true (Color_eq s t)) -> (s = t)). 
Proof. 
	eqb_eq_lem. 
Qed. 
#[global] Hint Resolve Color_eqb_eq : eq_hint_db.
#[global] Instance leibnitz_eq_Color : LeibnitzEqB := { 
	equalB' := Color_eq;
	refl' := Color_eq_refl;
	eqb_eq' := Color_eqb_eq
}.
Fixpoint Color_wf (x: Color_u): Prop := 
	match x with Black_u => True | (Primary_u VV) => ((RGB_wf VV) /\ True) | White_u => True end. 
Theorem Color_wf_ref [p: Color_u -> Prop] (tm: {v: Color_u | (Color_wf v) /\ (p v)}): Color_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation Color := {x: Color_u | (Color_wf x) /\ True}. 
Definition Black_lem: (Color_wf Black_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Black: Color := 
	exist _ Black_u Black_lem. 
Definition Primary_lem (VV: RGB): (Color_wf (Primary_u (⌊ VV -⌋))) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Primary (VV: RGB): Color := 
	exist _ (Primary_u (⌊ VV -⌋)) (Primary_lem VV). 
Definition White_lem: (Color_wf White_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition White: Color := 
	exist _ White_u White_lem. 
#[global] Hint Resolve Color_wf_ref : wf_constr_db.
#[global] Hint Unfold Color_wf : wf_constr_db.
#[global] Hint Resolve Color_eq : ref_constr_db.
#[global] Hint Unfold Black : ref_constr_db.
#[global] Hint Unfold Primary : ref_constr_db.
#[global] Hint Unfold White : ref_constr_db.
Definition isred_spec (c: Color): Type := 
	SFBool. 
#[global] Hint Unfold isred_spec : lia_unfold.
Definition isred (c: Color): isred_spec c. 
Proof. 
	destruct c as [c c_p]. 
	induction c as [(*Black*)  | (*Primary*) ds_d5TZ | (*White*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ SFFalse _); 
		solver.  
	  - intros . 
		induction ds_d5TZ as [(*Blue*)  | (*Green*)  | (*Red*) ]. 
		  -- intros . 
			refine (subsumptionCast _ _ SFFalse _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ SFFalse _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ SFTrue _); 
			solver.   
	  - intros . 
		refine (subsumptionCast _ _ SFFalse _); 
		solver.  
Defined. 
Definition monochrome_spec (c: Color): Type := 
	SFBool. 
#[global] Hint Unfold monochrome_spec : lia_unfold.
Definition monochrome (c: Color): monochrome_spec c. 
Proof. 
	destruct c as [c c_p]. 
	induction c as [(*Black*)  | (*Primary*) p | (*White*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ SFTrue _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ SFFalse _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ SFTrue _); 
		solver.  
Defined. 
Inductive monochrome_rel : (Color_u -> (SFBool_u -> Prop)) := 
	 | monochrome_Black: monochrome_rel Black_u SFTrue_u
	 | monochrome_White: monochrome_rel White_u SFTrue_u
	 | monochrome_Primary: (forall p , monochrome_rel (Primary_u p) SFFalse_u). 
#[global] Hint Constructors monochrome_rel : core_hint_db.
#[global] Instance monochrome_lookup_rel : dictionary rel monochrome := { 
	lookup' := monochrome_rel
}.
#[global] Instance monochrome_getF : getFunc monochrome_rel := { 
	getF' := monochrome
}.
Theorem monochrome_rel_funct [c: Color_u]: (forall (VV: SFBool_u) (VV': SFBool_u) (H: monochrome_rel c VV) (K: monochrome_rel c VV') , VV = VV'). 
Proof. 
	induction c as [(*Black*)  | (*Primary*) p | (*White*) ]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve monochrome_rel_funct : f_rel_funct_db.
Theorem monochrome_Black_lem: (monochrome_rel Black_u SFTrue_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite monochrome_Black_lem : f_rel_back.
Theorem monochrome_White_lem: (monochrome_rel White_u SFTrue_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite monochrome_White_lem : f_rel_back.
Theorem monochrome_Primary_lem (p: _): (monochrome_rel (Primary_u p) SFFalse_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite monochrome_Primary_lem : f_rel_back.
Theorem monochrome_rel_ex (c: Color_u) (c_p: (Color_wf c) /\ True): monochrome_rel c (⌊ monochrome (exist _ c c_p) -⌋). 
Proof. 
	Opaque monochrome.
	existence_lemma_pre monochrome; 
	induction c as [(*Black*)  | (*Primary*) p | (*White*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations| 
	fix_notations]; 
	simpl in *. 
	Transparent monochrome.
	all: existence_lemma_quicksolve monochrome; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve monochrome_rel_ex : rel_ax_db.
#[global] Opaque monochrome. 
Theorem monochrome__monochrome_rel_rw (c: Color_u) (c_p: (Color_wf c) /\ True) (VV: SFBool_u): ((⌊ monochrome (exist _ c c_p) -⌋) = VV) <-> (monochrome_rel c VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite monochrome__monochrome_rel_rw : f_rel_funct_db.
#[global] Hint Resolve monochrome__monochrome_rel_rw : rel_ax_db.
#[global] Instance monochrome_lookup_rw : dictionary rwLem monochrome := { 
	lookup' := monochrome__monochrome_rel_rw
}.
Theorem monochrome__monochrome_rel (c_r: Color) (VV: SFBool_u): ((⌊ monochrome c_r -⌋) = VV) <-> (monochrome_rel (⌊ c_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite monochrome__monochrome_rel : f_rel_funct_db.
Theorem monochrome__monochrome_rel' (c: Color_u) (c_r: Color) (VV: SFBool_u): (c = (⌊ c_r -⌋)) -> (((⌊ monochrome c_r -⌋) = VV) <-> (monochrome_rel c VV)). 
Proof. 
	intros ->. 
	refine (monochrome__monochrome_rel c_r VV). 
Qed. 
#[global] Hint Resolve monochrome__monochrome_rel' : f_rel_funct_db.
Theorem monochrome_rel_mk [c: Color_u] (c_p: (Color_wf c) /\ True): {VV: _ | monochrome_rel c VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (monochrome_rel c VV)) (monochrome (exist _ c c_p)) _); 
	rewrite <- monochrome__monochrome_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve monochrome_rel_mk : f_rel_funct_db.
#[global] Instance monochromePack : (@Pack (Color ::RT (fun (c_r: Color) => nilRT)) (Color_u ::UT nilUT) (ltac: (mkProjectsArgListTG (Color ::RT (fun (c_r: Color) => nilRT)) (Color_u ::UT nilUT))) SFBool_u (fun (x_45414719: (ArgList Color ::RT (fun (c_r: Color) => nilRT))) => (fun (v_x_45414719: SFBool_u) => (ltac: (flattenP (fun (c_r: Color) => (fun (VV: SFBool_u) => ((SFBool_wf VV) /\ True))) x_45414719 v_x_45414719))))).
Proof. 
	buildPackG monochrome monochrome_rel monochrome__monochrome_rel monochrome_rel_funct. 
Defined.