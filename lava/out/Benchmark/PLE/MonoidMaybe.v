From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Inductive Maybe_u : Set := 
	 | Just_u: Z -> Maybe_u
	 | Nothing_u: Maybe_u
	 | Nothing_u: Maybe_u. 
Fixpoint Maybe_eq (x: Maybe_u) (y: Maybe_u): bool := 
	match (x, y) with (Just_u x, Just_u x') => (true && (x ==? x')) | (Nothing_u, Nothing_u) => true | (Nothing_u, Nothing_u) => true | (_, _) => false end. 
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
	match x with (Just_u VV) => True | Nothing_u => True | Nothing_u => True end. 
Theorem Maybe_wf_ref [p: Maybe_u -> Prop] (tm: {v: Maybe_u | (Maybe_wf v) /\ (p v)}): Maybe_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation Maybe := {x: Maybe_u | (Maybe_wf x) /\ True}. 
Definition Just_lem (VV: {VV: Z | True}): (Maybe_wf (Just_u (⌊ VV -⌋))) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Just (VV: {VV: Z | True}): Maybe := 
	exist _ (Just_u (⌊ VV -⌋)) (Just_lem VV). 
Definition Nothing_lem: (Maybe_wf Nothing_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Nothing: Maybe := 
	exist _ Nothing_u Nothing_lem. 
Definition Nothing_lem: (Maybe_wf Nothing_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Nothing: Maybe := 
	exist _ Nothing_u Nothing_lem. 
#[global] Hint Resolve Maybe_wf_ref : wf_constr_db.
#[global] Hint Unfold Maybe_wf : wf_constr_db.
#[global] Hint Resolve Maybe_eq : ref_constr_db.
#[global] Hint Unfold Just : ref_constr_db.
#[global] Hint Unfold Nothing : ref_constr_db.
#[global] Hint Unfold Nothing : ref_constr_db.
Definition mappend (lq_tmp0: Maybe) (lq_tmp1: Maybe): Maybe. 
Proof. 
	destruct lq_tmp0 as [lq_tmp0 lq_tmp0_p]. 
	destruct lq_tmp1 as [lq_tmp1 lq_tmp1_p]. 
	try revert lq_tmp1_p; generalize dependent lq_tmp1; 
	induction lq_tmp0 as [(*Just*) x | (*Nothing*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ (Just (exist (fun (VV: Z) => True) x (ltac: (solver)))) _); 
		solver.  
	  - intros . 
		refine (exist _ lq_tmp1 _); 
		solver.  
Defined. 
Inductive mappend_rel : (Maybe_u -> (Maybe_u -> (Maybe_u -> Prop))) := 
	 | mappend_Nothing: (forall lq_tmp1 , mappend_rel Nothing_u lq_tmp1 lq_tmp1)
	 | mappend_Just: (forall lq_tmp1 x , mappend_rel (Just_u x) lq_tmp1 (Just_u x)). 
#[global] Hint Constructors mappend_rel : core_hint_db.
#[global] Instance mappend_lookup_rel : dictionary rel mappend := { 
	lookup' := mappend_rel
}.
#[global] Instance mappend_getF : getFunc mappend_rel := { 
	getF' := mappend
}.
Definition mappend_rel_funct [lq_tmp0: Maybe_u] [lq_tmp1: Maybe_u]: (forall (VV: Maybe_u) (VV': Maybe_u) (H: mappend_rel lq_tmp0 lq_tmp1 VV) (K: mappend_rel lq_tmp0 lq_tmp1 VV') , VV = VV'). 
Proof. 
	try revert lq_tmp1_p; generalize dependent lq_tmp1; 
	induction lq_tmp0 as [(*Just*) x | (*Nothing*) ]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve mappend_rel_funct : f_rel_funct_db.
Theorem mappend_Nothing_lem (lq_tmp1: _): (mappend_rel Nothing_u lq_tmp1 lq_tmp1) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite mappend_Nothing_lem : f_rel_back.
Theorem mappend_Just_lem (x: _) (lq_tmp1: _): (mappend_rel (Just_u x) lq_tmp1 (Just_u x)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite mappend_Just_lem : f_rel_back.
Theorem mappend_rel_ex (lq_tmp0: Maybe_u) (lq_tmp1: Maybe_u) (lq_tmp0_p: (Maybe_wf lq_tmp0) /\ True) (lq_tmp1_p: (Maybe_wf lq_tmp1) /\ True): mappend_rel lq_tmp0 lq_tmp1 
		(⌊ mappend (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p) -⌋). 
Proof. 
	existence_lemma_pre mappend; 
	try revert lq_tmp1_p; generalize dependent lq_tmp1; 
	induction lq_tmp0 as [(*Just*) x | (*Nothing*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations]; 
	existence_lemma_quicksolve mappend; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve mappend_rel_ex : rel_ax_db.
Opaque mappend. 
Theorem mappend__mappend_rel_rw (lq_tmp0: Maybe_u) (lq_tmp1: Maybe_u) (lq_tmp0_p: (Maybe_wf lq_tmp0) /\ True) (lq_tmp1_p: (Maybe_wf lq_tmp1) /\ True) (VV: Maybe_u): ((⌊ mappend (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p) -⌋) = VV) <-> (mappend_rel lq_tmp0 lq_tmp1 VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite mappend__mappend_rel_rw : f_rel_funct_db.
#[global] Hint Resolve mappend__mappend_rel_rw : rel_ax_db.
#[global] Instance mappend_lookup_rw : dictionary rwLem mappend := { 
	lookup' := mappend__mappend_rel_rw
}.
Theorem mappend__mappend_rel (lq_tmp0_r: Maybe) (lq_tmp1_r: Maybe) (VV: Maybe_u): ((⌊ mappend lq_tmp0_r lq_tmp1_r -⌋) = VV) <-> (mappend_rel (⌊ lq_tmp0_r -⌋) (⌊ lq_tmp1_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite mappend__mappend_rel : f_rel_funct_db.
Theorem mappend__mappend_rel' (lq_tmp0: Maybe_u) (lq_tmp1: Maybe_u) (lq_tmp0_r: Maybe) (lq_tmp1_r: Maybe) (VV: Maybe_u): (lq_tmp0 = (⌊ lq_tmp0_r -⌋)) -> ((lq_tmp1 = (⌊ lq_tmp1_r -⌋)) -> (((⌊ mappend lq_tmp0_r lq_tmp1_r -⌋) = VV) <-> (mappend_rel lq_tmp0 lq_tmp1 VV))). 
Proof. 
	intros -> ->. 
	refine (mappend__mappend_rel lq_tmp0_r lq_tmp1_r VV). 
Qed. 
#[global] Hint Resolve mappend__mappend_rel' : f_rel_funct_db.
Definition mappend_rel_mk [lq_tmp0: Maybe_u] [lq_tmp1: Maybe_u] (lq_tmp0_p: (Maybe_wf lq_tmp0) /\ True) (lq_tmp1_p: (Maybe_wf lq_tmp1) /\ True): {VV: _ | mappend_rel lq_tmp0 lq_tmp1 VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (mappend_rel lq_tmp0 lq_tmp1 VV)) 
		(mappend (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p)) _); 
	rewrite <- mappend__mappend_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve mappend_rel_mk : f_rel_funct_db.
#[global] Instance mappendPack : (@Pack (Maybe ::RT (fun (lq_tmp0_r: Maybe) => (Maybe ::RT (fun (lq_tmp1_r: Maybe) => nilRT)))) (Maybe_u ::UT (Maybe_u ::UT nilUT)) (ltac: (mkProjectsArgListTG (Maybe ::RT (fun (lq_tmp0_r: Maybe) => (Maybe ::RT (fun (lq_tmp1_r: Maybe) => nilRT)))) (Maybe_u ::UT (Maybe_u ::UT nilUT)))) Maybe_u (fun (x_38332132: (ArgList Maybe ::RT (fun (lq_tmp0_r: Maybe) => (Maybe ::RT (fun (lq_tmp1_r: Maybe) => nilRT))))) => (fun (v_x_38332132: Maybe_u) => (ltac: (flattenP (fun (lq_tmp0_r: Maybe) => (fun (lq_tmp1_r: Maybe) => (fun (VV: Maybe_u) => ((Maybe_wf VV) /\ True)))) x_38332132 v_x_38332132))))).
Proof. 
	buildPackG mappend mappend_rel mappend__mappend_rel mappend_rel_funct. 
Defined.
Definition mappend_assoc (xs: Maybe) (ys: Maybe) (zs: Maybe): {{forall (mappendres: Maybe_u), (mappend_rel (⌊ xs -⌋) (⌊ ys -⌋) mappendres) -> (forall (mappend_res_2: Maybe_u), (mappend_rel mappendres (⌊ zs -⌋) mappend_res_2) -> (forall (mappend_res_3: Maybe_u), (mappend_rel (⌊ ys -⌋) (⌊ zs -⌋) mappend_res_3) -> (forall (mappend_res_4: Maybe_u), (mappend_rel (⌊ xs -⌋) mappend_res_3 mappend_res_4) -> (mappend_res_2 == mappend_res_4))))}}. 
Proof. 
	destruct xs as [xs xs_p]. 
	destruct ys as [ys ys_p]. 
	destruct zs as [zs zs_p]. 
	try revert zs_p; generalize dependent zs; try revert ys_p; generalize dependent ys; 
	induction xs as [(*Just*) x | (*Nothing*) ]. 
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		induction ys as [(*Just*) ys | (*Nothing*) ]. 
		  -- intros . 
			refine (exist _ unit _); 
			solver.  
		  -- intros . 
			refine (exist _ unit _); 
			solver.   
Defined. 
Definition mempty: Maybe. 
Proof. 
	refine (subsumptionCast _ _ Nothing _); 
	solver. 
Defined. 
Inductive mempty_rel : (Maybe_u -> Prop) := 
	 | mempty_def: mempty_rel Nothing_u. 
#[global] Hint Constructors mempty_rel : core_hint_db.
#[global] Instance mempty_lookup_rel : dictionary rel mempty := { 
	lookup' := mempty_rel
}.
#[global] Instance mempty_getF : getFunc mempty_rel := { 
	getF' := mempty
}.
Definition mempty_rel_funct: (forall (VV: Maybe_u) (VV': Maybe_u) (H: mempty_rel VV) (K: mempty_rel VV') , VV = VV'). 
Proof. 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve mempty_rel_funct : f_rel_funct_db.
Theorem mempty_def_lem: (mempty_rel Nothing_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite mempty_def_lem : f_rel_back.
Theorem mempty_rel_ex: mempty_rel (⌊ mempty -⌋). 
Proof. 
	existence_lemma_pre mempty; 
	fix_notations; 
	existence_lemma_quicksolve mempty; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve mempty_rel_ex : rel_ax_db.
Opaque mempty. 
Theorem mempty__mempty_rel_rw (VV: Maybe_u): ((⌊ mempty -⌋) = VV) <-> (mempty_rel VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite mempty__mempty_rel_rw : f_rel_funct_db.
#[global] Hint Resolve mempty__mempty_rel_rw : rel_ax_db.
#[global] Instance mempty_lookup_rw : dictionary rwLem mempty := { 
	lookup' := mempty__mempty_rel_rw
}.
Theorem mempty__mempty_rel (VV: Maybe_u): ((⌊ mempty -⌋) = VV) <-> (mempty_rel VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite mempty__mempty_rel : f_rel_funct_db.
Theorem mempty__mempty_rel' (VV: Maybe_u): ((⌊ mempty -⌋) = VV) <-> (mempty_rel VV). 
Proof. 
	intros . 
	refine (mempty__mempty_rel VV). 
Qed. 
#[global] Hint Resolve mempty__mempty_rel' : f_rel_funct_db.
Definition mempty_rel_mk: {VV: _ | mempty_rel VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (mempty_rel VV)) mempty _); 
	rewrite <- mempty__mempty_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve mempty_rel_mk : f_rel_funct_db.
Definition mempty_left (x: Maybe): {{forall (mappendres: Maybe_u), (mappend_rel (⌊ mempty -⌋) (⌊ x -⌋) mappendres) -> (mappendres = (⌊ x -⌋))}}. 
Proof. 
	destruct x as [x x_p]. 
	refine (exist _ unit _); 
	solver. 
Defined. 
Definition mempty_right (x: Maybe): {{forall (mappendres: Maybe_u), (mappend_rel (⌊ x -⌋) (⌊ mempty -⌋) mappendres) -> (mappendres = (⌊ x -⌋))}}. 
Proof. 
	destruct x as [x x_p]. 
	induction x as [(*Just*) x | (*Nothing*) ]. 
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
Defined. 
Inductive Maybe_u : Set := 
	 | Just_u: Z -> Maybe_u
	 | Nothing_u: Maybe_u
	 | Nothing_u: Maybe_u. 
Fixpoint Maybe_eq (x: Maybe_u) (y: Maybe_u): bool := 
	match (x, y) with (Just_u x, Just_u x') => (true && (x ==? x')) | (Nothing_u, Nothing_u) => true | (Nothing_u, Nothing_u) => true | (_, _) => false end. 
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
	match x with (Just_u VV) => True | Nothing_u => True | Nothing_u => True end. 
Theorem Maybe_wf_ref [p: Maybe_u -> Prop] (tm: {v: Maybe_u | (Maybe_wf v) /\ (p v)}): Maybe_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation Maybe := {x: Maybe_u | (Maybe_wf x) /\ True}. 
Definition Just_lem (VV: {VV: Z | True}): (Maybe_wf (Just_u (⌊ VV -⌋))) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Just (VV: {VV: Z | True}): Maybe := 
	exist _ (Just_u (⌊ VV -⌋)) (Just_lem VV). 
Definition Nothing_lem: (Maybe_wf Nothing_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Nothing: Maybe := 
	exist _ Nothing_u Nothing_lem. 
Definition Nothing_lem: (Maybe_wf Nothing_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Nothing: Maybe := 
	exist _ Nothing_u Nothing_lem. 
#[global] Hint Resolve Maybe_wf_ref : wf_constr_db.
#[global] Hint Unfold Maybe_wf : wf_constr_db.
#[global] Hint Resolve Maybe_eq : ref_constr_db.
#[global] Hint Unfold Just : ref_constr_db.
#[global] Hint Unfold Nothing : ref_constr_db.
#[global] Hint Unfold Nothing : ref_constr_db.