From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Set Universe Polymorphism.
Inductive MaybeInt_u : Type := 
	 | Just_u: Z -> MaybeInt_u
	 | Nothing_u: MaybeInt_u. 
Fixpoint MaybeInt_eq (x: MaybeInt_u) (y: MaybeInt_u): bool := 
	match (x, y) with (Just_u x, Just_u x') => (true && (x ==? x')) | (Nothing_u, Nothing_u) => true | (_, _) => false end. 
Theorem MaybeInt_eq_refl: (forall (x: MaybeInt_u) , is_true (MaybeInt_eq x x)). 
Proof. 
	eq_refl_rec. 
Qed. 
#[global] Hint Resolve MaybeInt_eq_refl : eq_hint_db.
Theorem MaybeInt_eqb_eq: (forall (s: MaybeInt_u) (t: MaybeInt_u) , (is_true (MaybeInt_eq s t)) -> (s = t)). 
Proof. 
	eqb_eq_lem. 
Qed. 
#[global] Hint Resolve MaybeInt_eqb_eq : eq_hint_db.
#[global] Instance leibnitz_eq_MaybeInt : LeibnitzEqB := { 
	equalB' := MaybeInt_eq;
	refl' := MaybeInt_eq_refl;
	eqb_eq' := MaybeInt_eqb_eq
}.
Fixpoint MaybeInt_wf (x: MaybeInt_u): Prop := 
	match x with (Just_u VV) => True | Nothing_u => True end. 
Theorem MaybeInt_wf_ref [p: MaybeInt_u -> Prop] (tm: {v: MaybeInt_u | (MaybeInt_wf v) /\ (p v)}): MaybeInt_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation MaybeInt := {x: MaybeInt_u | (MaybeInt_wf x) /\ True}. 
Definition Just_lem (VV: {VV: Z | True}): (MaybeInt_wf (Just_u (⌊ VV -⌋))) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Just (VV: {VV: Z | True}): MaybeInt := 
	exist _ (Just_u (⌊ VV -⌋)) (Just_lem VV). 
Definition Nothing_lem: (MaybeInt_wf Nothing_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Nothing: MaybeInt := 
	exist _ Nothing_u Nothing_lem. 
#[global] Hint Resolve MaybeInt_wf_ref : wf_constr_db.
#[global] Hint Unfold MaybeInt_wf : wf_constr_db.
#[global] Hint Resolve MaybeInt_eq : ref_constr_db.
#[global] Hint Unfold Just : ref_constr_db.
#[global] Hint Unfold Nothing : ref_constr_db.
Definition mappend_spec (lq_tmp0: MaybeInt) (lq_tmp1: MaybeInt): Type := 
	MaybeInt. 
#[global] Hint Unfold mappend_spec : lia_unfold.
Definition mappend (lq_tmp0: MaybeInt) (lq_tmp1: MaybeInt): mappend_spec lq_tmp0 lq_tmp1. 
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
Inductive mappend_rel : (MaybeInt_u -> (MaybeInt_u -> (MaybeInt_u -> Prop))) := 
	 | mappend_Nothing: (forall lq_tmp1 , mappend_rel Nothing_u lq_tmp1 lq_tmp1)
	 | mappend_Just: (forall lq_tmp1 x , mappend_rel (Just_u x) lq_tmp1 (Just_u x)). 
#[global] Hint Constructors mappend_rel : core_hint_db.
#[global] Instance mappend_lookup_rel : dictionary rel mappend := { 
	lookup' := mappend_rel
}.
#[global] Instance mappend_getF : getFunc mappend_rel := { 
	getF' := mappend
}.
Theorem mappend_rel_funct [lq_tmp0: MaybeInt_u] [lq_tmp1: MaybeInt_u]: (forall (VV: MaybeInt_u) (VV': MaybeInt_u) (H: mappend_rel lq_tmp0 lq_tmp1 VV) (K: mappend_rel lq_tmp0 lq_tmp1 VV') , VV = VV'). 
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
Theorem mappend_rel_ex (lq_tmp0: MaybeInt_u) (lq_tmp1: MaybeInt_u) (lq_tmp0_p: (MaybeInt_wf lq_tmp0) /\ True) (lq_tmp1_p: (MaybeInt_wf lq_tmp1) /\ True): mappend_rel lq_tmp0 lq_tmp1 
		(⌊ mappend (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p) -⌋). 
Proof. 
	Opaque mappend.
	existence_lemma_pre mappend; 
	try revert lq_tmp1_p; generalize dependent lq_tmp1; 
	induction lq_tmp0 as [(*Just*) x | (*Nothing*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations]; 
	simpl in *. 
	Transparent mappend.
	all: existence_lemma_quicksolve mappend; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve mappend_rel_ex : rel_ax_db.
#[global] Opaque mappend. 
Theorem mappend__mappend_rel_rw (lq_tmp0: MaybeInt_u) (lq_tmp1: MaybeInt_u) (lq_tmp0_p: (MaybeInt_wf lq_tmp0) /\ True) (lq_tmp1_p: (MaybeInt_wf lq_tmp1) /\ True) (VV: MaybeInt_u): ((⌊ mappend (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p) -⌋) = VV) <-> (mappend_rel lq_tmp0 lq_tmp1 VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite mappend__mappend_rel_rw : f_rel_funct_db.
#[global] Hint Resolve mappend__mappend_rel_rw : rel_ax_db.
#[global] Instance mappend_lookup_rw : dictionary rwLem mappend := { 
	lookup' := mappend__mappend_rel_rw
}.
Theorem mappend__mappend_rel (lq_tmp0_r: MaybeInt) (lq_tmp1_r: MaybeInt) (VV: MaybeInt_u): ((⌊ mappend lq_tmp0_r lq_tmp1_r -⌋) = VV) <-> (mappend_rel (⌊ lq_tmp0_r -⌋) (⌊ lq_tmp1_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite mappend__mappend_rel : f_rel_funct_db.
Theorem mappend__mappend_rel' (lq_tmp0: MaybeInt_u) (lq_tmp1: MaybeInt_u) (lq_tmp0_r: MaybeInt) (lq_tmp1_r: MaybeInt) (VV: MaybeInt_u): (lq_tmp0 = (⌊ lq_tmp0_r -⌋)) -> ((lq_tmp1 = (⌊ lq_tmp1_r -⌋)) -> (((⌊ mappend lq_tmp0_r lq_tmp1_r -⌋) = VV) <-> (mappend_rel lq_tmp0 lq_tmp1 VV))). 
Proof. 
	intros -> ->. 
	refine (mappend__mappend_rel lq_tmp0_r lq_tmp1_r VV). 
Qed. 
#[global] Hint Resolve mappend__mappend_rel' : f_rel_funct_db.
Theorem mappend_rel_mk [lq_tmp0: MaybeInt_u] [lq_tmp1: MaybeInt_u] (lq_tmp0_p: (MaybeInt_wf lq_tmp0) /\ True) (lq_tmp1_p: (MaybeInt_wf lq_tmp1) /\ True): {VV: _ | mappend_rel lq_tmp0 lq_tmp1 VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (mappend_rel lq_tmp0 lq_tmp1 VV)) 
		(mappend (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p)) _); 
	rewrite <- mappend__mappend_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve mappend_rel_mk : f_rel_funct_db.
#[global] Instance mappendPack : (@Pack (MaybeInt ::RT (fun (lq_tmp0_r: MaybeInt) => (MaybeInt ::RT (fun (lq_tmp1_r: MaybeInt) => nilRT)))) (MaybeInt_u ::UT (MaybeInt_u ::UT nilUT)) (ltac: (mkProjectsArgListTG (MaybeInt ::RT (fun (lq_tmp0_r: MaybeInt) => (MaybeInt ::RT (fun (lq_tmp1_r: MaybeInt) => nilRT)))) (MaybeInt_u ::UT (MaybeInt_u ::UT nilUT)))) MaybeInt_u (fun (x_60657082: (ArgList MaybeInt ::RT (fun (lq_tmp0_r: MaybeInt) => (MaybeInt ::RT (fun (lq_tmp1_r: MaybeInt) => nilRT))))) => (fun (v_x_60657082: MaybeInt_u) => (ltac: (flattenP (fun (lq_tmp0_r: MaybeInt) => (fun (lq_tmp1_r: MaybeInt) => (fun (VV: MaybeInt_u) => ((MaybeInt_wf VV) /\ True)))) x_60657082 v_x_60657082))))).
Proof. 
	buildPackG mappend mappend_rel mappend__mappend_rel mappend_rel_funct. 
Defined.
Definition mappend_assoc_spec (xs: MaybeInt) (ys: MaybeInt) (zs: MaybeInt): Type := 
	{{forall (mappendres: MaybeInt_u), (mappend_rel (⌊ xs -⌋) (⌊ ys -⌋) mappendres) -> (forall (mappend_res_2: MaybeInt_u), (mappend_rel mappendres (⌊ zs -⌋) mappend_res_2) -> (forall (mappend_res_3: MaybeInt_u), (mappend_rel (⌊ ys -⌋) (⌊ zs -⌋) mappend_res_3) -> (forall (mappend_res_4: MaybeInt_u), (mappend_rel (⌊ xs -⌋) mappend_res_3 mappend_res_4) -> (mappend_res_2 == mappend_res_4))))}}. 
#[global] Hint Unfold mappend_assoc_spec : lia_unfold.
Theorem mappend_assoc (xs: MaybeInt) (ys: MaybeInt) (zs: MaybeInt): mappend_assoc_spec xs ys zs. 
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
Qed. 
Definition mempty_spec: Type := 
	MaybeInt. 
#[global] Hint Unfold mempty_spec : lia_unfold.
Definition mempty: mempty_spec. 
Proof. 
	refine (subsumptionCast _ _ Nothing _); 
	solver. 
Defined. 
Inductive mempty_rel : (MaybeInt_u -> Prop) := 
	 | mempty_def: mempty_rel Nothing_u. 
#[global] Hint Constructors mempty_rel : core_hint_db.
#[global] Instance mempty_lookup_rel : dictionary rel mempty := { 
	lookup' := mempty_rel
}.
#[global] Instance mempty_getF : getFunc mempty_rel := { 
	getF' := mempty
}.
Theorem mempty_rel_funct: (forall (VV: MaybeInt_u) (VV': MaybeInt_u) (H: mempty_rel VV) (K: mempty_rel VV') , VV = VV'). 
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
	Opaque mempty.
	existence_lemma_pre mempty; 
	fix_notations; 
	simpl in *. 
	Transparent mempty.
	all: existence_lemma_quicksolve mempty; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve mempty_rel_ex : rel_ax_db.
#[global] Opaque mempty. 
Theorem mempty__mempty_rel_rw (VV: MaybeInt_u): ((⌊ mempty -⌋) = VV) <-> (mempty_rel VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite mempty__mempty_rel_rw : f_rel_funct_db.
#[global] Hint Resolve mempty__mempty_rel_rw : rel_ax_db.
#[global] Instance mempty_lookup_rw : dictionary rwLem mempty := { 
	lookup' := mempty__mempty_rel_rw
}.
Theorem mempty__mempty_rel (VV: MaybeInt_u): ((⌊ mempty -⌋) = VV) <-> (mempty_rel VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite mempty__mempty_rel : f_rel_funct_db.
Theorem mempty__mempty_rel' (VV: MaybeInt_u): ((⌊ mempty -⌋) = VV) <-> (mempty_rel VV). 
Proof. 
	intros . 
	refine (mempty__mempty_rel VV). 
Qed. 
#[global] Hint Resolve mempty__mempty_rel' : f_rel_funct_db.
Theorem mempty_rel_mk: {VV: _ | mempty_rel VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (mempty_rel VV)) mempty _); 
	rewrite <- mempty__mempty_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve mempty_rel_mk : f_rel_funct_db.
Definition mempty_left_spec (x: MaybeInt): Type := 
	{{forall (mappendres: MaybeInt_u), (mappend_rel (⌊ mempty -⌋) (⌊ x -⌋) mappendres) -> (mappendres = (⌊ x -⌋))}}. 
#[global] Hint Unfold mempty_left_spec : lia_unfold.
Theorem mempty_left (x: MaybeInt): mempty_left_spec x. 
Proof. 
	destruct x as [x x_p]. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition mempty_right_spec (x: MaybeInt): Type := 
	{{forall (mappendres: MaybeInt_u), (mappend_rel (⌊ x -⌋) (⌊ mempty -⌋) mappendres) -> (mappendres = (⌊ x -⌋))}}. 
#[global] Hint Unfold mempty_right_spec : lia_unfold.
Theorem mempty_right (x: MaybeInt): mempty_right_spec x. 
Proof. 
	destruct x as [x x_p]. 
	induction x as [(*Just*) x | (*Nothing*) ]. 
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
Qed. 