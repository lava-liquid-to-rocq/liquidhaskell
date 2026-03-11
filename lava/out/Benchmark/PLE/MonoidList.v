From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Inductive L_u : Set := 
	 | C_u: Z -> (L_u -> L_u)
	 | Emp_u: L_u. 
Fixpoint L_eq (x: L_u) (y: L_u): bool := 
	match (x, y) with (C_u x x_1, C_u x' x_1') => ((true && (x ==? x')) && (L_eq x_1 x_1')) | (Emp_u, Emp_u) => true | (_, _) => false end. 
Theorem L_eq_refl: (forall (x: L_u) , is_true (L_eq x x)). 
Proof. 
	eq_refl_rec. 
Qed. 
#[global] Hint Resolve L_eq_refl : eq_hint_db.
Theorem L_eqb_eq: (forall (s: L_u) (t: L_u) , (is_true (L_eq s t)) -> (s = t)). 
Proof. 
	eqb_eq_lem. 
Qed. 
#[global] Hint Resolve L_eqb_eq : eq_hint_db.
#[global] Instance leibnitz_eq_L : LeibnitzEqB := { 
	equalB' := L_eq;
	refl' := L_eq_refl;
	eqb_eq' := L_eqb_eq
}.
Fixpoint L_wf (x: L_u): Prop := 
	match x with (C_u VV VV_) => ((L_wf VV_) /\ True) | Emp_u => True end. 
Theorem L_wf_ref [p: L_u -> Prop] (tm: {v: L_u | (L_wf v) /\ (p v)}): L_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation L := {x: L_u | (L_wf x) /\ True}. 
Definition C_lem (VV: {VV: Z | True}) (VV_: L): (L_wf (C_u (⌊ VV -⌋) (⌊ VV_ -⌋))) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition C (VV: {VV: Z | True}) (VV_: L): L := 
	exist _ (C_u (⌊ VV -⌋) (⌊ VV_ -⌋)) (C_lem VV VV_). 
Definition Emp_lem: (L_wf Emp_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Emp: L := 
	exist _ Emp_u Emp_lem. 
Definition wf_C_VV_ [VV: Z] [VV_: L_u] (p: L_wf (C_u VV VV_)): L_wf VV_. 
Proof. 
	quicksolve. 
Defined. 
#[global] Hint Resolve L_wf_ref : wf_constr_db.
#[global] Hint Unfold L_wf : wf_constr_db.
#[global] Hint Resolve L_eq : ref_constr_db.
#[global] Hint Resolve wf_C_VV_ : ref_constr_db.
#[global] Hint Unfold C : ref_constr_db.
#[global] Hint Unfold Emp : ref_constr_db.
Definition mappend (lq_tmp0: L) (lq_tmp1: L): L. 
Proof. 
	destruct lq_tmp0 as [lq_tmp0 lq_tmp0_p]. 
	destruct lq_tmp1 as [lq_tmp1 lq_tmp1_p]. 
	try revert lq_tmp1_p; generalize dependent lq_tmp1; 
	induction lq_tmp0 as [(*C*) x xs IH_xs | (*Emp*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ 
		(C (exist (fun (VV: Z) => True) x (ltac: (solver))) 
		(IH_xs (ltac: (try clear IH_xs; 
	solver)) lq_tmp1 (ltac: (try clear IH_xs; 
	solver)))) _); 
		solver.  
	  - intros . 
		refine (exist _ lq_tmp1 _); 
		solver.  
Defined. 
Inductive mappend_rel : (L_u -> (L_u -> (L_u -> Prop))) := 
	 | mappend_Emp: (forall lq_tmp1 , mappend_rel Emp_u lq_tmp1 lq_tmp1)
	 | mappend_C: (forall lq_tmp1 x xs , forall (mappendres: L_u), (mappend_rel xs lq_tmp1 mappendres) -> (mappend_rel (C_u x xs) lq_tmp1 (C_u x mappendres))). 
#[global] Hint Constructors mappend_rel : core_hint_db.
#[global] Instance mappend_lookup_rel : dictionary rel mappend := { 
	lookup' := mappend_rel
}.
#[global] Instance mappend_getF : getFunc mappend_rel := { 
	getF' := mappend
}.
Theorem mappend_rel_funct [lq_tmp0: L_u] [lq_tmp1: L_u]: (forall (VV: L_u) (VV': L_u) (H: mappend_rel lq_tmp0 lq_tmp1 VV) (K: mappend_rel lq_tmp0 lq_tmp1 VV') , VV = VV'). 
Proof. 
	try revert lq_tmp1_p; generalize dependent lq_tmp1; 
	induction lq_tmp0 as [(*C*) x xs IH_xs | (*Emp*) ]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve mappend_rel_funct : f_rel_funct_db.
Theorem mappend_Emp_lem (lq_tmp1: _): (mappend_rel Emp_u lq_tmp1 lq_tmp1) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite mappend_Emp_lem : f_rel_back.
Theorem mappend_C_lem (x: _) (xs: _) (lq_tmp1: _) (mappendres: L_u) (h_52086863: mappend_rel xs lq_tmp1 mappendres): (mappend_rel (C_u x xs) lq_tmp1 (C_u x mappendres)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite mappend_C_lem : f_rel_back.
Theorem mappend_rel_ex (lq_tmp0: L_u) (lq_tmp1: L_u) (lq_tmp0_p: (L_wf lq_tmp0) /\ True) (lq_tmp1_p: (L_wf lq_tmp1) /\ True): mappend_rel lq_tmp0 lq_tmp1 
		(⌊ mappend (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p) -⌋). 
Proof. 
	Opaque mappend.
	existence_lemma_pre mappend; 
	try revert lq_tmp1_p; generalize dependent lq_tmp1; 
	induction lq_tmp0 as [(*C*) x xs IH_xs | (*Emp*) ]; 
	intros ; 
	[fix_notations; 
	pose proof (IH_xs (ltac: (try clear IH_xs; 
	solver)) lq_tmp1 (ltac: (try clear IH_xs; 
	solver))) as IH_63046731; 
	try clear IH_xs| 
	fix_notations]; 
	simpl in *. 
	Transparent mappend.
	all: existence_lemma_quicksolve mappend; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve mappend_rel_ex : rel_ax_db.
#[global] Opaque mappend. 
Theorem mappend__mappend_rel_rw (lq_tmp0: L_u) (lq_tmp1: L_u) (lq_tmp0_p: (L_wf lq_tmp0) /\ True) (lq_tmp1_p: (L_wf lq_tmp1) /\ True) (VV: L_u): ((⌊ mappend (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p) -⌋) = VV) <-> (mappend_rel lq_tmp0 lq_tmp1 VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite mappend__mappend_rel_rw : f_rel_funct_db.
#[global] Hint Resolve mappend__mappend_rel_rw : rel_ax_db.
#[global] Instance mappend_lookup_rw : dictionary rwLem mappend := { 
	lookup' := mappend__mappend_rel_rw
}.
Theorem mappend__mappend_rel (lq_tmp0_r: L) (lq_tmp1_r: L) (VV: L_u): ((⌊ mappend lq_tmp0_r lq_tmp1_r -⌋) = VV) <-> (mappend_rel (⌊ lq_tmp0_r -⌋) (⌊ lq_tmp1_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite mappend__mappend_rel : f_rel_funct_db.
Theorem mappend__mappend_rel' (lq_tmp0: L_u) (lq_tmp1: L_u) (lq_tmp0_r: L) (lq_tmp1_r: L) (VV: L_u): (lq_tmp0 = (⌊ lq_tmp0_r -⌋)) -> ((lq_tmp1 = (⌊ lq_tmp1_r -⌋)) -> (((⌊ mappend lq_tmp0_r lq_tmp1_r -⌋) = VV) <-> (mappend_rel lq_tmp0 lq_tmp1 VV))). 
Proof. 
	intros -> ->. 
	refine (mappend__mappend_rel lq_tmp0_r lq_tmp1_r VV). 
Qed. 
#[global] Hint Resolve mappend__mappend_rel' : f_rel_funct_db.
Theorem mappend_rel_mk [lq_tmp0: L_u] [lq_tmp1: L_u] (lq_tmp0_p: (L_wf lq_tmp0) /\ True) (lq_tmp1_p: (L_wf lq_tmp1) /\ True): {VV: _ | mappend_rel lq_tmp0 lq_tmp1 VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (mappend_rel lq_tmp0 lq_tmp1 VV)) 
		(mappend (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p)) _); 
	rewrite <- mappend__mappend_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve mappend_rel_mk : f_rel_funct_db.
#[global] Instance mappendPack : (@Pack (L ::RT (fun (lq_tmp0_r: L) => (L ::RT (fun (lq_tmp1_r: L) => nilRT)))) (L_u ::UT (L_u ::UT nilUT)) (ltac: (mkProjectsArgListTG (L ::RT (fun (lq_tmp0_r: L) => (L ::RT (fun (lq_tmp1_r: L) => nilRT)))) (L_u ::UT (L_u ::UT nilUT)))) L_u (fun (x_46281847: (ArgList L ::RT (fun (lq_tmp0_r: L) => (L ::RT (fun (lq_tmp1_r: L) => nilRT))))) => (fun (v_x_46281847: L_u) => (ltac: (flattenP (fun (lq_tmp0_r: L) => (fun (lq_tmp1_r: L) => (fun (VV: L_u) => ((L_wf VV) /\ True)))) x_46281847 v_x_46281847))))).
Proof. 
	buildPackG mappend mappend_rel mappend__mappend_rel mappend_rel_funct. 
Defined.
Theorem mappend_assoc (xs: L) (ys: L) (zs: L): {{forall (mappendres: L_u), (mappend_rel (⌊ xs -⌋) (⌊ ys -⌋) mappendres) -> (forall (mappend_res_2: L_u), (mappend_rel mappendres (⌊ zs -⌋) mappend_res_2) -> (forall (mappend_res_3: L_u), (mappend_rel (⌊ ys -⌋) (⌊ zs -⌋) mappend_res_3) -> (forall (mappend_res_4: L_u), (mappend_rel (⌊ xs -⌋) mappend_res_3 mappend_res_4) -> (mappend_res_2 == mappend_res_4))))}}. 
Proof. 
	destruct xs as [xs xs_p]. 
	destruct ys as [ys ys_p]. 
	destruct zs as [zs zs_p]. 
	try revert zs_p; generalize dependent zs; try revert ys_p; generalize dependent ys; 
	induction xs as [(*C*) x xs IH_xs | (*Emp*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ 
		(IH_xs (ltac: (try clear IH_xs; 
	solver)) ys (ltac: (try clear IH_xs; 
	solver)) zs (ltac: (try clear IH_xs; 
	solver))) _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
Qed. 
Definition mempty: L. 
Proof. 
	refine (subsumptionCast _ _ Emp _); 
	solver. 
Defined. 
Inductive mempty_rel : (L_u -> Prop) := 
	 | mempty_def: mempty_rel Emp_u. 
#[global] Hint Constructors mempty_rel : core_hint_db.
#[global] Instance mempty_lookup_rel : dictionary rel mempty := { 
	lookup' := mempty_rel
}.
#[global] Instance mempty_getF : getFunc mempty_rel := { 
	getF' := mempty
}.
Theorem mempty_rel_funct: (forall (VV: L_u) (VV': L_u) (H: mempty_rel VV) (K: mempty_rel VV') , VV = VV'). 
Proof. 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve mempty_rel_funct : f_rel_funct_db.
Theorem mempty_def_lem: (mempty_rel Emp_u) <-> True. 
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
Theorem mempty__mempty_rel_rw (VV: L_u): ((⌊ mempty -⌋) = VV) <-> (mempty_rel VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite mempty__mempty_rel_rw : f_rel_funct_db.
#[global] Hint Resolve mempty__mempty_rel_rw : rel_ax_db.
#[global] Instance mempty_lookup_rw : dictionary rwLem mempty := { 
	lookup' := mempty__mempty_rel_rw
}.
Theorem mempty__mempty_rel (VV: L_u): ((⌊ mempty -⌋) = VV) <-> (mempty_rel VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite mempty__mempty_rel : f_rel_funct_db.
Theorem mempty__mempty_rel' (VV: L_u): ((⌊ mempty -⌋) = VV) <-> (mempty_rel VV). 
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
Theorem mempty_left (x: L): {{forall (mappendres: L_u), (mappend_rel (⌊ mempty -⌋) (⌊ x -⌋) mappendres) -> (mappendres = (⌊ x -⌋))}}. 
Proof. 
	destruct x as [x x_p]. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Theorem mempty_right (x: L): {{forall (mappendres: L_u), (mappend_rel (⌊ x -⌋) (⌊ mempty -⌋) mappendres) -> (mappendres = (⌊ x -⌋))}}. 
Proof. 
	destruct x as [x x_p]. 
	induction x as [(*C*) x xs IH_xs | (*Emp*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ (IH_xs (ltac: (try clear IH_xs; 
	solver))) _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
Qed. 