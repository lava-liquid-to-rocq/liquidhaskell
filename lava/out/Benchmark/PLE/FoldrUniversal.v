From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Set Universe Polymorphism.
Inductive L_u : Type := 
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
Definition compose_spec (lq_tmp0: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_39721497: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))) => (fun (v_x_39721497: Z) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True)) x_39721497 v_x_39721497)))))) (lq_tmp3: (@Pack (L ::RT (fun (lq_tmp4: L) => nilRT)) (L_u ::UT nilUT) (ltac: (mkProjectsArgListTG (L ::RT (fun (lq_tmp4: L) => nilRT)) (L_u ::UT nilUT))) Z (fun (x_12632004: (ArgList L ::RT (fun (lq_tmp4: L) => nilRT))) => (fun (v_x_12632004: Z) => (ltac: (flattenP (fun (lq_tmp4: L) => (fun (VV: Z) => True)) x_12632004 v_x_12632004)))))) (lq_tmp6: L): Type := 
	{VV: Z | True}. 
#[global] Hint Unfold compose_spec : lia_unfold.
Definition compose (lq_tmp0: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_39721497: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))) => (fun (v_x_39721497: Z) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True)) x_39721497 v_x_39721497)))))) (lq_tmp3: (@Pack (L ::RT (fun (lq_tmp4: L) => nilRT)) (L_u ::UT nilUT) (ltac: (mkProjectsArgListTG (L ::RT (fun (lq_tmp4: L) => nilRT)) (L_u ::UT nilUT))) Z (fun (x_12632004: (ArgList L ::RT (fun (lq_tmp4: L) => nilRT))) => (fun (v_x_12632004: Z) => (ltac: (flattenP (fun (lq_tmp4: L) => (fun (VV: Z) => True)) x_12632004 v_x_12632004)))))) (lq_tmp6: L): compose_spec lq_tmp0 lq_tmp3 lq_tmp6. 
Proof. 
	destruct lq_tmp6 as [lq_tmp6 lq_tmp6_p]. 
	refine (subsumptionCast _ _ 
		((getPackF lq_tmp0) 
		(subsumptionCast Z (fun (lq_tmp1: Z) => True) 
		((getPackF lq_tmp3) 
		(exist (fun (lq_tmp4: L_u) => ((L_wf lq_tmp4) /\ True)) lq_tmp6 (ltac: (solver)))) (ltac: (solver)))) _); 
	solver. 
Defined. 
Inductive compose_rel : ((@uPack (Z ::UT nilUT) Z) -> ((@uPack (L_u ::UT nilUT) Z) -> (L_u -> (Z -> Prop)))) := 
	 | compose_def: (forall (lq_tmp0: @uPack (Z ::UT nilUT) Z) (lq_tmp3: @uPack (L_u ::UT nilUT) Z) lq_tmp6 , forall (lq_tmp3res: _), ((getUPackRel lq_tmp3) lq_tmp6 lq_tmp3res) -> (forall (lq_tmp0res: _), ((getUPackRel lq_tmp0) lq_tmp3res lq_tmp0res) -> (compose_rel lq_tmp0 lq_tmp3 lq_tmp6 lq_tmp0res))). 
#[global] Hint Constructors compose_rel : core_hint_db.
#[global] Instance compose_lookup_rel : dictionary rel compose := { 
	lookup' := compose_rel
}.
#[global] Instance compose_getF : getFunc compose_rel := { 
	getF' := compose
}.
Theorem compose_rel_funct [lq_tmp0: @uPack (Z ::UT nilUT) Z] [lq_tmp3: @uPack (L_u ::UT nilUT) Z] [lq_tmp6: L_u]: (forall (VV: Z) (VV': Z) (H: compose_rel lq_tmp0 lq_tmp3 lq_tmp6 VV) (K: compose_rel lq_tmp0 lq_tmp3 lq_tmp6 VV') , VV = VV'). 
Proof. 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve compose_rel_funct : f_rel_funct_db.
Theorem compose_def_lem (lq_tmp0: @uPack (Z ::UT nilUT) Z) (lq_tmp3: @uPack (L_u ::UT nilUT) Z) (lq_tmp6: _) (lq_tmp0res: _): (compose_rel lq_tmp0 lq_tmp3 lq_tmp6 lq_tmp0res) <-> (exists (lq_tmp3res: _), ((getUPackRel lq_tmp3) lq_tmp6 lq_tmp3res) /\ ((getUPackRel lq_tmp0) lq_tmp3res lq_tmp0res)). 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite compose_def_lem : f_rel_back.
Theorem compose_rel_ex (lq_tmp0: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_39721497: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))) => (fun (v_x_39721497: Z) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True)) x_39721497 v_x_39721497)))))) (lq_tmp3: (@Pack (L ::RT (fun (lq_tmp4: L) => nilRT)) (L_u ::UT nilUT) (ltac: (mkProjectsArgListTG (L ::RT (fun (lq_tmp4: L) => nilRT)) (L_u ::UT nilUT))) Z (fun (x_12632004: (ArgList L ::RT (fun (lq_tmp4: L) => nilRT))) => (fun (v_x_12632004: Z) => (ltac: (flattenP (fun (lq_tmp4: L) => (fun (VV: Z) => True)) x_12632004 v_x_12632004)))))) (lq_tmp6: L_u) (lq_tmp6_p: (L_wf lq_tmp6) /\ True): compose_rel (packProj lq_tmp0) (packProj lq_tmp3) lq_tmp6 (⌊ compose lq_tmp0 lq_tmp3 (exist _ lq_tmp6 lq_tmp6_p) -⌋). 
Proof. 
	Opaque compose.
	existence_lemma_pre compose; 
	fix_notations; 
	simpl in *. 
	Transparent compose.
	all: existence_lemma_quicksolve compose; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve compose_rel_ex : rel_ax_db.
#[global] Opaque compose. 
Theorem compose__compose_rel_rw (lq_tmp0: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_39721497: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))) => (fun (v_x_39721497: Z) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True)) x_39721497 v_x_39721497)))))) (lq_tmp3: (@Pack (L ::RT (fun (lq_tmp4: L) => nilRT)) (L_u ::UT nilUT) (ltac: (mkProjectsArgListTG (L ::RT (fun (lq_tmp4: L) => nilRT)) (L_u ::UT nilUT))) Z (fun (x_12632004: (ArgList L ::RT (fun (lq_tmp4: L) => nilRT))) => (fun (v_x_12632004: Z) => (ltac: (flattenP (fun (lq_tmp4: L) => (fun (VV: Z) => True)) x_12632004 v_x_12632004)))))) (lq_tmp6: L_u) (lq_tmp6_p: (L_wf lq_tmp6) /\ True) (VV: Z): ((⌊ compose lq_tmp0 lq_tmp3 (exist _ lq_tmp6 lq_tmp6_p) -⌋) = VV) <-> (compose_rel (packProj lq_tmp0) (packProj lq_tmp3) lq_tmp6 VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite compose__compose_rel_rw : f_rel_funct_db.
#[global] Hint Resolve compose__compose_rel_rw : rel_ax_db.
#[global] Instance compose_lookup_rw : dictionary rwLem compose := { 
	lookup' := compose__compose_rel_rw
}.
Theorem compose__compose_rel (lq_tmp0_r: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_39721497: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))) => (fun (v_x_39721497: Z) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True)) x_39721497 v_x_39721497)))))) (lq_tmp3_r: (@Pack (L ::RT (fun (lq_tmp4: L) => nilRT)) (L_u ::UT nilUT) (ltac: (mkProjectsArgListTG (L ::RT (fun (lq_tmp4: L) => nilRT)) (L_u ::UT nilUT))) Z (fun (x_12632004: (ArgList L ::RT (fun (lq_tmp4: L) => nilRT))) => (fun (v_x_12632004: Z) => (ltac: (flattenP (fun (lq_tmp4: L) => (fun (VV: Z) => True)) x_12632004 v_x_12632004)))))) (lq_tmp6_r: L) (VV: Z): ((⌊ compose lq_tmp0_r lq_tmp3_r lq_tmp6_r -⌋) = VV) <-> (compose_rel (packProj lq_tmp0_r) (packProj lq_tmp3_r) (⌊ lq_tmp6_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite compose__compose_rel : f_rel_funct_db.
Theorem compose__compose_rel' (lq_tmp0: @uPack (Z ::UT nilUT) Z) (lq_tmp3: @uPack (L_u ::UT nilUT) Z) (lq_tmp6: L_u) (lq_tmp0_r: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_39721497: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))) => (fun (v_x_39721497: Z) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True)) x_39721497 v_x_39721497)))))) (lq_tmp3_r: (@Pack (L ::RT (fun (lq_tmp4: L) => nilRT)) (L_u ::UT nilUT) (ltac: (mkProjectsArgListTG (L ::RT (fun (lq_tmp4: L) => nilRT)) (L_u ::UT nilUT))) Z (fun (x_12632004: (ArgList L ::RT (fun (lq_tmp4: L) => nilRT))) => (fun (v_x_12632004: Z) => (ltac: (flattenP (fun (lq_tmp4: L) => (fun (VV: Z) => True)) x_12632004 v_x_12632004)))))) (lq_tmp6_r: L) (VV: Z): (lq_tmp0 = (packProj lq_tmp0_r)) -> ((lq_tmp3 = (packProj lq_tmp3_r)) -> ((lq_tmp6 = (⌊ lq_tmp6_r -⌋)) -> (((⌊ compose lq_tmp0_r lq_tmp3_r lq_tmp6_r -⌋) = VV) <-> (compose_rel lq_tmp0 lq_tmp3 lq_tmp6 VV)))). 
Proof. 
	intros -> -> ->. 
	refine (compose__compose_rel lq_tmp0_r lq_tmp3_r lq_tmp6_r VV). 
Qed. 
#[global] Hint Resolve compose__compose_rel' : f_rel_funct_db.
Theorem compose_rel_mk [lq_tmp0: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_39721497: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))) => (fun (v_x_39721497: Z) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True)) x_39721497 v_x_39721497)))))] [lq_tmp3: (@Pack (L ::RT (fun (lq_tmp4: L) => nilRT)) (L_u ::UT nilUT) (ltac: (mkProjectsArgListTG (L ::RT (fun (lq_tmp4: L) => nilRT)) (L_u ::UT nilUT))) Z (fun (x_12632004: (ArgList L ::RT (fun (lq_tmp4: L) => nilRT))) => (fun (v_x_12632004: Z) => (ltac: (flattenP (fun (lq_tmp4: L) => (fun (VV: Z) => True)) x_12632004 v_x_12632004)))))] [lq_tmp6: L_u] (lq_tmp6_p: (L_wf lq_tmp6) /\ True): {VV: _ | compose_rel (packProj lq_tmp0) (packProj lq_tmp3) lq_tmp6 VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ 
		(fun (VV: _) => (compose_rel (packProj lq_tmp0) (packProj lq_tmp3) lq_tmp6 VV)) (compose lq_tmp0 lq_tmp3 (exist _ lq_tmp6 lq_tmp6_p)) _); 
	rewrite <- compose__compose_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve compose_rel_mk : f_rel_funct_db.
Definition foldr_spec (lq_tmp0: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)))) Z (fun (x_67570197: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT))))) => (fun (v_x_67570197: Z) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (lq_tmp2: {lq_tmp2: Z | True}) => (fun (VV: Z) => True))) x_67570197 v_x_67570197)))))) (lq_tmp4: {lq_tmp4: Z | True}) (lq_tmp5: L): Type := 
	{VV: Z | True}. 
#[global] Hint Unfold foldr_spec : lia_unfold.
Definition foldr (lq_tmp0: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)))) Z (fun (x_67570197: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT))))) => (fun (v_x_67570197: Z) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (lq_tmp2: {lq_tmp2: Z | True}) => (fun (VV: Z) => True))) x_67570197 v_x_67570197)))))) (lq_tmp4: {lq_tmp4: Z | True}) (lq_tmp5: L): foldr_spec lq_tmp0 lq_tmp4 lq_tmp5. 
Proof. 
	destruct lq_tmp4 as [lq_tmp4 lq_tmp4_p]. 
	destruct lq_tmp5 as [lq_tmp5 lq_tmp5_p]. 
	try revert lq_tmp4_p; generalize dependent lq_tmp4; try revert lq_tmp0_p; generalize dependent lq_tmp0; 
	induction lq_tmp5 as [(*C*) x xs IH_xs | (*Emp*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ 
		((getPackF lq_tmp0) (exist (fun (lq_tmp1: Z) => True) x (ltac: (solver))) 
		(subsumptionCast Z (fun (lq_tmp2: Z) => True) 
		(IH_xs (ltac: (try clear IH_xs; 
	solver)) lq_tmp0 lq_tmp4 (ltac: (try clear IH_xs; 
	solver))) (ltac: (solver)))) _); 
		solver.  
	  - intros . 
		refine (exist _ lq_tmp4 _); 
		solver.  
Defined. 
Inductive foldr_rel : ((@uPack (Z ::UT (Z ::UT nilUT)) Z) -> (Z -> (L_u -> (Z -> Prop)))) := 
	 | foldr_Emp: (forall (lq_tmp0: @uPack (Z ::UT (Z ::UT nilUT)) Z) lq_tmp4 , foldr_rel lq_tmp0 lq_tmp4 Emp_u lq_tmp4)
	 | foldr_C: (forall (lq_tmp0: @uPack (Z ::UT (Z ::UT nilUT)) Z) lq_tmp4 x xs , forall (foldrres: Z), (foldr_rel lq_tmp0 lq_tmp4 xs foldrres) -> (forall (lq_tmp0res: _), ((getUPackRel lq_tmp0) x foldrres lq_tmp0res) -> (foldr_rel lq_tmp0 lq_tmp4 (C_u x xs) lq_tmp0res))). 
#[global] Hint Constructors foldr_rel : core_hint_db.
#[global] Instance foldr_lookup_rel : dictionary rel foldr := { 
	lookup' := foldr_rel
}.
#[global] Instance foldr_getF : getFunc foldr_rel := { 
	getF' := foldr
}.
Theorem foldr_rel_funct [lq_tmp0: @uPack (Z ::UT (Z ::UT nilUT)) Z] [lq_tmp4: Z] [lq_tmp5: L_u]: (forall (VV: Z) (VV': Z) (H: foldr_rel lq_tmp0 lq_tmp4 lq_tmp5 VV) (K: foldr_rel lq_tmp0 lq_tmp4 lq_tmp5 VV') , VV = VV'). 
Proof. 
	try revert lq_tmp4_p; generalize dependent lq_tmp4; try revert lq_tmp0_p; generalize dependent lq_tmp0; 
	induction lq_tmp5 as [(*C*) x xs IH_xs | (*Emp*) ]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve foldr_rel_funct : f_rel_funct_db.
Theorem foldr_Emp_lem (lq_tmp0: @uPack (Z ::UT (Z ::UT nilUT)) Z) (lq_tmp4: _): (foldr_rel lq_tmp0 lq_tmp4 Emp_u lq_tmp4) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite foldr_Emp_lem : f_rel_back.
Theorem foldr_C_lem (lq_tmp0: @uPack (Z ::UT (Z ::UT nilUT)) Z) (lq_tmp4: _) (x: _) (xs: _) (lq_tmp0res: _): (foldr_rel lq_tmp0 lq_tmp4 (C_u x xs) lq_tmp0res) <-> (exists (foldrres: Z), (foldr_rel lq_tmp0 lq_tmp4 xs foldrres) /\ ((getUPackRel lq_tmp0) x foldrres lq_tmp0res)). 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite foldr_C_lem : f_rel_back.
Theorem foldr_rel_ex (lq_tmp0: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)))) Z (fun (x_67570197: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT))))) => (fun (v_x_67570197: Z) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (lq_tmp2: {lq_tmp2: Z | True}) => (fun (VV: Z) => True))) x_67570197 v_x_67570197)))))) (lq_tmp4: Z) (lq_tmp5: L_u) (lq_tmp4_p: True) (lq_tmp5_p: (L_wf lq_tmp5) /\ True): foldr_rel (packProj lq_tmp0) lq_tmp4 lq_tmp5 
		(⌊ foldr lq_tmp0 (exist _ lq_tmp4 lq_tmp4_p) (exist _ lq_tmp5 lq_tmp5_p) -⌋). 
Proof. 
	Opaque foldr.
	existence_lemma_pre foldr; 
	try revert lq_tmp4_p; generalize dependent lq_tmp4; try revert lq_tmp0_p; generalize dependent lq_tmp0; 
	induction lq_tmp5 as [(*C*) x xs IH_xs | (*Emp*) ]; 
	intros ; 
	[fix_notations; 
	pose proof (IH_xs (ltac: (try clear IH_xs; 
	solver)) lq_tmp0 lq_tmp4 (ltac: (try clear IH_xs; 
	solver))) as IH_42647660; 
	try clear IH_xs| 
	fix_notations]; 
	simpl in *. 
	Transparent foldr.
	all: existence_lemma_quicksolve foldr; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve foldr_rel_ex : rel_ax_db.
#[global] Opaque foldr. 
Theorem foldr__foldr_rel_rw (lq_tmp0: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)))) Z (fun (x_67570197: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT))))) => (fun (v_x_67570197: Z) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (lq_tmp2: {lq_tmp2: Z | True}) => (fun (VV: Z) => True))) x_67570197 v_x_67570197)))))) (lq_tmp4: Z) (lq_tmp5: L_u) (lq_tmp4_p: True) (lq_tmp5_p: (L_wf lq_tmp5) /\ True) (VV: Z): ((⌊ foldr lq_tmp0 (exist _ lq_tmp4 lq_tmp4_p) (exist _ lq_tmp5 lq_tmp5_p) -⌋) = VV) <-> (foldr_rel (packProj lq_tmp0) lq_tmp4 lq_tmp5 VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite foldr__foldr_rel_rw : f_rel_funct_db.
#[global] Hint Resolve foldr__foldr_rel_rw : rel_ax_db.
#[global] Instance foldr_lookup_rw : dictionary rwLem foldr := { 
	lookup' := foldr__foldr_rel_rw
}.
Theorem foldr__foldr_rel (lq_tmp0_r: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)))) Z (fun (x_67570197: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT))))) => (fun (v_x_67570197: Z) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (lq_tmp2: {lq_tmp2: Z | True}) => (fun (VV: Z) => True))) x_67570197 v_x_67570197)))))) (lq_tmp4_r: {lq_tmp4: Z | True}) (lq_tmp5_r: L) (VV: Z): ((⌊ foldr lq_tmp0_r lq_tmp4_r lq_tmp5_r -⌋) = VV) <-> (foldr_rel (packProj lq_tmp0_r) (⌊ lq_tmp4_r -⌋) (⌊ lq_tmp5_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite foldr__foldr_rel : f_rel_funct_db.
Theorem foldr__foldr_rel' (lq_tmp0: @uPack (Z ::UT (Z ::UT nilUT)) Z) (lq_tmp4: Z) (lq_tmp5: L_u) (lq_tmp0_r: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)))) Z (fun (x_67570197: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT))))) => (fun (v_x_67570197: Z) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (lq_tmp2: {lq_tmp2: Z | True}) => (fun (VV: Z) => True))) x_67570197 v_x_67570197)))))) (lq_tmp4_r: {lq_tmp4: Z | True}) (lq_tmp5_r: L) (VV: Z): (lq_tmp0 = (packProj lq_tmp0_r)) -> ((lq_tmp4 = (⌊ lq_tmp4_r -⌋)) -> ((lq_tmp5 = (⌊ lq_tmp5_r -⌋)) -> (((⌊ foldr lq_tmp0_r lq_tmp4_r lq_tmp5_r -⌋) = VV) <-> (foldr_rel lq_tmp0 lq_tmp4 lq_tmp5 VV)))). 
Proof. 
	intros -> -> ->. 
	refine (foldr__foldr_rel lq_tmp0_r lq_tmp4_r lq_tmp5_r VV). 
Qed. 
#[global] Hint Resolve foldr__foldr_rel' : f_rel_funct_db.
Theorem foldr_rel_mk [lq_tmp0: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)))) Z (fun (x_67570197: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT))))) => (fun (v_x_67570197: Z) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (lq_tmp2: {lq_tmp2: Z | True}) => (fun (VV: Z) => True))) x_67570197 v_x_67570197)))))] [lq_tmp4: Z] [lq_tmp5: L_u] (lq_tmp4_p: True) (lq_tmp5_p: (L_wf lq_tmp5) /\ True): {VV: _ | foldr_rel (packProj lq_tmp0) lq_tmp4 lq_tmp5 VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ 
		(fun (VV: _) => (foldr_rel (packProj lq_tmp0) lq_tmp4 lq_tmp5 VV)) 
		(foldr lq_tmp0 (exist _ lq_tmp4 lq_tmp4_p) (exist _ lq_tmp5 lq_tmp5_p)) _); 
	rewrite <- foldr__foldr_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve foldr_rel_mk : f_rel_funct_db.
Definition foldrUniversal_spec (f: (@Pack ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)) (ltac: (mkProjectsArgListTG ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)))) Z (fun (x_33150792: (ArgList {lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))))) => (fun (v_x_33150792: Z) => (ltac: (flattenP (fun (lq_tmp0: {lq_tmp0: Z | True}) => (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True))) x_33150792 v_x_33150792)))))) (h: (@Pack (L ::RT (fun (lq_tmp3: L) => nilRT)) (L_u ::UT nilUT) (ltac: (mkProjectsArgListTG (L ::RT (fun (lq_tmp3: L) => nilRT)) (L_u ::UT nilUT))) Z (fun (x_72943783: (ArgList L ::RT (fun (lq_tmp3: L) => nilRT))) => (fun (v_x_72943783: Z) => (ltac: (flattenP (fun (lq_tmp3: L) => (fun (VV: Z) => True)) x_72943783 v_x_72943783)))))) (e: {e: Z | True}) (ys: L) (base: {{exists (hres: _), ((getPackRel h) Emp_u hres) /\ (hres = (⌊ e -⌋))}}) (step: (forall (x: {x: Z | True}) (xs: L) , {{exists (hres: _), ((getPackRel h) (C_u (⌊ x -⌋) (⌊ xs -⌋)) hres) /\ (exists (h_res_2: _), ((getPackRel h) (⌊ xs -⌋) h_res_2) /\ (exists (fres: _), ((getPackRel f) (⌊ x -⌋) h_res_2 fres) /\ (hres == fres)))}})): Type := 
	{{exists (hres: _), ((getPackRel h) (⌊ ys -⌋) hres) /\ (exists (foldrres: Z), (foldr_rel (packProj f) (⌊ e -⌋) (⌊ ys -⌋) foldrres) /\ (hres == foldrres))}}. 
#[global] Hint Unfold foldrUniversal_spec : lia_unfold.
Theorem foldrUniversal (f: (@Pack ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)) (ltac: (mkProjectsArgListTG ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)))) Z (fun (x_33150792: (ArgList {lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))))) => (fun (v_x_33150792: Z) => (ltac: (flattenP (fun (lq_tmp0: {lq_tmp0: Z | True}) => (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True))) x_33150792 v_x_33150792)))))) (h: (@Pack (L ::RT (fun (lq_tmp3: L) => nilRT)) (L_u ::UT nilUT) (ltac: (mkProjectsArgListTG (L ::RT (fun (lq_tmp3: L) => nilRT)) (L_u ::UT nilUT))) Z (fun (x_72943783: (ArgList L ::RT (fun (lq_tmp3: L) => nilRT))) => (fun (v_x_72943783: Z) => (ltac: (flattenP (fun (lq_tmp3: L) => (fun (VV: Z) => True)) x_72943783 v_x_72943783)))))) (e: {e: Z | True}) (ys: L) (base: {{exists (hres: _), ((getPackRel h) Emp_u hres) /\ (hres = (⌊ e -⌋))}}) (step: (forall (x: {x: Z | True}) (xs: L) , {{exists (hres: _), ((getPackRel h) (C_u (⌊ x -⌋) (⌊ xs -⌋)) hres) /\ (exists (h_res_2: _), ((getPackRel h) (⌊ xs -⌋) h_res_2) /\ (exists (fres: _), ((getPackRel f) (⌊ x -⌋) h_res_2 fres) /\ (hres == fres)))}})): foldrUniversal_spec f h e ys base step. 
Proof. 
	destruct e as [e e_p]. 
	destruct ys as [ys ys_p]. 
	destruct base as [base base_p]. 
	try revert step_p; generalize dependent step; try revert base_p; generalize dependent base; try revert e_p; generalize dependent e; try revert h_p; generalize dependent h; try revert f_p; generalize dependent f; 
	induction ys as [(*C*) x xs IH_xs | (*Emp*) ]. 
	  - intros . 
		pose proof (IH_xs (ltac: (try clear IH_xs; 
	solver)) f h e (ltac: (try clear IH_xs; 
	solver)) base (ltac: (try clear IH_xs; 
	solver)) step) as H_42980961. 
		simpl in H_42980961. 
		refine (subsumptionCast _ _ 
		(step (exist (fun (x: Z) => True) x (ltac: (solver))) 
		(exist (fun (xs: L_u) => ((L_wf xs) /\ True)) xs (ltac: (solver)))) _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
Qed. 