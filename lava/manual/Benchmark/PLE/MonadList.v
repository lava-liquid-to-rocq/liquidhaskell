From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
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
Definition append (lq_tmp0: L) (lq_tmp1: L): L. 
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
Inductive append_rel : (L_u -> (L_u -> (L_u -> Prop))) := 
	 | append_Emp: (forall lq_tmp1 , append_rel Emp_u lq_tmp1 lq_tmp1)
	 | append_C: (forall lq_tmp1 x xs , forall (appendres: L_u), (append_rel xs lq_tmp1 appendres) -> (append_rel (C_u x xs) lq_tmp1 (C_u x appendres))). 
#[global] Hint Constructors append_rel : core_hint_db.
#[global] Instance append_lookup_rel : dictionary rel append := { 
	lookup' := append_rel
}.
#[global] Instance append_getF : getFunc append_rel := { 
	getF' := append
}.
Theorem append_rel_funct [lq_tmp0: L_u] [lq_tmp1: L_u]: (forall (VV: L_u) (VV': L_u) (H: append_rel lq_tmp0 lq_tmp1 VV) (K: append_rel lq_tmp0 lq_tmp1 VV') , VV = VV'). 
Proof. 
	try revert lq_tmp1_p; generalize dependent lq_tmp1; 
	induction lq_tmp0 as [(*C*) x xs IH_xs | (*Emp*) ]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve append_rel_funct : f_rel_funct_db.
Theorem append_Emp_lem (lq_tmp1: _): (append_rel Emp_u lq_tmp1 lq_tmp1) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite append_Emp_lem : f_rel_back.
Theorem append_C_lem (x: _) (xs: _) (lq_tmp1: _) (appendres: L_u) (h_86920335: append_rel xs lq_tmp1 appendres): (append_rel (C_u x xs) lq_tmp1 (C_u x appendres)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite append_C_lem : f_rel_back.
Theorem append_rel_ex (lq_tmp0: L_u) (lq_tmp1: L_u) (lq_tmp0_p: (L_wf lq_tmp0) /\ True) (lq_tmp1_p: (L_wf lq_tmp1) /\ True): append_rel lq_tmp0 lq_tmp1 
		(⌊ append (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p) -⌋). 
Proof. 
	Opaque append.
	existence_lemma_pre append; 
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
	Transparent append.
	all: existence_lemma_quicksolve append; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve append_rel_ex : rel_ax_db.
#[global] Opaque append. 
Theorem append__append_rel_rw (lq_tmp0: L_u) (lq_tmp1: L_u) (lq_tmp0_p: (L_wf lq_tmp0) /\ True) (lq_tmp1_p: (L_wf lq_tmp1) /\ True) (VV: L_u): ((⌊ append (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p) -⌋) = VV) <-> (append_rel lq_tmp0 lq_tmp1 VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite append__append_rel_rw : f_rel_funct_db.
#[global] Hint Resolve append__append_rel_rw : rel_ax_db.
#[global] Instance append_lookup_rw : dictionary rwLem append := { 
	lookup' := append__append_rel_rw
}.
Theorem append__append_rel (lq_tmp0_r: L) (lq_tmp1_r: L) (VV: L_u): ((⌊ append lq_tmp0_r lq_tmp1_r -⌋) = VV) <-> (append_rel (⌊ lq_tmp0_r -⌋) (⌊ lq_tmp1_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite append__append_rel : f_rel_funct_db.
Theorem append__append_rel' (lq_tmp0: L_u) (lq_tmp1: L_u) (lq_tmp0_r: L) (lq_tmp1_r: L) (VV: L_u): (lq_tmp0 = (⌊ lq_tmp0_r -⌋)) -> ((lq_tmp1 = (⌊ lq_tmp1_r -⌋)) -> (((⌊ append lq_tmp0_r lq_tmp1_r -⌋) = VV) <-> (append_rel lq_tmp0 lq_tmp1 VV))). 
Proof. 
	intros -> ->. 
	refine (append__append_rel lq_tmp0_r lq_tmp1_r VV). 
Qed. 
#[global] Hint Resolve append__append_rel' : f_rel_funct_db.
Theorem append_rel_mk [lq_tmp0: L_u] [lq_tmp1: L_u] (lq_tmp0_p: (L_wf lq_tmp0) /\ True) (lq_tmp1_p: (L_wf lq_tmp1) /\ True): {VV: _ | append_rel lq_tmp0 lq_tmp1 VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (append_rel lq_tmp0 lq_tmp1 VV)) 
		(append (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p)) _); 
	rewrite <- append__append_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve append_rel_mk : f_rel_funct_db.
#[global] Instance appendPack : (@Pack (L ::RT (fun (lq_tmp0_r: L) => (L ::RT (fun (lq_tmp1_r: L) => nilRT)))) (L_u ::UT (L_u ::UT nilUT)) (ltac: (mkProjectsArgListTG (L ::RT (fun (lq_tmp0_r: L) => (L ::RT (fun (lq_tmp1_r: L) => nilRT)))) (L_u ::UT (L_u ::UT nilUT)))) L_u (fun (x_46281847: (ArgList L ::RT (fun (lq_tmp0_r: L) => (L ::RT (fun (lq_tmp1_r: L) => nilRT))))) => (fun (v_x_46281847: L_u) => (ltac: (flattenP (fun (lq_tmp0_r: L) => (fun (lq_tmp1_r: L) => (fun (VV: L_u) => ((L_wf VV) /\ True)))) x_46281847 v_x_46281847))))).
Proof. 
	buildPackG append append_rel append__append_rel append_rel_funct. 
Defined.
Definition bind (lq_tmp0: L) (lq_tmp1: (@Pack ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT))) L_u (fun (x_61572807: (ArgList {lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT))) => (fun (v_x_61572807: L_u) => (ltac: (flattenP (fun (lq_tmp2: {lq_tmp2: Z | True}) => (fun (VV: L_u) => ((L_wf VV) /\ True))) x_61572807 v_x_61572807)))))): L. 
Proof. 
	destruct lq_tmp0 as [lq_tmp0 lq_tmp0_p]. 
	try revert lq_tmp1_p; generalize dependent lq_tmp1; 
	induction lq_tmp0 as [(*C*) x xs IH_xs | (*Emp*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ 
		(append 
		(subsumptionCast L_u (fun (lq_tmp0: L_u) => ((L_wf lq_tmp0) /\ True)) 
		((getPackF lq_tmp1) (exist (fun (lq_tmp2: Z) => True) x (ltac: (solver)))) (ltac: (solver))) 
		(subsumptionCast L_u (fun (lq_tmp1: L_u) => ((L_wf lq_tmp1) /\ True)) (IH_xs (ltac: (try clear IH_xs; 
	solver)) lq_tmp1) (ltac: (solver)))) _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ Emp _); 
		solver.  
Defined. 
Polymorphic Inductive bind_rel : (L_u -> ((@uPack (Z ::UT nilUT) L_u) -> (L_u -> Prop))) := 
	 | bind_Emp: (forall (lq_tmp1: @uPack (Z ::UT nilUT) L_u) , bind_rel Emp_u lq_tmp1 Emp_u)
	 | bind_C: (forall (lq_tmp1: @uPack (Z ::UT nilUT) L_u) x xs , forall (bindres: L_u), (bind_rel xs lq_tmp1 bindres) -> (forall (lq_tmp1res: _), ((getUPackRel lq_tmp1) x lq_tmp1res) -> (forall (appendres: L_u), (append_rel lq_tmp1res bindres appendres) -> (bind_rel (C_u x xs) lq_tmp1 appendres)))). 
#[global] Hint Constructors bind_rel : core_hint_db.
#[global] Instance bind_lookup_rel : dictionary rel bind := { 
	lookup' := bind_rel
}.
#[global] Instance bind_getF : getFunc bind_rel := { 
	getF' := bind
}.
Theorem bind_rel_funct [lq_tmp0: L_u] [lq_tmp1: @uPack (Z ::UT nilUT) L_u]: (forall (VV: L_u) (VV': L_u) (H: bind_rel lq_tmp0 lq_tmp1 VV) (K: bind_rel lq_tmp0 lq_tmp1 VV') , VV = VV'). 
Proof. 
	try revert lq_tmp1_p; generalize dependent lq_tmp1; 
	induction lq_tmp0 as [(*C*) x xs IH_xs | (*Emp*) ]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve bind_rel_funct : f_rel_funct_db.
Theorem bind_Emp_lem (lq_tmp1: @uPack (Z ::UT nilUT) L_u): (bind_rel Emp_u lq_tmp1 Emp_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite bind_Emp_lem : f_rel_back.
Theorem bind_C_lem (x: _) (xs: _) (lq_tmp1: @uPack (Z ::UT nilUT) L_u) (appendres: L_u): (bind_rel (C_u x xs) lq_tmp1 appendres) <-> (exists (bindres: L_u), (bind_rel xs lq_tmp1 bindres) /\ (exists (lq_tmp1res: _), ((getUPackRel lq_tmp1) x lq_tmp1res) /\ (append_rel lq_tmp1res bindres appendres))). 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite bind_C_lem : f_rel_back.
Theorem bind_rel_ex (lq_tmp0: L_u) (lq_tmp1: (@Pack ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT))) L_u (fun (x_61572807: (ArgList {lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT))) => (fun (v_x_61572807: L_u) => (ltac: (flattenP (fun (lq_tmp2: {lq_tmp2: Z | True}) => (fun (VV: L_u) => ((L_wf VV) /\ True))) x_61572807 v_x_61572807)))))) (lq_tmp0_p: (L_wf lq_tmp0) /\ True): bind_rel lq_tmp0 (packProj lq_tmp1) (⌊ bind (exist _ lq_tmp0 lq_tmp0_p) lq_tmp1 -⌋). 
Proof. 
	Opaque bind.
	existence_lemma_pre bind; 
	try revert lq_tmp1_p; generalize dependent lq_tmp1; 
	induction lq_tmp0 as [(*C*) x xs IH_xs | (*Emp*) ]; 
	intros ; 
	[fix_notations; 
	pose proof (IH_xs (ltac: (try clear IH_xs; 
	solver)) lq_tmp1) as IH_72941671; 
	try clear IH_xs| 
	fix_notations]; 
	simpl in *. 
	Transparent bind.
	all: existence_lemma_quicksolve bind; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve bind_rel_ex : rel_ax_db.
#[global] Opaque bind. 
Theorem bind__bind_rel_rw (lq_tmp0: L_u) (lq_tmp1: (@Pack ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT))) L_u (fun (x_61572807: (ArgList {lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT))) => (fun (v_x_61572807: L_u) => (ltac: (flattenP (fun (lq_tmp2: {lq_tmp2: Z | True}) => (fun (VV: L_u) => ((L_wf VV) /\ True))) x_61572807 v_x_61572807)))))) (lq_tmp0_p: (L_wf lq_tmp0) /\ True) (VV: L_u): ((⌊ bind (exist _ lq_tmp0 lq_tmp0_p) lq_tmp1 -⌋) = VV) <-> (bind_rel lq_tmp0 (packProj lq_tmp1) VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite bind__bind_rel_rw : f_rel_funct_db.
#[global] Hint Resolve bind__bind_rel_rw : rel_ax_db.
#[global] Instance bind_lookup_rw : dictionary rwLem bind := { 
	lookup' := bind__bind_rel_rw
}.
Theorem bind__bind_rel (lq_tmp0_r: L) (lq_tmp1_r: (@Pack ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT))) L_u (fun (x_61572807: (ArgList {lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT))) => (fun (v_x_61572807: L_u) => (ltac: (flattenP (fun (lq_tmp2: {lq_tmp2: Z | True}) => (fun (VV: L_u) => ((L_wf VV) /\ True))) x_61572807 v_x_61572807)))))) (VV: L_u): ((⌊ bind lq_tmp0_r lq_tmp1_r -⌋) = VV) <-> (bind_rel (⌊ lq_tmp0_r -⌋) (packProj lq_tmp1_r) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite bind__bind_rel : f_rel_funct_db.
Theorem bind__bind_rel' (lq_tmp0: L_u) (lq_tmp1: @uPack (Z ::UT nilUT) L_u) (lq_tmp0_r: L) (lq_tmp1_r: (@Pack ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT))) L_u (fun (x_61572807: (ArgList {lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT))) => (fun (v_x_61572807: L_u) => (ltac: (flattenP (fun (lq_tmp2: {lq_tmp2: Z | True}) => (fun (VV: L_u) => ((L_wf VV) /\ True))) x_61572807 v_x_61572807)))))) (VV: L_u): (lq_tmp0 = (⌊ lq_tmp0_r -⌋)) -> ((lq_tmp1 = (packProj lq_tmp1_r)) -> (((⌊ bind lq_tmp0_r lq_tmp1_r -⌋) = VV) <-> (bind_rel lq_tmp0 lq_tmp1 VV))). 
Proof. 
	intros -> ->. 
	refine (bind__bind_rel lq_tmp0_r lq_tmp1_r VV). 
Qed. 
#[global] Hint Resolve bind__bind_rel' : f_rel_funct_db.
Theorem bind_rel_mk [lq_tmp0: L_u] [lq_tmp1: (@Pack ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT))) L_u (fun (x_61572807: (ArgList {lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT))) => (fun (v_x_61572807: L_u) => (ltac: (flattenP (fun (lq_tmp2: {lq_tmp2: Z | True}) => (fun (VV: L_u) => ((L_wf VV) /\ True))) x_61572807 v_x_61572807)))))] (lq_tmp0_p: (L_wf lq_tmp0) /\ True): {VV: _ | bind_rel lq_tmp0 (packProj lq_tmp1) VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (bind_rel lq_tmp0 (packProj lq_tmp1) VV)) (bind (exist _ lq_tmp0 lq_tmp0_p) lq_tmp1) _); 
	rewrite <- bind__bind_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve bind_rel_mk : f_rel_funct_db.
Theorem prop_append_neutral (xs: L): {{forall (appendres: L_u), (append_rel (⌊ xs -⌋) Emp_u appendres) -> (appendres = (⌊ xs -⌋))}}. 
Proof. 
	destruct xs as [xs xs_p]. 
	induction xs as [(*C*) x xs IH_xs | (*Emp*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ (IH_xs (ltac: (try clear IH_xs; 
	solver))) _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
Qed. 
Definition retrn (lq_tmp0: {lq_tmp0: Z | True}): L. 
Proof. 
	destruct lq_tmp0 as [lq_tmp0 lq_tmp0_p]. 
	refine (subsumptionCast _ _ 
		(C (exist (fun (VV: Z) => True) lq_tmp0 (ltac: (solver))) 
		(subsumptionCast L_u (fun (VV: L_u) => ((L_wf VV) /\ True)) Emp (ltac: (solver)))) _); 
	solver. 
Defined. 
Inductive retrn_rel : (Z -> (L_u -> Prop)) := 
	 | retrn_def: (forall lq_tmp0 , retrn_rel lq_tmp0 (C_u lq_tmp0 Emp_u)). 
#[global] Hint Constructors retrn_rel : core_hint_db.
#[global] Instance retrn_lookup_rel : dictionary rel retrn := { 
	lookup' := retrn_rel
}.
#[global] Instance retrn_getF : getFunc retrn_rel := { 
	getF' := retrn
}.
Theorem retrn_rel_funct [lq_tmp0: Z]: (forall (VV: L_u) (VV': L_u) (H: retrn_rel lq_tmp0 VV) (K: retrn_rel lq_tmp0 VV') , VV = VV'). 
Proof. 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve retrn_rel_funct : f_rel_funct_db.
Theorem retrn_def_lem (lq_tmp0: _): (retrn_rel lq_tmp0 (C_u lq_tmp0 Emp_u)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite retrn_def_lem : f_rel_back.
Theorem retrn_rel_ex (lq_tmp0: Z) (lq_tmp0_p: True): retrn_rel lq_tmp0 (⌊ retrn (exist _ lq_tmp0 lq_tmp0_p) -⌋). 
Proof. 
	Opaque retrn.
	existence_lemma_pre retrn; 
	fix_notations; 
	simpl in *. 
	Transparent retrn.
	all: existence_lemma_quicksolve retrn; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve retrn_rel_ex : rel_ax_db.
#[global] Opaque retrn. 
Theorem retrn__retrn_rel_rw (lq_tmp0: Z) (lq_tmp0_p: True) (VV: L_u): ((⌊ retrn (exist _ lq_tmp0 lq_tmp0_p) -⌋) = VV) <-> (retrn_rel lq_tmp0 VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite retrn__retrn_rel_rw : f_rel_funct_db.
#[global] Hint Resolve retrn__retrn_rel_rw : rel_ax_db.
#[global] Instance retrn_lookup_rw : dictionary rwLem retrn := { 
	lookup' := retrn__retrn_rel_rw
}.
Theorem retrn__retrn_rel (lq_tmp0_r: {lq_tmp0: Z | True}) (VV: L_u): ((⌊ retrn lq_tmp0_r -⌋) = VV) <-> (retrn_rel (⌊ lq_tmp0_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite retrn__retrn_rel : f_rel_funct_db.
Theorem retrn__retrn_rel' (lq_tmp0: Z) (lq_tmp0_r: {lq_tmp0: Z | True}) (VV: L_u): (lq_tmp0 = (⌊ lq_tmp0_r -⌋)) -> (((⌊ retrn lq_tmp0_r -⌋) = VV) <-> (retrn_rel lq_tmp0 VV)). 
Proof. 
	intros ->. 
	refine (retrn__retrn_rel lq_tmp0_r VV). 
Qed. 
#[global] Hint Resolve retrn__retrn_rel' : f_rel_funct_db.
Theorem retrn_rel_mk [lq_tmp0: Z] (lq_tmp0_p: True): {VV: _ | retrn_rel lq_tmp0 VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (retrn_rel lq_tmp0 VV)) (retrn (exist _ lq_tmp0 lq_tmp0_p)) _); 
	rewrite <- retrn__retrn_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve retrn_rel_mk : f_rel_funct_db.
#[global] Instance retrnPack : (@Pack ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0_r: {lq_tmp0: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0_r: {lq_tmp0: Z | True}) => nilRT)) (Z ::UT nilUT))) L_u (fun (x_89043232: (ArgList {lq_tmp0: Z | True} ::RT (fun (lq_tmp0_r: {lq_tmp0: Z | True}) => nilRT))) => (fun (v_x_89043232: L_u) => (ltac: (flattenP (fun (lq_tmp0_r: {lq_tmp0: Z | True}) => (fun (VV: L_u) => ((L_wf VV) /\ True))) x_89043232 v_x_89043232))))).
Proof. 
	buildPackG retrn retrn_rel retrn__retrn_rel retrn_rel_funct. 
Defined.
Theorem left_identity (x: {x: Z | True}) (f: (@Pack ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => nilRT)) (Z ::UT nilUT))) L_u (fun (x_86410777: (ArgList {lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => nilRT))) => (fun (v_x_86410777: L_u) => (ltac: (flattenP (fun (lq_tmp0: {lq_tmp0: Z | True}) => (fun (VV: L_u) => ((L_wf VV) /\ True))) x_86410777 v_x_86410777)))))): {{forall (retrnres: L_u), (retrn_rel (⌊ x -⌋) retrnres) -> (forall (bindres: L_u), (bind_rel retrnres (packProj f) bindres) -> (forall (fres: _), ((getPackRel f) (⌊ x -⌋) fres) -> (bindres == fres)))}}. 
Proof. 
	destruct x as [x x_p]. 
	refine (subsumptionCast _ _ 
		(prop_append_neutral 
		(subsumptionCast L_u (fun (xs: L_u) => ((L_wf xs) /\ True)) 
		((getPackF f) (exist (fun (lq_tmp0: Z) => True) x (ltac: (solver)))) (ltac: (solver)))) _); 
	solver. 
Qed. 

Polymorphic Definition right_identity_tp (x: L): Type :=
  {{forall (bindres: L_u), (bind_rel (⌊ x -⌋) 
		(ltac: (pose retrn_rel as Rel; 
	pose retrn_rel_funct as Funct; 
	buildUPackG Rel Funct)) bindres) -> (bindres = (⌊ x -⌋))}}.

Polymorphic Theorem right_identity (x: L): right_identity_tp x. 
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