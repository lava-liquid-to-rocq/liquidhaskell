From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Inductive L_u : Set := 
	 | App_u: Z -> (L_u -> L_u)
	 | Emp_u: L_u. 
Fixpoint L_eq (x: L_u) (y: L_u): bool := 
	match (x, y) with (App_u x x_1, App_u x' x_1') => ((true && (x ==? x')) && (L_eq x_1 x_1')) | (Emp_u, Emp_u) => true | (_, _) => false end. 
Definition L_eq_refl: (forall (x: L_u) , is_true (L_eq x x)). 
Proof. 
	eq_refl. 
Qed. 
#[global] Hint Resolve L_eq_refl : eq_hint_db.
Definition L_eqb_eq: (forall (s: L_u) (t: L_u) , (is_true (L_eq s t)) -> (s = t)). 
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
	match x with (App_u VV VV_) => ((L_wf VV_) /\ True) | Emp_u => True end. 
Theorem L_wf_ref [p: L_u -> Prop] (tm: {v: L_u | (L_wf v) /\ (p v)}): L_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation L := {x: L_u | (L_wf x) /\ True}. 
Definition App_lem (VV: {VV: Z | True}) (VV_: L): (L_wf (App_u (⌊ VV -⌋) (⌊ VV_ -⌋))) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition App (VV: {VV: Z | True}) (VV_: L): L := 
	exist _ (App_u (⌊ VV -⌋) (⌊ VV_ -⌋)) (App_lem VV VV_). 
Definition Emp_lem: (L_wf Emp_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Emp: L := 
	exist _ Emp_u Emp_lem. 
Definition wf_App_VV_ [VV: Z] [VV_: L_u] (p: L_wf (App_u VV VV_)): L_wf VV_. 
Proof. 
	quicksolve. 
Defined. 
#[global] Hint Resolve L_wf_ref : wf_constr_db.
#[global] Hint Unfold L_wf : wf_constr_db.
#[global] Hint Resolve L_eq : ref_constr_db.
#[global] Hint Resolve wf_App_VV_ : ref_constr_db.
#[global] Hint Unfold App : ref_constr_db.
#[global] Hint Unfold Emp : ref_constr_db.
Definition append (lq_tmp0: L) (lq_tmp1: L): L. 
Proof. 
	destruct lq_tmp0 as [lq_tmp0 lq_tmp0_p]. 
	destruct lq_tmp1 as [lq_tmp1 lq_tmp1_p]. 
	try revert lq_tmp1_p; generalize dependent lq_tmp1; 
	induction lq_tmp0 as [(*App*) x xs IH_xs | (*Emp*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ 
		(App (exist (fun (VV: Z) => True) x (ltac: (solver))) 
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
	 | append_App: (forall lq_tmp1 x xs , forall (appendres: L_u), (append_rel xs lq_tmp1 appendres) -> (append_rel (App_u x xs) lq_tmp1 (App_u x appendres))). 
#[global] Hint Constructors append_rel : core_hint_db.
#[global] Instance append_lookup_rel : dictionary rel append := { 
	lookup' := append_rel
}.
#[global] Instance append_getF : getFunc append_rel := { 
	getF' := append
}.
Definition append_rel_funct [lq_tmp0: L_u] [lq_tmp1: L_u]: (forall (VV: L_u) (VV': L_u) (H: append_rel lq_tmp0 lq_tmp1 VV) (K: append_rel lq_tmp0 lq_tmp1 VV') , VV = VV'). 
Proof. 
	try revert lq_tmp1_p; generalize dependent lq_tmp1; 
	induction lq_tmp0 as [(*App*) x xs IH_xs | (*Emp*) ]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve append_rel_funct : f_rel_funct_db.
Theorem append_Emp_lem (lq_tmp1: _): (append_rel Emp_u lq_tmp1 lq_tmp1) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite append_Emp_lem : f_rel_back.
Theorem append_App_lem (x: _) (xs: _) (lq_tmp1: _) (appendres: L_u) (h_86920335: append_rel xs lq_tmp1 appendres): (append_rel (App_u x xs) lq_tmp1 (App_u x appendres)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite append_App_lem : f_rel_back.
Theorem append_rel_ex (lq_tmp0: L_u) (lq_tmp1: L_u) (lq_tmp0_p: (L_wf lq_tmp0) /\ True) (lq_tmp1_p: (L_wf lq_tmp1) /\ True): append_rel lq_tmp0 lq_tmp1 
		(⌊ append (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p) -⌋). 
Proof. 
	existence_lemma_pre append; 
	try revert lq_tmp1_p; generalize dependent lq_tmp1; 
	induction lq_tmp0 as [(*App*) x xs IH_xs | (*Emp*) ]; 
	intros ; 
	[fix_notations; 
	pose proof (IH_xs (ltac: (try clear IH_xs; 
	solver)) lq_tmp1 (ltac: (try clear IH_xs; 
	solver))) as IH_63046731; 
	try clear IH_xs| 
	fix_notations]; 
	existence_lemma_quicksolve append; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve append_rel_ex : rel_ax_db.
Opaque append. 
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
Definition append_rel_mk [lq_tmp0: L_u] [lq_tmp1: L_u] (lq_tmp0_p: (L_wf lq_tmp0) /\ True) (lq_tmp1_p: (L_wf lq_tmp1) /\ True): {VV: _ | append_rel lq_tmp0 lq_tmp1 VV}. 
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
Definition concatMap (lq_tmp0: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT))) L_u (fun (x_39721497: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))) => (fun (v_x_39721497: L_u) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: L_u) => ((L_wf VV) /\ True))) x_39721497 v_x_39721497)))))) (lq_tmp3: L): L. 
Proof. 
	destruct lq_tmp3 as [lq_tmp3 lq_tmp3_p]. 
	try revert lq_tmp0_p; generalize dependent lq_tmp0; 
	induction lq_tmp3 as [(*App*) x xs IH_xs | (*Emp*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ 
		(append 
		(subsumptionCast L_u (fun (lq_tmp0: L_u) => ((L_wf lq_tmp0) /\ True)) 
		((getPackF lq_tmp0) (exist (fun (lq_tmp1: Z) => True) x (ltac: (solver)))) (ltac: (solver))) 
		(subsumptionCast L_u (fun (lq_tmp1: L_u) => ((L_wf lq_tmp1) /\ True)) (IH_xs (ltac: (try clear IH_xs; 
	solver)) lq_tmp0) (ltac: (solver)))) _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ Emp _); 
		solver.  
Defined. 
Inductive concatMap_rel : ((@uPack (Z ::UT nilUT) L_u) -> (L_u -> (L_u -> Prop))) := 
	 | concatMap_Emp: (forall (lq_tmp0: @uPack (Z ::UT nilUT) L_u) , concatMap_rel lq_tmp0 Emp_u Emp_u)
	 | concatMap_App: (forall (lq_tmp0: @uPack (Z ::UT nilUT) L_u) x xs , forall (concatMapres: L_u), (concatMap_rel lq_tmp0 xs concatMapres) -> (forall (lq_tmp0res: _), ((getUPackRel lq_tmp0) x lq_tmp0res) -> (forall (appendres: L_u), (append_rel lq_tmp0res concatMapres appendres) -> (concatMap_rel lq_tmp0 (App_u x xs) appendres)))). 
#[global] Hint Constructors concatMap_rel : core_hint_db.
#[global] Instance concatMap_lookup_rel : dictionary rel concatMap := { 
	lookup' := concatMap_rel
}.
#[global] Instance concatMap_getF : getFunc concatMap_rel := { 
	getF' := concatMap
}.
Definition concatMap_rel_funct [lq_tmp0: @uPack (Z ::UT nilUT) L_u] [lq_tmp3: L_u]: (forall (VV: L_u) (VV': L_u) (H: concatMap_rel lq_tmp0 lq_tmp3 VV) (K: concatMap_rel lq_tmp0 lq_tmp3 VV') , VV = VV'). 
Proof. 
	try revert lq_tmp0_p; generalize dependent lq_tmp0; 
	induction lq_tmp3 as [(*App*) x xs IH_xs | (*Emp*) ]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve concatMap_rel_funct : f_rel_funct_db.
Theorem concatMap_Emp_lem (lq_tmp0: @uPack (Z ::UT nilUT) L_u): (concatMap_rel lq_tmp0 Emp_u Emp_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite concatMap_Emp_lem : f_rel_back.
Theorem concatMap_App_lem (lq_tmp0: @uPack (Z ::UT nilUT) L_u) (x: _) (xs: _) (appendres: L_u): (concatMap_rel lq_tmp0 (App_u x xs) appendres) <-> (exists (concatMapres: L_u), (concatMap_rel lq_tmp0 xs concatMapres) /\ (exists (lq_tmp0res: _), ((getUPackRel lq_tmp0) x lq_tmp0res) /\ (append_rel lq_tmp0res concatMapres appendres))). 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite concatMap_App_lem : f_rel_back.
Theorem concatMap_rel_ex (lq_tmp0: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT))) L_u (fun (x_39721497: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))) => (fun (v_x_39721497: L_u) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: L_u) => ((L_wf VV) /\ True))) x_39721497 v_x_39721497)))))) (lq_tmp3: L_u) (lq_tmp3_p: (L_wf lq_tmp3) /\ True): concatMap_rel (packProj lq_tmp0) lq_tmp3 (⌊ concatMap lq_tmp0 (exist _ lq_tmp3 lq_tmp3_p) -⌋). 
Proof. 
	existence_lemma_pre concatMap; 
	try revert lq_tmp0_p; generalize dependent lq_tmp0; 
	induction lq_tmp3 as [(*App*) x xs IH_xs | (*Emp*) ]; 
	intros ; 
	[fix_notations; 
	pose proof (IH_xs (ltac: (try clear IH_xs; 
	solver)) lq_tmp0) as IH_35317719; 
	try clear IH_xs| 
	fix_notations]; 
	existence_lemma_quicksolve concatMap; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve concatMap_rel_ex : rel_ax_db.
Opaque concatMap. 
Theorem concatMap__concatMap_rel_rw (lq_tmp0: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT))) L_u (fun (x_39721497: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))) => (fun (v_x_39721497: L_u) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: L_u) => ((L_wf VV) /\ True))) x_39721497 v_x_39721497)))))) (lq_tmp3: L_u) (lq_tmp3_p: (L_wf lq_tmp3) /\ True) (VV: L_u): ((⌊ concatMap lq_tmp0 (exist _ lq_tmp3 lq_tmp3_p) -⌋) = VV) <-> (concatMap_rel (packProj lq_tmp0) lq_tmp3 VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite concatMap__concatMap_rel_rw : f_rel_funct_db.
#[global] Hint Resolve concatMap__concatMap_rel_rw : rel_ax_db.
#[global] Instance concatMap_lookup_rw : dictionary rwLem concatMap := { 
	lookup' := concatMap__concatMap_rel_rw
}.
Theorem concatMap__concatMap_rel (lq_tmp0_r: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT))) L_u (fun (x_39721497: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))) => (fun (v_x_39721497: L_u) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: L_u) => ((L_wf VV) /\ True))) x_39721497 v_x_39721497)))))) (lq_tmp3_r: L) (VV: L_u): ((⌊ concatMap lq_tmp0_r lq_tmp3_r -⌋) = VV) <-> (concatMap_rel (packProj lq_tmp0_r) (⌊ lq_tmp3_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite concatMap__concatMap_rel : f_rel_funct_db.
Theorem concatMap__concatMap_rel' (lq_tmp0: @uPack (Z ::UT nilUT) L_u) (lq_tmp3: L_u) (lq_tmp0_r: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT))) L_u (fun (x_39721497: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))) => (fun (v_x_39721497: L_u) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: L_u) => ((L_wf VV) /\ True))) x_39721497 v_x_39721497)))))) (lq_tmp3_r: L) (VV: L_u): (lq_tmp0 = (packProj lq_tmp0_r)) -> ((lq_tmp3 = (⌊ lq_tmp3_r -⌋)) -> (((⌊ concatMap lq_tmp0_r lq_tmp3_r -⌋) = VV) <-> (concatMap_rel lq_tmp0 lq_tmp3 VV))). 
Proof. 
	intros -> ->. 
	refine (concatMap__concatMap_rel lq_tmp0_r lq_tmp3_r VV). 
Qed. 
#[global] Hint Resolve concatMap__concatMap_rel' : f_rel_funct_db.
Definition concatMap_rel_mk [lq_tmp0: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT))) L_u (fun (x_39721497: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))) => (fun (v_x_39721497: L_u) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: L_u) => ((L_wf VV) /\ True))) x_39721497 v_x_39721497)))))] [lq_tmp3: L_u] (lq_tmp3_p: (L_wf lq_tmp3) /\ True): {VV: _ | concatMap_rel (packProj lq_tmp0) lq_tmp3 VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ 
		(fun (VV: _) => (concatMap_rel (packProj lq_tmp0) lq_tmp3 VV)) (concatMap lq_tmp0 (exist _ lq_tmp3 lq_tmp3_p)) _); 
	rewrite <- concatMap__concatMap_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve concatMap_rel_mk : f_rel_funct_db.
Definition map (lq_tmp0: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_39721497: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))) => (fun (v_x_39721497: Z) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True)) x_39721497 v_x_39721497)))))) (lq_tmp3: L): L. 
Proof. 
	destruct lq_tmp3 as [lq_tmp3 lq_tmp3_p]. 
	try revert lq_tmp0_p; generalize dependent lq_tmp0; 
	induction lq_tmp3 as [(*App*) x xs IH_xs | (*Emp*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ 
		(App 
		((getPackF lq_tmp0) (exist (fun (lq_tmp1: Z) => True) x (ltac: (solver)))) (IH_xs (ltac: (try clear IH_xs; 
	solver)) lq_tmp0)) _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ Emp _); 
		solver.  
Defined. 
Inductive map_rel : ((@uPack (Z ::UT nilUT) Z) -> (L_u -> (L_u -> Prop))) := 
	 | map_Emp: (forall (lq_tmp0: @uPack (Z ::UT nilUT) Z) , map_rel lq_tmp0 Emp_u Emp_u)
	 | map_App: (forall (lq_tmp0: @uPack (Z ::UT nilUT) Z) x xs , forall (mapres: L_u), (map_rel lq_tmp0 xs mapres) -> (forall (lq_tmp0res: _), ((getUPackRel lq_tmp0) x lq_tmp0res) -> (map_rel lq_tmp0 (App_u x xs) (App_u lq_tmp0res mapres)))). 
#[global] Hint Constructors map_rel : core_hint_db.
#[global] Instance map_lookup_rel : dictionary rel map := { 
	lookup' := map_rel
}.
#[global] Instance map_getF : getFunc map_rel := { 
	getF' := map
}.
Definition map_rel_funct [lq_tmp0: @uPack (Z ::UT nilUT) Z] [lq_tmp3: L_u]: (forall (VV: L_u) (VV': L_u) (H: map_rel lq_tmp0 lq_tmp3 VV) (K: map_rel lq_tmp0 lq_tmp3 VV') , VV = VV'). 
Proof. 
	try revert lq_tmp0_p; generalize dependent lq_tmp0; 
	induction lq_tmp3 as [(*App*) x xs IH_xs | (*Emp*) ]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve map_rel_funct : f_rel_funct_db.
Theorem map_Emp_lem (lq_tmp0: @uPack (Z ::UT nilUT) Z): (map_rel lq_tmp0 Emp_u Emp_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite map_Emp_lem : f_rel_back.
Theorem map_App_lem (lq_tmp0: @uPack (Z ::UT nilUT) Z) (x: _) (xs: _) (lq_tmp0res: _) (mapres: L_u) (h_88923566: (getUPackRel lq_tmp0) x lq_tmp0res) (h_40663038: map_rel lq_tmp0 xs mapres): (map_rel lq_tmp0 (App_u x xs) (App_u lq_tmp0res mapres)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite map_App_lem : f_rel_back.
Theorem map_rel_ex (lq_tmp0: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_39721497: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))) => (fun (v_x_39721497: Z) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True)) x_39721497 v_x_39721497)))))) (lq_tmp3: L_u) (lq_tmp3_p: (L_wf lq_tmp3) /\ True): map_rel (packProj lq_tmp0) lq_tmp3 (⌊ map lq_tmp0 (exist _ lq_tmp3 lq_tmp3_p) -⌋). 
Proof. 
	existence_lemma_pre map; 
	try revert lq_tmp0_p; generalize dependent lq_tmp0; 
	induction lq_tmp3 as [(*App*) x xs IH_xs | (*Emp*) ]; 
	intros ; 
	[fix_notations; 
	pose proof (IH_xs (ltac: (try clear IH_xs; 
	solver)) lq_tmp0) as IH_35317719; 
	try clear IH_xs| 
	fix_notations]; 
	existence_lemma_quicksolve map; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve map_rel_ex : rel_ax_db.
Opaque map. 
Theorem map__map_rel_rw (lq_tmp0: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_39721497: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))) => (fun (v_x_39721497: Z) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True)) x_39721497 v_x_39721497)))))) (lq_tmp3: L_u) (lq_tmp3_p: (L_wf lq_tmp3) /\ True) (VV: L_u): ((⌊ map lq_tmp0 (exist _ lq_tmp3 lq_tmp3_p) -⌋) = VV) <-> (map_rel (packProj lq_tmp0) lq_tmp3 VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite map__map_rel_rw : f_rel_funct_db.
#[global] Hint Resolve map__map_rel_rw : rel_ax_db.
#[global] Instance map_lookup_rw : dictionary rwLem map := { 
	lookup' := map__map_rel_rw
}.
Theorem map__map_rel (lq_tmp0_r: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_39721497: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))) => (fun (v_x_39721497: Z) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True)) x_39721497 v_x_39721497)))))) (lq_tmp3_r: L) (VV: L_u): ((⌊ map lq_tmp0_r lq_tmp3_r -⌋) = VV) <-> (map_rel (packProj lq_tmp0_r) (⌊ lq_tmp3_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite map__map_rel : f_rel_funct_db.
Theorem map__map_rel' (lq_tmp0: @uPack (Z ::UT nilUT) Z) (lq_tmp3: L_u) (lq_tmp0_r: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_39721497: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))) => (fun (v_x_39721497: Z) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True)) x_39721497 v_x_39721497)))))) (lq_tmp3_r: L) (VV: L_u): (lq_tmp0 = (packProj lq_tmp0_r)) -> ((lq_tmp3 = (⌊ lq_tmp3_r -⌋)) -> (((⌊ map lq_tmp0_r lq_tmp3_r -⌋) = VV) <-> (map_rel lq_tmp0 lq_tmp3 VV))). 
Proof. 
	intros -> ->. 
	refine (map__map_rel lq_tmp0_r lq_tmp3_r VV). 
Qed. 
#[global] Hint Resolve map__map_rel' : f_rel_funct_db.
Definition map_rel_mk [lq_tmp0: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_39721497: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))) => (fun (v_x_39721497: Z) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True)) x_39721497 v_x_39721497)))))] [lq_tmp3: L_u] (lq_tmp3_p: (L_wf lq_tmp3) /\ True): {VV: _ | map_rel (packProj lq_tmp0) lq_tmp3 VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (map_rel (packProj lq_tmp0) lq_tmp3 VV)) (map lq_tmp0 (exist _ lq_tmp3 lq_tmp3_p)) _); 
	rewrite <- map__map_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve map_rel_mk : f_rel_funct_db.
Definition prop_append_neutral (xs: L): {{forall (appendres: L_u), (append_rel (⌊ xs -⌋) Emp_u appendres) -> (appendres = (⌊ xs -⌋))}}. 
Proof. 
	destruct xs as [xs xs_p]. 
	induction xs as [(*App*) ds_d2kz xs IH_xs | (*Emp*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ (IH_xs (ltac: (try clear IH_xs; 
	solver))) _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
Defined. 
Definition prop_assoc (xs: L) (ys: L) (zs: L): {{forall (appendres: L_u), (append_rel (⌊ xs -⌋) (⌊ ys -⌋) appendres) -> (forall (append_res_2: L_u), (append_rel appendres (⌊ zs -⌋) append_res_2) -> (forall (append_res_3: L_u), (append_rel (⌊ ys -⌋) (⌊ zs -⌋) append_res_3) -> (forall (append_res_4: L_u), (append_rel (⌊ xs -⌋) append_res_3 append_res_4) -> (append_res_2 == append_res_4))))}}. 
Proof. 
	destruct xs as [xs xs_p]. 
	destruct ys as [ys ys_p]. 
	destruct zs as [zs zs_p]. 
	try revert zs_p; generalize dependent zs; try revert ys_p; generalize dependent ys; 
	induction xs as [(*App*) x xs IH_xs | (*Emp*) ]. 
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
Defined. 
Definition prop_map_append (f: (@Pack ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_86410777: (ArgList {lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => nilRT))) => (fun (v_x_86410777: Z) => (ltac: (flattenP (fun (lq_tmp0: {lq_tmp0: Z | True}) => (fun (VV: Z) => True)) x_86410777 v_x_86410777)))))) (xs: L) (ys: L): {{forall (appendres: L_u), (append_rel (⌊ xs -⌋) (⌊ ys -⌋) appendres) -> (forall (mapres: L_u), (map_rel (packProj f) appendres mapres) -> (forall (map_res_2: L_u), (map_rel (packProj f) (⌊ ys -⌋) map_res_2) -> (forall (map_res_3: L_u), (map_rel (packProj f) (⌊ xs -⌋) map_res_3) -> (forall (append_res_2: L_u), (append_rel map_res_3 map_res_2 append_res_2) -> (mapres == append_res_2)))))}}. 
Proof. 
	destruct xs as [xs xs_p]. 
	destruct ys as [ys ys_p]. 
	try revert ys_p; generalize dependent ys; try revert f_p; generalize dependent f; 
	induction xs as [(*App*) ds_d2ku xs IH_xs | (*Emp*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ 
		(IH_xs (ltac: (try clear IH_xs; 
	solver)) f ys (ltac: (try clear IH_xs; 
	solver))) _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
Defined. 