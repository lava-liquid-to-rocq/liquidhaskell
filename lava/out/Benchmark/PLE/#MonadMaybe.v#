From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
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
Definition bind (lq_tmp0: MaybeInt) (lq_tmp1: (@Pack ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT))) MaybeInt_u (fun (x_61572807: (ArgList {lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT))) => (fun (v_x_61572807: MaybeInt_u) => (ltac: (flattenP (fun (lq_tmp2: {lq_tmp2: Z | True}) => (fun (VV: MaybeInt_u) => ((MaybeInt_wf VV) /\ True))) x_61572807 v_x_61572807)))))): MaybeInt. 
Proof. 
	destruct lq_tmp0 as [lq_tmp0 lq_tmp0_p]. 
	try revert lq_tmp1_p; generalize dependent lq_tmp1; 
	induction lq_tmp0 as [(*Just*) m | (*Nothing*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ 
		((getPackF lq_tmp1) (exist (fun (lq_tmp2: Z) => True) m (ltac: (solver)))) _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ Nothing _); 
		solver.  
Defined. 
Inductive bind_rel : (MaybeInt_u -> ((@uPack (Z ::UT nilUT) MaybeInt_u) -> (MaybeInt_u -> Prop))) := 
	 | bind_Nothing: (forall (lq_tmp1: @uPack (Z ::UT nilUT) MaybeInt_u) , bind_rel Nothing_u lq_tmp1 Nothing_u)
	 | bind_Just: (forall (lq_tmp1: @uPack (Z ::UT nilUT) MaybeInt_u) m , forall (lq_tmp1res: _), ((getUPackRel lq_tmp1) m lq_tmp1res) -> (bind_rel (Just_u m) lq_tmp1 lq_tmp1res)). 
#[global] Hint Constructors bind_rel : core_hint_db.
#[global] Instance bind_lookup_rel : dictionary rel bind := { 
	lookup' := bind_rel
}.
#[global] Instance bind_getF : getFunc bind_rel := { 
	getF' := bind
}.
Theorem bind_rel_funct [lq_tmp0: MaybeInt_u] [lq_tmp1: @uPack (Z ::UT nilUT) MaybeInt_u]: (forall (VV: MaybeInt_u) (VV': MaybeInt_u) (H: bind_rel lq_tmp0 lq_tmp1 VV) (K: bind_rel lq_tmp0 lq_tmp1 VV') , VV = VV'). 
Proof. 
	try revert lq_tmp1_p; generalize dependent lq_tmp1; 
	induction lq_tmp0 as [(*Just*) m | (*Nothing*) ]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve bind_rel_funct : f_rel_funct_db.
Theorem bind_Nothing_lem (lq_tmp1: @uPack (Z ::UT nilUT) MaybeInt_u): (bind_rel Nothing_u lq_tmp1 Nothing_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite bind_Nothing_lem : f_rel_back.
Theorem bind_Just_lem (m: _) (lq_tmp1: @uPack (Z ::UT nilUT) MaybeInt_u) (lq_tmp1res: _) (h_48917519: (getUPackRel lq_tmp1) m lq_tmp1res): (bind_rel (Just_u m) lq_tmp1 lq_tmp1res) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite bind_Just_lem : f_rel_back.
Theorem bind_rel_ex (lq_tmp0: MaybeInt_u) (lq_tmp1: (@Pack ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT))) MaybeInt_u (fun (x_61572807: (ArgList {lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT))) => (fun (v_x_61572807: MaybeInt_u) => (ltac: (flattenP (fun (lq_tmp2: {lq_tmp2: Z | True}) => (fun (VV: MaybeInt_u) => ((MaybeInt_wf VV) /\ True))) x_61572807 v_x_61572807)))))) (lq_tmp0_p: (MaybeInt_wf lq_tmp0) /\ True): bind_rel lq_tmp0 (packProj lq_tmp1) (⌊ bind (exist _ lq_tmp0 lq_tmp0_p) lq_tmp1 -⌋). 
Proof. 
	Opaque bind.
	existence_lemma_pre bind; 
	try revert lq_tmp1_p; generalize dependent lq_tmp1; 
	induction lq_tmp0 as [(*Just*) m | (*Nothing*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations]; 
	simpl in *. 
	Transparent bind.
	all: existence_lemma_quicksolve bind; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve bind_rel_ex : rel_ax_db.
#[global] Opaque bind. 
Theorem bind__bind_rel_rw (lq_tmp0: MaybeInt_u) (lq_tmp1: (@Pack ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT))) MaybeInt_u (fun (x_61572807: (ArgList {lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT))) => (fun (v_x_61572807: MaybeInt_u) => (ltac: (flattenP (fun (lq_tmp2: {lq_tmp2: Z | True}) => (fun (VV: MaybeInt_u) => ((MaybeInt_wf VV) /\ True))) x_61572807 v_x_61572807)))))) (lq_tmp0_p: (MaybeInt_wf lq_tmp0) /\ True) (VV: MaybeInt_u): ((⌊ bind (exist _ lq_tmp0 lq_tmp0_p) lq_tmp1 -⌋) = VV) <-> (bind_rel lq_tmp0 (packProj lq_tmp1) VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite bind__bind_rel_rw : f_rel_funct_db.
#[global] Hint Resolve bind__bind_rel_rw : rel_ax_db.
#[global] Instance bind_lookup_rw : dictionary rwLem bind := { 
	lookup' := bind__bind_rel_rw
}.
Theorem bind__bind_rel (lq_tmp0_r: MaybeInt) (lq_tmp1_r: (@Pack ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT))) MaybeInt_u (fun (x_61572807: (ArgList {lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT))) => (fun (v_x_61572807: MaybeInt_u) => (ltac: (flattenP (fun (lq_tmp2: {lq_tmp2: Z | True}) => (fun (VV: MaybeInt_u) => ((MaybeInt_wf VV) /\ True))) x_61572807 v_x_61572807)))))) (VV: MaybeInt_u): ((⌊ bind lq_tmp0_r lq_tmp1_r -⌋) = VV) <-> (bind_rel (⌊ lq_tmp0_r -⌋) (packProj lq_tmp1_r) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite bind__bind_rel : f_rel_funct_db.
Theorem bind__bind_rel' (lq_tmp0: MaybeInt_u) (lq_tmp1: @uPack (Z ::UT nilUT) MaybeInt_u) (lq_tmp0_r: MaybeInt) (lq_tmp1_r: (@Pack ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT))) MaybeInt_u (fun (x_61572807: (ArgList {lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT))) => (fun (v_x_61572807: MaybeInt_u) => (ltac: (flattenP (fun (lq_tmp2: {lq_tmp2: Z | True}) => (fun (VV: MaybeInt_u) => ((MaybeInt_wf VV) /\ True))) x_61572807 v_x_61572807)))))) (VV: MaybeInt_u): (lq_tmp0 = (⌊ lq_tmp0_r -⌋)) -> ((lq_tmp1 = (packProj lq_tmp1_r)) -> (((⌊ bind lq_tmp0_r lq_tmp1_r -⌋) = VV) <-> (bind_rel lq_tmp0 lq_tmp1 VV))). 
Proof. 
	intros -> ->. 
	refine (bind__bind_rel lq_tmp0_r lq_tmp1_r VV). 
Qed. 
#[global] Hint Resolve bind__bind_rel' : f_rel_funct_db.
Theorem bind_rel_mk [lq_tmp0: MaybeInt_u] [lq_tmp1: (@Pack ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT))) MaybeInt_u (fun (x_61572807: (ArgList {lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT))) => (fun (v_x_61572807: MaybeInt_u) => (ltac: (flattenP (fun (lq_tmp2: {lq_tmp2: Z | True}) => (fun (VV: MaybeInt_u) => ((MaybeInt_wf VV) /\ True))) x_61572807 v_x_61572807)))))] (lq_tmp0_p: (MaybeInt_wf lq_tmp0) /\ True): {VV: _ | bind_rel lq_tmp0 (packProj lq_tmp1) VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (bind_rel lq_tmp0 (packProj lq_tmp1) VV)) (bind (exist _ lq_tmp0 lq_tmp0_p) lq_tmp1) _); 
	rewrite <- bind__bind_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve bind_rel_mk : f_rel_funct_db.
Definition retrn (lq_tmp0: {lq_tmp0: Z | True}): MaybeInt. 
Proof. 
	destruct lq_tmp0 as [lq_tmp0 lq_tmp0_p]. 
	refine (subsumptionCast _ _ 
		(Just (exist (fun (VV: Z) => True) lq_tmp0 (ltac: (solver)))) _); 
	solver. 
Defined. 
Inductive retrn_rel : (Z -> (MaybeInt_u -> Prop)) := 
	 | retrn_def: (forall lq_tmp0 , retrn_rel lq_tmp0 (Just_u lq_tmp0)). 
#[global] Hint Constructors retrn_rel : core_hint_db.
#[global] Instance retrn_lookup_rel : dictionary rel retrn := { 
	lookup' := retrn_rel
}.
#[global] Instance retrn_getF : getFunc retrn_rel := { 
	getF' := retrn
}.
Theorem retrn_rel_funct [lq_tmp0: Z]: (forall (VV: MaybeInt_u) (VV': MaybeInt_u) (H: retrn_rel lq_tmp0 VV) (K: retrn_rel lq_tmp0 VV') , VV = VV'). 
Proof. 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve retrn_rel_funct : f_rel_funct_db.
Theorem retrn_def_lem (lq_tmp0: _): (retrn_rel lq_tmp0 (Just_u lq_tmp0)) <-> True. 
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
Theorem retrn__retrn_rel_rw (lq_tmp0: Z) (lq_tmp0_p: True) (VV: MaybeInt_u): ((⌊ retrn (exist _ lq_tmp0 lq_tmp0_p) -⌋) = VV) <-> (retrn_rel lq_tmp0 VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite retrn__retrn_rel_rw : f_rel_funct_db.
#[global] Hint Resolve retrn__retrn_rel_rw : rel_ax_db.
#[global] Instance retrn_lookup_rw : dictionary rwLem retrn := { 
	lookup' := retrn__retrn_rel_rw
}.
Theorem retrn__retrn_rel (lq_tmp0_r: {lq_tmp0: Z | True}) (VV: MaybeInt_u): ((⌊ retrn lq_tmp0_r -⌋) = VV) <-> (retrn_rel (⌊ lq_tmp0_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite retrn__retrn_rel : f_rel_funct_db.
Theorem retrn__retrn_rel' (lq_tmp0: Z) (lq_tmp0_r: {lq_tmp0: Z | True}) (VV: MaybeInt_u): (lq_tmp0 = (⌊ lq_tmp0_r -⌋)) -> (((⌊ retrn lq_tmp0_r -⌋) = VV) <-> (retrn_rel lq_tmp0 VV)). 
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
#[global] Instance retrnPack : (@Pack ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0_r: {lq_tmp0: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0_r: {lq_tmp0: Z | True}) => nilRT)) (Z ::UT nilUT))) MaybeInt_u (fun (x_89043232: (ArgList {lq_tmp0: Z | True} ::RT (fun (lq_tmp0_r: {lq_tmp0: Z | True}) => nilRT))) => (fun (v_x_89043232: MaybeInt_u) => (ltac: (flattenP (fun (lq_tmp0_r: {lq_tmp0: Z | True}) => (fun (VV: MaybeInt_u) => ((MaybeInt_wf VV) /\ True))) x_89043232 v_x_89043232))))).
Proof. 
	buildPackG retrn retrn_rel retrn__retrn_rel retrn_rel_funct. 
Defined.
Theorem left_identity (x: {x: Z | True}) (f: (@Pack ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => nilRT)) (Z ::UT nilUT))) MaybeInt_u (fun (x_86410777: (ArgList {lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => nilRT))) => (fun (v_x_86410777: MaybeInt_u) => (ltac: (flattenP (fun (lq_tmp0: {lq_tmp0: Z | True}) => (fun (VV: MaybeInt_u) => ((MaybeInt_wf VV) /\ True))) x_86410777 v_x_86410777)))))): {{forall (retrnres: MaybeInt_u), (retrn_rel (⌊ x -⌋) retrnres) -> (forall (bindres: MaybeInt_u), (bind_rel retrnres (packProj f) bindres) -> (forall (fres: _), ((getPackRel f) (⌊ x -⌋) fres) -> (bindres == fres)))}}. 
Proof. 
	destruct x as [x x_p]. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Theorem right_identity (x: MaybeInt): {{forall (bindres: MaybeInt_u), (bind_rel (⌊ x -⌋) 
		(ltac: (pose retrn_rel as Rel; 
	pose retrn_rel_funct as Funct; 
	buildUPackG Rel Funct)) bindres) -> (bindres = (⌊ x -⌋))}}. 
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