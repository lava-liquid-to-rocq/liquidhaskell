From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Inductive Identity_u : Set := 
	 | Val_u: Z -> Identity_u. 
Fixpoint Identity_eq (x: Identity_u) (y: Identity_u): bool := 
	match (x, y) with (Val_u x, Val_u x') => (true && (x ==? x')) end. 
Definition Identity_eq_refl: (forall (x: Identity_u) , is_true (Identity_eq x x)). 
Proof. 
	eq_refl_rec. 
Qed. 
#[global] Hint Resolve Identity_eq_refl : eq_hint_db.
Definition Identity_eqb_eq: (forall (s: Identity_u) (t: Identity_u) , (is_true (Identity_eq s t)) -> (s = t)). 
Proof. 
	eqb_eq_lem. 
Qed. 
#[global] Hint Resolve Identity_eqb_eq : eq_hint_db.
#[global] Instance leibnitz_eq_Identity : LeibnitzEqB := { 
	equalB' := Identity_eq;
	refl' := Identity_eq_refl;
	eqb_eq' := Identity_eqb_eq
}.
Fixpoint Identity_wf (x: Identity_u): Prop := 
	match x with (Val_u n) => True end. 
Theorem Identity_wf_ref [p: Identity_u -> Prop] (tm: {v: Identity_u | (Identity_wf v) /\ (p v)}): Identity_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation Identity := {x: Identity_u | (Identity_wf x) /\ True}. 
Definition Val_lem (n: {n: Z | True}): (Identity_wf (Val_u (⌊ n -⌋))) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Val (n: {n: Z | True}): Identity := 
	exist _ (Val_u (⌊ n -⌋)) (Val_lem n). 
#[global] Hint Resolve Identity_wf_ref : wf_constr_db.
#[global] Hint Unfold Identity_wf : wf_constr_db.
#[global] Hint Resolve Identity_eq : ref_constr_db.
#[global] Hint Unfold Val : ref_constr_db.
Definition compose (vx: Identity) (f: (@Pack ({x: Z | True} ::RT (fun (x: {x: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({x: Z | True} ::RT (fun (x: {x: Z | True}) => nilRT)) (Z ::UT nilUT))) Identity_u (fun (x_35415358: (ArgList {x: Z | True} ::RT (fun (x: {x: Z | True}) => nilRT))) => (fun (v_x_35415358: Identity_u) => (ltac: (flattenP (fun (x: {x: Z | True}) => (fun (VV: Identity_u) => ((Identity_wf VV) /\ True))) x_35415358 v_x_35415358)))))): Identity. 
Proof. 
	destruct vx as [vx vx_p]. 
	try revert f_p; generalize dependent f; 
	induction vx as [(*Val*) x]. 
	  - intros . 
		refine (subsumptionCast _ _ 
		((getPackF f) (exist (fun (x: Z) => True) x (ltac: (solver)))) _); 
		solver.  
Defined. 
Inductive compose_rel : (Identity_u -> ((@uPack (Z ::UT nilUT) Identity_u) -> (Identity_u -> Prop))) := 
	 | compose_Val: (forall (f: @uPack (Z ::UT nilUT) Identity_u) x , forall (fres: _), ((getUPackRel f) x fres) -> (compose_rel (Val_u x) f fres)). 
#[global] Hint Constructors compose_rel : core_hint_db.
#[global] Instance compose_lookup_rel : dictionary rel compose := { 
	lookup' := compose_rel
}.
#[global] Instance compose_getF : getFunc compose_rel := { 
	getF' := compose
}.
Definition compose_rel_funct [vx: Identity_u] [f: @uPack (Z ::UT nilUT) Identity_u]: (forall (VV: Identity_u) (VV': Identity_u) (H: compose_rel vx f VV) (K: compose_rel vx f VV') , VV = VV'). 
Proof. 
	try revert f_p; generalize dependent f; 
	induction vx as [(*Val*) x]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve compose_rel_funct : f_rel_funct_db.
Theorem compose_Val_lem (x: _) (f: @uPack (Z ::UT nilUT) Identity_u) (fres: _) (h_70155527: (getUPackRel f) x fres): (compose_rel (Val_u x) f fres) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite compose_Val_lem : f_rel_back.
Theorem compose_rel_ex (vx: Identity_u) (f: (@Pack ({x: Z | True} ::RT (fun (x: {x: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({x: Z | True} ::RT (fun (x: {x: Z | True}) => nilRT)) (Z ::UT nilUT))) Identity_u (fun (x_35415358: (ArgList {x: Z | True} ::RT (fun (x: {x: Z | True}) => nilRT))) => (fun (v_x_35415358: Identity_u) => (ltac: (flattenP (fun (x: {x: Z | True}) => (fun (VV: Identity_u) => ((Identity_wf VV) /\ True))) x_35415358 v_x_35415358)))))) (vx_p: (Identity_wf vx) /\ True): compose_rel vx (packProj f) (⌊ compose (exist _ vx vx_p) f -⌋). 
Proof. 
	Opaque compose.
	existence_lemma_pre compose; 
	try revert f_p; generalize dependent f; 
	induction vx as [(*Val*) x]; 
	intros ; 
	[fix_notations]; 
	simpl in *. 
	Transparent compose.
	all: existence_lemma_quicksolve compose; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve compose_rel_ex : rel_ax_db.
#[global] Opaque compose. 
Theorem compose__compose_rel_rw (vx: Identity_u) (f: (@Pack ({x: Z | True} ::RT (fun (x: {x: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({x: Z | True} ::RT (fun (x: {x: Z | True}) => nilRT)) (Z ::UT nilUT))) Identity_u (fun (x_35415358: (ArgList {x: Z | True} ::RT (fun (x: {x: Z | True}) => nilRT))) => (fun (v_x_35415358: Identity_u) => (ltac: (flattenP (fun (x: {x: Z | True}) => (fun (VV: Identity_u) => ((Identity_wf VV) /\ True))) x_35415358 v_x_35415358)))))) (vx_p: (Identity_wf vx) /\ True) (VV: Identity_u): ((⌊ compose (exist _ vx vx_p) f -⌋) = VV) <-> (compose_rel vx (packProj f) VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite compose__compose_rel_rw : f_rel_funct_db.
#[global] Hint Resolve compose__compose_rel_rw : rel_ax_db.
#[global] Instance compose_lookup_rw : dictionary rwLem compose := { 
	lookup' := compose__compose_rel_rw
}.
Theorem compose__compose_rel (vx_r: Identity) (f_r: (@Pack ({x: Z | True} ::RT (fun (x: {x: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({x: Z | True} ::RT (fun (x: {x: Z | True}) => nilRT)) (Z ::UT nilUT))) Identity_u (fun (x_35415358: (ArgList {x: Z | True} ::RT (fun (x: {x: Z | True}) => nilRT))) => (fun (v_x_35415358: Identity_u) => (ltac: (flattenP (fun (x: {x: Z | True}) => (fun (VV: Identity_u) => ((Identity_wf VV) /\ True))) x_35415358 v_x_35415358)))))) (VV: Identity_u): ((⌊ compose vx_r f_r -⌋) = VV) <-> (compose_rel (⌊ vx_r -⌋) (packProj f_r) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite compose__compose_rel : f_rel_funct_db.
Theorem compose__compose_rel' (vx: Identity_u) (f: @uPack (Z ::UT nilUT) Identity_u) (vx_r: Identity) (f_r: (@Pack ({x: Z | True} ::RT (fun (x: {x: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({x: Z | True} ::RT (fun (x: {x: Z | True}) => nilRT)) (Z ::UT nilUT))) Identity_u (fun (x_35415358: (ArgList {x: Z | True} ::RT (fun (x: {x: Z | True}) => nilRT))) => (fun (v_x_35415358: Identity_u) => (ltac: (flattenP (fun (x: {x: Z | True}) => (fun (VV: Identity_u) => ((Identity_wf VV) /\ True))) x_35415358 v_x_35415358)))))) (VV: Identity_u): (vx = (⌊ vx_r -⌋)) -> ((f = (packProj f_r)) -> (((⌊ compose vx_r f_r -⌋) = VV) <-> (compose_rel vx f VV))). 
Proof. 
	intros -> ->. 
	refine (compose__compose_rel vx_r f_r VV). 
Qed. 
#[global] Hint Resolve compose__compose_rel' : f_rel_funct_db.
Definition compose_rel_mk [vx: Identity_u] [f: (@Pack ({x: Z | True} ::RT (fun (x: {x: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({x: Z | True} ::RT (fun (x: {x: Z | True}) => nilRT)) (Z ::UT nilUT))) Identity_u (fun (x_35415358: (ArgList {x: Z | True} ::RT (fun (x: {x: Z | True}) => nilRT))) => (fun (v_x_35415358: Identity_u) => (ltac: (flattenP (fun (x: {x: Z | True}) => (fun (VV: Identity_u) => ((Identity_wf VV) /\ True))) x_35415358 v_x_35415358)))))] (vx_p: (Identity_wf vx) /\ True): {VV: _ | compose_rel vx (packProj f) VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (compose_rel vx (packProj f) VV)) (compose (exist _ vx vx_p) f) _); 
	rewrite <- compose__compose_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve compose_rel_mk : f_rel_funct_db.
Definition retrn (v: {v: Z | True}): Identity. 
Proof. 
	destruct v as [v v_p]. 
	refine (subsumptionCast _ _ (Val (exist (fun (n: Z) => True) v (ltac: (solver)))) _); 
	solver. 
Defined. 
Inductive retrn_rel : (Z -> (Identity_u -> Prop)) := 
	 | retrn_def: (forall v , retrn_rel v (Val_u v)). 
#[global] Hint Constructors retrn_rel : core_hint_db.
#[global] Instance retrn_lookup_rel : dictionary rel retrn := { 
	lookup' := retrn_rel
}.
#[global] Instance retrn_getF : getFunc retrn_rel := { 
	getF' := retrn
}.
Definition retrn_rel_funct [v: Z]: (forall (VV: Identity_u) (VV': Identity_u) (H: retrn_rel v VV) (K: retrn_rel v VV') , VV = VV'). 
Proof. 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve retrn_rel_funct : f_rel_funct_db.
Theorem retrn_def_lem (v: _): (retrn_rel v (Val_u v)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite retrn_def_lem : f_rel_back.
Theorem retrn_rel_ex (v: Z) (v_p: True): retrn_rel v (⌊ retrn (exist _ v v_p) -⌋). 
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
Theorem retrn__retrn_rel_rw (v: Z) (v_p: True) (VV: Identity_u): ((⌊ retrn (exist _ v v_p) -⌋) = VV) <-> (retrn_rel v VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite retrn__retrn_rel_rw : f_rel_funct_db.
#[global] Hint Resolve retrn__retrn_rel_rw : rel_ax_db.
#[global] Instance retrn_lookup_rw : dictionary rwLem retrn := { 
	lookup' := retrn__retrn_rel_rw
}.
Theorem retrn__retrn_rel (v_r: {v: Z | True}) (VV: Identity_u): ((⌊ retrn v_r -⌋) = VV) <-> (retrn_rel (⌊ v_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite retrn__retrn_rel : f_rel_funct_db.
Theorem retrn__retrn_rel' (v: Z) (v_r: {v: Z | True}) (VV: Identity_u): (v = (⌊ v_r -⌋)) -> (((⌊ retrn v_r -⌋) = VV) <-> (retrn_rel v VV)). 
Proof. 
	intros ->. 
	refine (retrn__retrn_rel v_r VV). 
Qed. 
#[global] Hint Resolve retrn__retrn_rel' : f_rel_funct_db.
Definition retrn_rel_mk [v: Z] (v_p: True): {VV: _ | retrn_rel v VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (retrn_rel v VV)) (retrn (exist _ v v_p)) _); 
	rewrite <- retrn__retrn_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve retrn_rel_mk : f_rel_funct_db.
#[global] Instance retrnPack : (@Pack ({v: Z | True} ::RT (fun (v_r: {v: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({v: Z | True} ::RT (fun (v_r: {v: Z | True}) => nilRT)) (Z ::UT nilUT))) Identity_u (fun (x_63674686: (ArgList {v: Z | True} ::RT (fun (v_r: {v: Z | True}) => nilRT))) => (fun (v_x_63674686: Identity_u) => (ltac: (flattenP (fun (v_r: {v: Z | True}) => (fun (VV: Identity_u) => ((Identity_wf VV) /\ True))) x_63674686 v_x_63674686))))).
Proof. 
	buildPackG retrn retrn_rel retrn__retrn_rel retrn_rel_funct. 
Defined.
Definition leftIdentity (x: {x: Z | True}) (f: (@Pack ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => nilRT)) (Z ::UT nilUT))) Identity_u (fun (x_86410777: (ArgList {lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => nilRT))) => (fun (v_x_86410777: Identity_u) => (ltac: (flattenP (fun (lq_tmp0: {lq_tmp0: Z | True}) => (fun (VV: Identity_u) => ((Identity_wf VV) /\ True))) x_86410777 v_x_86410777)))))): {{forall (retrnres: Identity_u), (retrn_rel (⌊ x -⌋) retrnres) -> (forall (composeres: Identity_u), (compose_rel retrnres (packProj f) composeres) -> (forall (fres: _), ((getPackRel f) (⌊ x -⌋) fres) -> (composeres == fres)))}}. 
Proof. 
	destruct x as [x x_p]. 
	refine (exist _ unit _); 
	solver. 
Defined. 
Definition rightIdentity (x: Identity): {{forall (composeres: Identity_u), (compose_rel (⌊ x -⌋) 
		(ltac: (pose retrn_rel as Rel; 
	pose retrn_rel_funct as Funct; 
	buildUPackG Rel Funct)) composeres) -> (composeres = (⌊ x -⌋))}}. 
Proof. 
	destruct x as [x x_p]. 
	induction x as [(*Val*) x]. 
	  - intros . 
		refine (exist _ unit _); 
		solver.  
Defined. 