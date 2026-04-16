From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Definition flip (f: (@Pack ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)) (ltac: (mkProjectsArgListTG ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)))) Z (fun (x_33150792: (ArgList {lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))))) => (fun (v_x_33150792: Z) => (ltac: (flattenP (fun (lq_tmp0: {lq_tmp0: Z | True}) => (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True))) x_33150792 v_x_33150792)))))) (x: {x: Z | True}) (y: {y: Z | True}): {VV: Z | True}. 
Proof. 
	destruct x as [x x_p]. 
	destruct y as [y y_p]. 
	refine (subsumptionCast _ _ 
		((getPackF f) (exist (fun (lq_tmp0: Z) => True) y (ltac: (solver))) (exist (fun (lq_tmp1: Z) => True) x (ltac: (solver)))) _); 
	solver. 
Defined. 
Inductive flip_rel : ((@uPack (Z ::UT (Z ::UT nilUT)) Z) -> (Z -> (Z -> (Z -> Prop)))) := 
	 | flip_def: (forall (f: @uPack (Z ::UT (Z ::UT nilUT)) Z) x y , forall (fres: _), ((getUPackRel f) y x fres) -> (flip_rel f x y fres)). 
#[global] Hint Constructors flip_rel : core_hint_db.
#[global] Instance flip_lookup_rel : dictionary rel flip := { 
	lookup' := flip_rel
}.
#[global] Instance flip_getF : getFunc flip_rel := { 
	getF' := flip
}.
Definition flip_rel_funct [f: @uPack (Z ::UT (Z ::UT nilUT)) Z] [x: Z] [y: Z]: (forall (VV: Z) (VV': Z) (H: flip_rel f x y VV) (K: flip_rel f x y VV') , VV = VV'). 
Proof. 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve flip_rel_funct : f_rel_funct_db.
Theorem flip_def_lem (f: @uPack (Z ::UT (Z ::UT nilUT)) Z) (x: _) (y: _) (fres: _) (h_10281062: (getUPackRel f) y x fres): (flip_rel f x y fres) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite flip_def_lem : f_rel_back.
Theorem flip_rel_ex (f: (@Pack ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)) (ltac: (mkProjectsArgListTG ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)))) Z (fun (x_33150792: (ArgList {lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))))) => (fun (v_x_33150792: Z) => (ltac: (flattenP (fun (lq_tmp0: {lq_tmp0: Z | True}) => (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True))) x_33150792 v_x_33150792)))))) (x: Z) (y: Z) (x_p: True) (y_p: True): flip_rel (packProj f) x y (⌊ flip f (exist _ x x_p) (exist _ y y_p) -⌋). 
Proof. 
	existence_lemma_pre flip; 
	fix_notations; 
	existence_lemma_quicksolve flip; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve flip_rel_ex : rel_ax_db.
Opaque flip. 
Theorem flip__flip_rel_rw (f: (@Pack ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)) (ltac: (mkProjectsArgListTG ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)))) Z (fun (x_33150792: (ArgList {lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))))) => (fun (v_x_33150792: Z) => (ltac: (flattenP (fun (lq_tmp0: {lq_tmp0: Z | True}) => (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True))) x_33150792 v_x_33150792)))))) (x: Z) (y: Z) (x_p: True) (y_p: True) (VV: Z): ((⌊ flip f (exist _ x x_p) (exist _ y y_p) -⌋) = VV) <-> (flip_rel (packProj f) x y VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite flip__flip_rel_rw : f_rel_funct_db.
#[global] Hint Resolve flip__flip_rel_rw : rel_ax_db.
#[global] Instance flip_lookup_rw : dictionary rwLem flip := { 
	lookup' := flip__flip_rel_rw
}.
Theorem flip__flip_rel (f_r: (@Pack ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)) (ltac: (mkProjectsArgListTG ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)))) Z (fun (x_33150792: (ArgList {lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))))) => (fun (v_x_33150792: Z) => (ltac: (flattenP (fun (lq_tmp0: {lq_tmp0: Z | True}) => (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True))) x_33150792 v_x_33150792)))))) (x_r: {x: Z | True}) (y_r: {y: Z | True}) (VV: Z): ((⌊ flip f_r x_r y_r -⌋) = VV) <-> (flip_rel (packProj f_r) (⌊ x_r -⌋) (⌊ y_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite flip__flip_rel : f_rel_funct_db.
Theorem flip__flip_rel' (f: @uPack (Z ::UT (Z ::UT nilUT)) Z) (x: Z) (y: Z) (f_r: (@Pack ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)) (ltac: (mkProjectsArgListTG ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)))) Z (fun (x_33150792: (ArgList {lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))))) => (fun (v_x_33150792: Z) => (ltac: (flattenP (fun (lq_tmp0: {lq_tmp0: Z | True}) => (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True))) x_33150792 v_x_33150792)))))) (x_r: {x: Z | True}) (y_r: {y: Z | True}) (VV: Z): (f = (packProj f_r)) -> ((x = (⌊ x_r -⌋)) -> ((y = (⌊ y_r -⌋)) -> (((⌊ flip f_r x_r y_r -⌋) = VV) <-> (flip_rel f x y VV)))). 
Proof. 
	intros -> -> ->. 
	refine (flip__flip_rel f_r x_r y_r VV). 
Qed. 
#[global] Hint Resolve flip__flip_rel' : f_rel_funct_db.
Definition flip_rel_mk [f: (@Pack ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)) (ltac: (mkProjectsArgListTG ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)))) Z (fun (x_33150792: (ArgList {lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))))) => (fun (v_x_33150792: Z) => (ltac: (flattenP (fun (lq_tmp0: {lq_tmp0: Z | True}) => (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True))) x_33150792 v_x_33150792)))))] [x: Z] [y: Z] (x_p: True) (y_p: True): {VV: _ | flip_rel (packProj f) x y VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (flip_rel (packProj f) x y VV)) (flip f (exist _ x x_p) (exist _ y y_p)) _); 
	rewrite <- flip__flip_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve flip_rel_mk : f_rel_funct_db.
Inductive Pair_u : Set := 
	 | MkPair_u: Z -> (Z -> Pair_u). 
Fixpoint Pair_eq (x: Pair_u) (y: Pair_u): bool := 
	match (x, y) with (MkPair_u x x_1, MkPair_u x' x_1') => ((true && (x ==? x')) && (x_1 ==? x_1')) end. 
Definition Pair_eq_refl: (forall (x: Pair_u) , is_true (Pair_eq x x)). 
Proof. 
	eq_refl. 
Qed. 
#[global] Hint Resolve Pair_eq_refl : eq_hint_db.
Definition Pair_eqb_eq: (forall (s: Pair_u) (t: Pair_u) , (is_true (Pair_eq s t)) -> (s = t)). 
Proof. 
	eqb_eq_lem. 
Qed. 
#[global] Hint Resolve Pair_eqb_eq : eq_hint_db.
#[global] Instance leibnitz_eq_Pair : LeibnitzEqB := { 
	equalB' := Pair_eq;
	refl' := Pair_eq_refl;
	eqb_eq' := Pair_eqb_eq
}.
Fixpoint Pair_wf (x: Pair_u): Prop := 
	match x with (MkPair_u VV VV_) => True end. 
Theorem Pair_wf_ref [p: Pair_u -> Prop] (tm: {v: Pair_u | (Pair_wf v) /\ (p v)}): Pair_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation Pair := {x: Pair_u | (Pair_wf x) /\ True}. 
Definition MkPair_lem (VV: {VV: Z | True}) (VV_: {VV: Z | True}): (Pair_wf (MkPair_u (⌊ VV -⌋) (⌊ VV_ -⌋))) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition MkPair (VV: {VV: Z | True}) (VV_: {VV: Z | True}): Pair := 
	exist _ (MkPair_u (⌊ VV -⌋) (⌊ VV_ -⌋)) (MkPair_lem VV VV_). 
#[global] Hint Resolve Pair_wf_ref : wf_constr_db.
#[global] Hint Unfold Pair_wf : wf_constr_db.
#[global] Hint Resolve Pair_eq : ref_constr_db.
#[global] Hint Unfold MkPair : ref_constr_db.
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
Inductive L2_u : Set := 
	 | App2_u: Pair_u -> (L2_u -> L2_u)
	 | Emp2_u: L2_u. 
Fixpoint L2_eq (x: L2_u) (y: L2_u): bool := 
	match (x, y) with (App2_u x x_1, App2_u x' x_1') => ((true && (x ==? x')) && (L2_eq x_1 x_1')) | (Emp2_u, Emp2_u) => true | (_, _) => false end. 
Definition L2_eq_refl: (forall (x: L2_u) , is_true (L2_eq x x)). 
Proof. 
	eq_refl. 
Qed. 
#[global] Hint Resolve L2_eq_refl : eq_hint_db.
Definition L2_eqb_eq: (forall (s: L2_u) (t: L2_u) , (is_true (L2_eq s t)) -> (s = t)). 
Proof. 
	eqb_eq_lem. 
Qed. 
#[global] Hint Resolve L2_eqb_eq : eq_hint_db.
#[global] Instance leibnitz_eq_L2 : LeibnitzEqB := { 
	equalB' := L2_eq;
	refl' := L2_eq_refl;
	eqb_eq' := L2_eqb_eq
}.
Fixpoint L2_wf (x: L2_u): Prop := 
	match x with (App2_u VV VV_) => (((Pair_wf VV) /\ True) /\ ((L2_wf VV_) /\ True)) | Emp2_u => True end. 
Theorem L2_wf_ref [p: L2_u -> Prop] (tm: {v: L2_u | (L2_wf v) /\ (p v)}): L2_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation L2 := {x: L2_u | (L2_wf x) /\ True}. 
Definition App2_lem (VV: Pair) (VV_: L2): (L2_wf (App2_u (⌊ VV -⌋) (⌊ VV_ -⌋))) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition App2 (VV: Pair) (VV_: L2): L2 := 
	exist _ (App2_u (⌊ VV -⌋) (⌊ VV_ -⌋)) (App2_lem VV VV_). 
Definition Emp2_lem: (L2_wf Emp2_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Emp2: L2 := 
	exist _ Emp2_u Emp2_lem. 
Definition wf_App2_VV_ [VV: Pair_u] [VV_: L2_u] (p: L2_wf (App2_u VV VV_)): L2_wf VV_. 
Proof. 
	quicksolve. 
Defined. 
#[global] Hint Resolve L2_wf_ref : wf_constr_db.
#[global] Hint Unfold L2_wf : wf_constr_db.
#[global] Hint Resolve L2_eq : ref_constr_db.
#[global] Hint Resolve wf_App2_VV_ : ref_constr_db.
#[global] Hint Unfold App2 : ref_constr_db.
#[global] Hint Unfold Emp2 : ref_constr_db.
Definition length2 (l: L2): Nats. 
Proof. 
	destruct l as [l l_p]. 
	induction l as [(*App2*) ds_d2zh xs IH_xs | (*Emp2*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ 
		(Suc 
		(subsumptionCast Nats_u (fun (n: Nats_u) => ((Nats_wf n) /\ True)) (IH_xs (ltac: (try clear IH_xs; 
	solver))) (ltac: (solver)))) _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ Zero _); 
		solver.  
Defined. 
Inductive length2_rel : (L2_u -> (Nats_u -> Prop)) := 
	 | length2_Emp2: length2_rel Emp2_u Zero_u
	 | length2_App2: (forall ds_d2zh xs , forall (length2res: Nats_u), (length2_rel xs length2res) -> (length2_rel (App2_u ds_d2zh xs) (Suc_u length2res))). 
#[global] Hint Constructors length2_rel : core_hint_db.
#[global] Instance length2_lookup_rel : dictionary rel length2 := { 
	lookup' := length2_rel
}.
#[global] Instance length2_getF : getFunc length2_rel := { 
	getF' := length2
}.
Definition length2_rel_funct [l: L2_u]: (forall (VV: Nats_u) (VV': Nats_u) (H: length2_rel l VV) (K: length2_rel l VV') , VV = VV'). 
Proof. 
	induction l as [(*App2*) ds_d2zh xs IH_xs | (*Emp2*) ]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve length2_rel_funct : f_rel_funct_db.
Theorem length2_Emp2_lem: (length2_rel Emp2_u Zero_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite length2_Emp2_lem : f_rel_back.
Theorem length2_App2_lem (ds_d2zh: _) (xs: _) (length2res: Nats_u) (h_68853692: length2_rel xs length2res): (length2_rel (App2_u ds_d2zh xs) (Suc_u length2res)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite length2_App2_lem : f_rel_back.
Theorem length2_rel_ex (l: L2_u) (l_p: (L2_wf l) /\ True): length2_rel l (⌊ length2 (exist _ l l_p) -⌋). 
Proof. 
	existence_lemma_pre length2; 
	induction l as [(*App2*) ds_d2zh xs IH_xs | (*Emp2*) ]; 
	intros ; 
	[fix_notations; 
	pose proof (IH_xs (ltac: (try clear IH_xs; 
	solver))) as IH_55394889; 
	try clear IH_xs| 
	fix_notations]; 
	existence_lemma_quicksolve length2; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve length2_rel_ex : rel_ax_db.
Opaque length2. 
Theorem length2__length2_rel_rw (l: L2_u) (l_p: (L2_wf l) /\ True) (VV: Nats_u): ((⌊ length2 (exist _ l l_p) -⌋) = VV) <-> (length2_rel l VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite length2__length2_rel_rw : f_rel_funct_db.
#[global] Hint Resolve length2__length2_rel_rw : rel_ax_db.
#[global] Instance length2_lookup_rw : dictionary rwLem length2 := { 
	lookup' := length2__length2_rel_rw
}.
Theorem length2__length2_rel (l_r: L2) (VV: Nats_u): ((⌊ length2 l_r -⌋) = VV) <-> (length2_rel (⌊ l_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite length2__length2_rel : f_rel_funct_db.
Theorem length2__length2_rel' (l: L2_u) (l_r: L2) (VV: Nats_u): (l = (⌊ l_r -⌋)) -> (((⌊ length2 l_r -⌋) = VV) <-> (length2_rel l VV)). 
Proof. 
	intros ->. 
	refine (length2__length2_rel l_r VV). 
Qed. 
#[global] Hint Resolve length2__length2_rel' : f_rel_funct_db.
Definition length2_rel_mk [l: L2_u] (l_p: (L2_wf l) /\ True): {VV: _ | length2_rel l VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (length2_rel l VV)) (length2 (exist _ l l_p)) _); 
	rewrite <- length2__length2_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve length2_rel_mk : f_rel_funct_db.
#[global] Instance length2Pack : (@Pack (L2 ::RT (fun (l_r: L2) => nilRT)) (L2_u ::UT nilUT) (ltac: (mkProjectsArgListTG (L2 ::RT (fun (l_r: L2) => nilRT)) (L2_u ::UT nilUT))) Nats_u (fun (x_29182827: (ArgList L2 ::RT (fun (l_r: L2) => nilRT))) => (fun (v_x_29182827: Nats_u) => (ltac: (flattenP (fun (l_r: L2) => (fun (VV: Nats_u) => ((Nats_wf VV) /\ True))) x_29182827 v_x_29182827))))).
Proof. 
	buildPackG length2 length2_rel length2__length2_rel length2_rel_funct. 
Defined.
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
Inductive PairL_u : Set := 
	 | MkPairL_u: L_u -> (L_u -> PairL_u). 
Fixpoint PairL_eq (x: PairL_u) (y: PairL_u): bool := 
	match (x, y) with (MkPairL_u x x_1, MkPairL_u x' x_1') => ((true && (x ==? x')) && (x_1 ==? x_1')) end. 
Definition PairL_eq_refl: (forall (x: PairL_u) , is_true (PairL_eq x x)). 
Proof. 
	eq_refl. 
Qed. 
#[global] Hint Resolve PairL_eq_refl : eq_hint_db.
Definition PairL_eqb_eq: (forall (s: PairL_u) (t: PairL_u) , (is_true (PairL_eq s t)) -> (s = t)). 
Proof. 
	eqb_eq_lem. 
Qed. 
#[global] Hint Resolve PairL_eqb_eq : eq_hint_db.
#[global] Instance leibnitz_eq_PairL : LeibnitzEqB := { 
	equalB' := PairL_eq;
	refl' := PairL_eq_refl;
	eqb_eq' := PairL_eqb_eq
}.
Fixpoint PairL_wf (x: PairL_u): Prop := 
	match x with (MkPairL_u VV VV_) => (((L_wf VV) /\ True) /\ ((L_wf VV_) /\ True)) end. 
Theorem PairL_wf_ref [p: PairL_u -> Prop] (tm: {v: PairL_u | (PairL_wf v) /\ (p v)}): PairL_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation PairL := {x: PairL_u | (PairL_wf x) /\ True}. 
Definition MkPairL_lem (VV: L) (VV_: L): (PairL_wf (MkPairL_u (⌊ VV -⌋) (⌊ VV_ -⌋))) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition MkPairL (VV: L) (VV_: L): PairL := 
	exist _ (MkPairL_u (⌊ VV -⌋) (⌊ VV_ -⌋)) (MkPairL_lem VV VV_). 
#[global] Hint Resolve PairL_wf_ref : wf_constr_db.
#[global] Hint Unfold PairL_wf : wf_constr_db.
#[global] Hint Resolve PairL_eq : ref_constr_db.
#[global] Hint Unfold MkPairL : ref_constr_db.
Definition unzip (l: L2): PairL. 
Proof. 
	destruct l as [l l_p]. 
	induction l as [(*App2*) ds_d2zv l IH_l | (*Emp2*) ]. 
	  - intros . 
		induction ds_d2zv as [(*MkPair*) x y]. 
		  -- intros . 
			let E := fresh "E" in 
			destruct (⌊ IH_l (ltac: (try clear IH_l; 
	solver)) -⌋) as [xs ys] eqn:E; [intros ; 
			refine (subsumptionCast _ _ 
		(MkPairL 
		(App (exist (fun (VV: Z) => True) x (ltac: (solver))) 
		(exist (fun (VV: L_u) => ((L_wf VV) /\ True)) xs (ltac: (solver)))) 
		(App (exist (fun (VV: Z) => True) y (ltac: (solver))) 
		(exist (fun (VV: L_u) => ((L_wf VV) /\ True)) ys (ltac: (solver))))) _); 
			solver].   
	  - intros . 
		refine (subsumptionCast _ _ 
		(MkPairL 
		(subsumptionCast L_u (fun (VV: L_u) => ((L_wf VV) /\ True)) Emp (ltac: (solver))) 
		(subsumptionCast L_u (fun (VV: L_u) => ((L_wf VV) /\ True)) Emp (ltac: (solver)))) _); 
		solver.  
Defined. 
Definition app_inj (x: {x: Z | True}) (y: {y: Z | True}) (xs: L) (ys: L) (p: {{(App_u (⌊ x -⌋) (⌊ xs -⌋)) == (App_u (⌊ y -⌋) (⌊ ys -⌋))}}): {{((⌊ x -⌋) = (⌊ y -⌋)) /\ ((⌊ xs -⌋) = (⌊ ys -⌋))}}. 
Proof. 
	destruct x as [x x_p]. 
	destruct y as [y y_p]. 
	destruct xs as [xs xs_p]. 
	destruct ys as [ys ys_p]. 
	destruct p as [p p_p]. 
	refine (exist _ unit _); 
	solver. 
Defined. 
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
Definition append_nonempty_xs (xs: L) (ys: L) (p: {{forall (appendres: L_u), (append_rel (⌊ xs -⌋) (⌊ ys -⌋) appendres) -> (appendres = Emp_u)}}): {{(⌊ xs -⌋) = Emp_u}}. 
Proof. 
	destruct xs as [xs xs_p]. 
	destruct ys as [ys ys_p]. 
	destruct p as [p p_p]. 
	try revert p_p; generalize dependent p; try revert ys_p; generalize dependent ys; 
	induction xs as [(*App*) lq_anf7205759403792803677 lq_anf7205759403792803678 IH_lq_anf7205759403792803678 | (*Emp*) ]. 
	  - intros . 
		refine (exist _ p _); 
		solver.  
	  - intros . 
		induction ys as [(*App*) lq_anf7205759403792803675 lq_anf7205759403792803676 IH_lq_anf7205759403792803676 | (*Emp*) ]. 
		  -- intros . 
			refine (exist _ p _); 
			solver.  
		  -- intros . 
			refine (exist _ unit _); 
			solver.   
Defined. 
Definition append_nonempty_ys (xs: L) (ys: L) (p: {{forall (appendres: L_u), (append_rel (⌊ xs -⌋) (⌊ ys -⌋) appendres) -> (appendres = Emp_u)}}): {{(⌊ ys -⌋) = Emp_u}}. 
Proof. 
	destruct xs as [xs xs_p]. 
	destruct ys as [ys ys_p]. 
	destruct p as [p p_p]. 
	try revert p_p; generalize dependent p; try revert ys_p; generalize dependent ys; 
	induction xs as [(*App*) lq_anf7205759403792803668 lq_anf7205759403792803669 IH_lq_anf7205759403792803669 | (*Emp*) ]. 
	  - intros . 
		refine (exist _ p _); 
		solver.  
	  - intros . 
		induction ys as [(*App*) lq_anf7205759403792803666 lq_anf7205759403792803667 IH_lq_anf7205759403792803667 | (*Emp*) ]. 
		  -- intros . 
			refine (exist _ p _); 
			solver.  
		  -- intros . 
			refine (exist _ unit _); 
			solver.   
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
Definition l2_pr1 (l: L2): L. 
Proof. 
	destruct l as [l l_p]. 
	induction l as [(*App2*) ds_d2z2 l IH_l | (*Emp2*) ]. 
	  - intros . 
		induction ds_d2z2 as [(*MkPair*) x ds_d2z3]. 
		  -- intros . 
			refine (subsumptionCast _ _ 
		(App (exist (fun (VV: Z) => True) x (ltac: (solver))) (IH_l (ltac: (try clear IH_l; 
	solver)))) _); 
			solver.   
	  - intros . 
		refine (subsumptionCast _ _ Emp _); 
		solver.  
Defined. 
Inductive l2_pr1_rel : (L2_u -> (L_u -> Prop)) := 
	 | l2_pr1_Emp2: l2_pr1_rel Emp2_u Emp_u
	 | l2_pr1_App2: (forall ds_d2z3 l x , forall (l2_pr1res: L_u), (l2_pr1_rel l l2_pr1res) -> (l2_pr1_rel (App2_u (MkPair_u x ds_d2z3) l) (App_u x l2_pr1res))). 
#[global] Hint Constructors l2_pr1_rel : core_hint_db.
#[global] Instance l2_pr1_lookup_rel : dictionary rel l2_pr1 := { 
	lookup' := l2_pr1_rel
}.
#[global] Instance l2_pr1_getF : getFunc l2_pr1_rel := { 
	getF' := l2_pr1
}.
Definition l2_pr1_rel_funct [l: L2_u]: (forall (VV: L_u) (VV': L_u) (H: l2_pr1_rel l VV) (K: l2_pr1_rel l VV') , VV = VV'). 
Proof. 
	induction l as [(*App2*) ds_d2z2 l IH_l | (*Emp2*) ]; 
	intros ; 
	[induction ds_d2z2 as [(*MkPair*) x ds_d2z3]; 
	intros | 
	]; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve l2_pr1_rel_funct : f_rel_funct_db.
Theorem l2_pr1_Emp2_lem: (l2_pr1_rel Emp2_u Emp_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite l2_pr1_Emp2_lem : f_rel_back.
Theorem l2_pr1_App2_lem (x: _) (ds_d2z3: _) (l: _) (l2_pr1res: L_u) (h_59309786: l2_pr1_rel l l2_pr1res): (l2_pr1_rel (App2_u (MkPair_u x ds_d2z3) l) (App_u x l2_pr1res)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite l2_pr1_App2_lem : f_rel_back.
Theorem l2_pr1_rel_ex (l: L2_u) (l_p: (L2_wf l) /\ True): l2_pr1_rel l (⌊ l2_pr1 (exist _ l l_p) -⌋). 
Proof. 
	existence_lemma_pre l2_pr1; 
	induction l as [(*App2*) ds_d2z2 l IH_l | (*Emp2*) ]; 
	intros ; 
	[induction ds_d2z2 as [(*MkPair*) x ds_d2z3]; 
	intros ; 
	[fix_notations; 
	pose proof (IH_l (ltac: (try clear IH_l; 
	solver))) as IH_12179161; 
	try clear IH_l]| 
	fix_notations]; 
	existence_lemma_quicksolve l2_pr1; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve l2_pr1_rel_ex : rel_ax_db.
Opaque l2_pr1. 
Theorem l2_pr1__l2_pr1_rel_rw (l: L2_u) (l_p: (L2_wf l) /\ True) (VV: L_u): ((⌊ l2_pr1 (exist _ l l_p) -⌋) = VV) <-> (l2_pr1_rel l VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite l2_pr1__l2_pr1_rel_rw : f_rel_funct_db.
#[global] Hint Resolve l2_pr1__l2_pr1_rel_rw : rel_ax_db.
#[global] Instance l2_pr1_lookup_rw : dictionary rwLem l2_pr1 := { 
	lookup' := l2_pr1__l2_pr1_rel_rw
}.
Theorem l2_pr1__l2_pr1_rel (l_r: L2) (VV: L_u): ((⌊ l2_pr1 l_r -⌋) = VV) <-> (l2_pr1_rel (⌊ l_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite l2_pr1__l2_pr1_rel : f_rel_funct_db.
Theorem l2_pr1__l2_pr1_rel' (l: L2_u) (l_r: L2) (VV: L_u): (l = (⌊ l_r -⌋)) -> (((⌊ l2_pr1 l_r -⌋) = VV) <-> (l2_pr1_rel l VV)). 
Proof. 
	intros ->. 
	refine (l2_pr1__l2_pr1_rel l_r VV). 
Qed. 
#[global] Hint Resolve l2_pr1__l2_pr1_rel' : f_rel_funct_db.
Definition l2_pr1_rel_mk [l: L2_u] (l_p: (L2_wf l) /\ True): {VV: _ | l2_pr1_rel l VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (l2_pr1_rel l VV)) (l2_pr1 (exist _ l l_p)) _); 
	rewrite <- l2_pr1__l2_pr1_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve l2_pr1_rel_mk : f_rel_funct_db.
#[global] Instance l2_pr1Pack : (@Pack (L2 ::RT (fun (l_r: L2) => nilRT)) (L2_u ::UT nilUT) (ltac: (mkProjectsArgListTG (L2 ::RT (fun (l_r: L2) => nilRT)) (L2_u ::UT nilUT))) L_u (fun (x_29182827: (ArgList L2 ::RT (fun (l_r: L2) => nilRT))) => (fun (v_x_29182827: L_u) => (ltac: (flattenP (fun (l_r: L2) => (fun (VV: L_u) => ((L_wf VV) /\ True))) x_29182827 v_x_29182827))))).
Proof. 
	buildPackG l2_pr1 l2_pr1_rel l2_pr1__l2_pr1_rel l2_pr1_rel_funct. 
Defined.
Definition l2_pr2 (l: L2): L. 
Proof. 
	destruct l as [l l_p]. 
	induction l as [(*App2*) ds_d2yX l IH_l | (*Emp2*) ]. 
	  - intros . 
		induction ds_d2yX as [(*MkPair*) ds_d2yY y]. 
		  -- intros . 
			refine (subsumptionCast _ _ 
		(App (exist (fun (VV: Z) => True) y (ltac: (solver))) (IH_l (ltac: (try clear IH_l; 
	solver)))) _); 
			solver.   
	  - intros . 
		refine (subsumptionCast _ _ Emp _); 
		solver.  
Defined. 
Inductive l2_pr2_rel : (L2_u -> (L_u -> Prop)) := 
	 | l2_pr2_Emp2: l2_pr2_rel Emp2_u Emp_u
	 | l2_pr2_App2: (forall ds_d2yY l y , forall (l2_pr2res: L_u), (l2_pr2_rel l l2_pr2res) -> (l2_pr2_rel (App2_u (MkPair_u ds_d2yY y) l) (App_u y l2_pr2res))). 
#[global] Hint Constructors l2_pr2_rel : core_hint_db.
#[global] Instance l2_pr2_lookup_rel : dictionary rel l2_pr2 := { 
	lookup' := l2_pr2_rel
}.
#[global] Instance l2_pr2_getF : getFunc l2_pr2_rel := { 
	getF' := l2_pr2
}.
Definition l2_pr2_rel_funct [l: L2_u]: (forall (VV: L_u) (VV': L_u) (H: l2_pr2_rel l VV) (K: l2_pr2_rel l VV') , VV = VV'). 
Proof. 
	induction l as [(*App2*) ds_d2yX l IH_l | (*Emp2*) ]; 
	intros ; 
	[induction ds_d2yX as [(*MkPair*) ds_d2yY y]; 
	intros | 
	]; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve l2_pr2_rel_funct : f_rel_funct_db.
Theorem l2_pr2_Emp2_lem: (l2_pr2_rel Emp2_u Emp_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite l2_pr2_Emp2_lem : f_rel_back.
Theorem l2_pr2_App2_lem (ds_d2yY: _) (y: _) (l: _) (l2_pr2res: L_u) (h_15598697: l2_pr2_rel l l2_pr2res): (l2_pr2_rel (App2_u (MkPair_u ds_d2yY y) l) (App_u y l2_pr2res)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite l2_pr2_App2_lem : f_rel_back.
Theorem l2_pr2_rel_ex (l: L2_u) (l_p: (L2_wf l) /\ True): l2_pr2_rel l (⌊ l2_pr2 (exist _ l l_p) -⌋). 
Proof. 
	existence_lemma_pre l2_pr2; 
	induction l as [(*App2*) ds_d2yX l IH_l | (*Emp2*) ]; 
	intros ; 
	[induction ds_d2yX as [(*MkPair*) ds_d2yY y]; 
	intros ; 
	[fix_notations; 
	pose proof (IH_l (ltac: (try clear IH_l; 
	solver))) as IH_12179161; 
	try clear IH_l]| 
	fix_notations]; 
	existence_lemma_quicksolve l2_pr2; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve l2_pr2_rel_ex : rel_ax_db.
Opaque l2_pr2. 
Theorem l2_pr2__l2_pr2_rel_rw (l: L2_u) (l_p: (L2_wf l) /\ True) (VV: L_u): ((⌊ l2_pr2 (exist _ l l_p) -⌋) = VV) <-> (l2_pr2_rel l VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite l2_pr2__l2_pr2_rel_rw : f_rel_funct_db.
#[global] Hint Resolve l2_pr2__l2_pr2_rel_rw : rel_ax_db.
#[global] Instance l2_pr2_lookup_rw : dictionary rwLem l2_pr2 := { 
	lookup' := l2_pr2__l2_pr2_rel_rw
}.
Theorem l2_pr2__l2_pr2_rel (l_r: L2) (VV: L_u): ((⌊ l2_pr2 l_r -⌋) = VV) <-> (l2_pr2_rel (⌊ l_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite l2_pr2__l2_pr2_rel : f_rel_funct_db.
Theorem l2_pr2__l2_pr2_rel' (l: L2_u) (l_r: L2) (VV: L_u): (l = (⌊ l_r -⌋)) -> (((⌊ l2_pr2 l_r -⌋) = VV) <-> (l2_pr2_rel l VV)). 
Proof. 
	intros ->. 
	refine (l2_pr2__l2_pr2_rel l_r VV). 
Qed. 
#[global] Hint Resolve l2_pr2__l2_pr2_rel' : f_rel_funct_db.
Definition l2_pr2_rel_mk [l: L2_u] (l_p: (L2_wf l) /\ True): {VV: _ | l2_pr2_rel l VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (l2_pr2_rel l VV)) (l2_pr2 (exist _ l l_p)) _); 
	rewrite <- l2_pr2__l2_pr2_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve l2_pr2_rel_mk : f_rel_funct_db.
#[global] Instance l2_pr2Pack : (@Pack (L2 ::RT (fun (l_r: L2) => nilRT)) (L2_u ::UT nilUT) (ltac: (mkProjectsArgListTG (L2 ::RT (fun (l_r: L2) => nilRT)) (L2_u ::UT nilUT))) L_u (fun (x_29182827: (ArgList L2 ::RT (fun (l_r: L2) => nilRT))) => (fun (v_x_29182827: L_u) => (ltac: (flattenP (fun (l_r: L2) => (fun (VV: L_u) => ((L_wf VV) /\ True))) x_29182827 v_x_29182827))))).
Proof. 
	buildPackG l2_pr2 l2_pr2_rel l2_pr2__l2_pr2_rel l2_pr2_rel_funct. 
Defined.
Definition length (l: L): Nats. 
Proof. 
	destruct l as [l l_p]. 
	induction l as [(*App*) ds_d2zk xs IH_xs | (*Emp*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ 
		(Suc 
		(subsumptionCast Nats_u (fun (n: Nats_u) => ((Nats_wf n) /\ True)) (IH_xs (ltac: (try clear IH_xs; 
	solver))) (ltac: (solver)))) _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ Zero _); 
		solver.  
Defined. 
Inductive length_rel : (L_u -> (Nats_u -> Prop)) := 
	 | length_Emp: length_rel Emp_u Zero_u
	 | length_App: (forall ds_d2zk xs , forall (lengthres: Nats_u), (length_rel xs lengthres) -> (length_rel (App_u ds_d2zk xs) (Suc_u lengthres))). 
#[global] Hint Constructors length_rel : core_hint_db.
#[global] Instance length_lookup_rel : dictionary rel length := { 
	lookup' := length_rel
}.
#[global] Instance length_getF : getFunc length_rel := { 
	getF' := length
}.
Definition length_rel_funct [l: L_u]: (forall (VV: Nats_u) (VV': Nats_u) (H: length_rel l VV) (K: length_rel l VV') , VV = VV'). 
Proof. 
	induction l as [(*App*) ds_d2zk xs IH_xs | (*Emp*) ]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve length_rel_funct : f_rel_funct_db.
Theorem length_Emp_lem: (length_rel Emp_u Zero_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite length_Emp_lem : f_rel_back.
Theorem length_App_lem (ds_d2zk: _) (xs: _) (lengthres: Nats_u) (h_57695211: length_rel xs lengthres): (length_rel (App_u ds_d2zk xs) (Suc_u lengthres)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite length_App_lem : f_rel_back.
Theorem length_rel_ex (l: L_u) (l_p: (L_wf l) /\ True): length_rel l (⌊ length (exist _ l l_p) -⌋). 
Proof. 
	existence_lemma_pre length; 
	induction l as [(*App*) ds_d2zk xs IH_xs | (*Emp*) ]; 
	intros ; 
	[fix_notations; 
	pose proof (IH_xs (ltac: (try clear IH_xs; 
	solver))) as IH_55394889; 
	try clear IH_xs| 
	fix_notations]; 
	existence_lemma_quicksolve length; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve length_rel_ex : rel_ax_db.
Opaque length. 
Theorem length__length_rel_rw (l: L_u) (l_p: (L_wf l) /\ True) (VV: Nats_u): ((⌊ length (exist _ l l_p) -⌋) = VV) <-> (length_rel l VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite length__length_rel_rw : f_rel_funct_db.
#[global] Hint Resolve length__length_rel_rw : rel_ax_db.
#[global] Instance length_lookup_rw : dictionary rwLem length := { 
	lookup' := length__length_rel_rw
}.
Theorem length__length_rel (l_r: L) (VV: Nats_u): ((⌊ length l_r -⌋) = VV) <-> (length_rel (⌊ l_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite length__length_rel : f_rel_funct_db.
Theorem length__length_rel' (l: L_u) (l_r: L) (VV: Nats_u): (l = (⌊ l_r -⌋)) -> (((⌊ length l_r -⌋) = VV) <-> (length_rel l VV)). 
Proof. 
	intros ->. 
	refine (length__length_rel l_r VV). 
Qed. 
#[global] Hint Resolve length__length_rel' : f_rel_funct_db.
Definition length_rel_mk [l: L_u] (l_p: (L_wf l) /\ True): {VV: _ | length_rel l VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (length_rel l VV)) (length (exist _ l l_p)) _); 
	rewrite <- length__length_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve length_rel_mk : f_rel_funct_db.
#[global] Instance lengthPack : (@Pack (L ::RT (fun (l_r: L) => nilRT)) (L_u ::UT nilUT) (ltac: (mkProjectsArgListTG (L ::RT (fun (l_r: L) => nilRT)) (L_u ::UT nilUT))) Nats_u (fun (x_41603409: (ArgList L ::RT (fun (l_r: L) => nilRT))) => (fun (v_x_41603409: Nats_u) => (ltac: (flattenP (fun (l_r: L) => (fun (VV: Nats_u) => ((Nats_wf VV) /\ True))) x_41603409 v_x_41603409))))).
Proof. 
	buildPackG length length_rel length__length_rel length_rel_funct. 
Defined.
Definition length_unzip_1 (l: L2): {{forall (length2res: Nats_u), (length2_rel (⌊ l -⌋) length2res) -> (forall (l2_pr1res: L_u), (l2_pr1_rel (⌊ l -⌋) l2_pr1res) -> (forall (lengthres: Nats_u), (length_rel l2_pr1res lengthres) -> (length2res == lengthres)))}}. 
Proof. 
	destruct l as [l l_p]. 
	induction l as [(*App2*) ds_d2yT l IH_l | (*Emp2*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ (IH_l (ltac: (try clear IH_l; 
	solver))) _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
Defined. 
Definition length_unzip_2 (l: L2): {{forall (length2res: Nats_u), (length2_rel (⌊ l -⌋) length2res) -> (forall (l2_pr2res: L_u), (l2_pr2_rel (⌊ l -⌋) l2_pr2res) -> (forall (lengthres: Nats_u), (length_rel l2_pr2res lengthres) -> (length2res == lengthres)))}}. 
Proof. 
	destruct l as [l l_p]. 
	induction l as [(*App2*) ds_d2yR l IH_l | (*Emp2*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ (IH_l (ltac: (try clear IH_l; 
	solver))) _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
Defined. 
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
Definition length_map (f: (@Pack ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_86410777: (ArgList {lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => nilRT))) => (fun (v_x_86410777: Z) => (ltac: (flattenP (fun (lq_tmp0: {lq_tmp0: Z | True}) => (fun (VV: Z) => True)) x_86410777 v_x_86410777)))))) (l: L): {{forall (mapres: L_u), (map_rel (packProj f) (⌊ l -⌋) mapres) -> (forall (lengthres: Nats_u), (length_rel mapres lengthres) -> (forall (length_res_2: Nats_u), (length_rel (⌊ l -⌋) length_res_2) -> (lengthres == length_res_2)))}}. 
Proof. 
	destruct l as [l l_p]. 
	try revert f_p; generalize dependent f; 
	induction l as [(*App*) x xs IH_xs | (*Emp*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ (IH_xs (ltac: (try clear IH_xs; 
	solver)) f) _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
Defined. 
Definition reverse (l: L): L. 
Proof. 
	destruct l as [l l_p]. 
	induction l as [(*App*) x xs IH_xs | (*Emp*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ 
		(append 
		(subsumptionCast L_u (fun (lq_tmp0: L_u) => ((L_wf lq_tmp0) /\ True)) (IH_xs (ltac: (try clear IH_xs; 
	solver))) (ltac: (solver))) 
		(subsumptionCast L_u (fun (lq_tmp1: L_u) => ((L_wf lq_tmp1) /\ True)) 
		(App (exist (fun (VV: Z) => True) x (ltac: (solver))) 
		(subsumptionCast L_u (fun (VV: L_u) => ((L_wf VV) /\ True)) Emp (ltac: (solver)))) (ltac: (solver)))) _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ Emp _); 
		solver.  
Defined. 
Inductive reverse_rel : (L_u -> (L_u -> Prop)) := 
	 | reverse_Emp: reverse_rel Emp_u Emp_u
	 | reverse_App: (forall x xs , forall (reverseres: L_u), (reverse_rel xs reverseres) -> (forall (appendres: L_u), (append_rel reverseres (App_u x Emp_u) appendres) -> (reverse_rel (App_u x xs) appendres))). 
#[global] Hint Constructors reverse_rel : core_hint_db.
#[global] Instance reverse_lookup_rel : dictionary rel reverse := { 
	lookup' := reverse_rel
}.
#[global] Instance reverse_getF : getFunc reverse_rel := { 
	getF' := reverse
}.
Definition reverse_rel_funct [l: L_u]: (forall (VV: L_u) (VV': L_u) (H: reverse_rel l VV) (K: reverse_rel l VV') , VV = VV'). 
Proof. 
	induction l as [(*App*) x xs IH_xs | (*Emp*) ]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve reverse_rel_funct : f_rel_funct_db.
Theorem reverse_Emp_lem: (reverse_rel Emp_u Emp_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite reverse_Emp_lem : f_rel_back.
Theorem reverse_App_lem (x: _) (xs: _) (appendres: L_u): (reverse_rel (App_u x xs) appendres) <-> (exists (reverseres: L_u), (reverse_rel xs reverseres) /\ (append_rel reverseres (App_u x Emp_u) appendres)). 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite reverse_App_lem : f_rel_back.
Theorem reverse_rel_ex (l: L_u) (l_p: (L_wf l) /\ True): reverse_rel l (⌊ reverse (exist _ l l_p) -⌋). 
Proof. 
	existence_lemma_pre reverse; 
	induction l as [(*App*) x xs IH_xs | (*Emp*) ]; 
	intros ; 
	[fix_notations; 
	pose proof (IH_xs (ltac: (try clear IH_xs; 
	solver))) as IH_55394889; 
	try clear IH_xs| 
	fix_notations]; 
	existence_lemma_quicksolve reverse; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve reverse_rel_ex : rel_ax_db.
Opaque reverse. 
Theorem reverse__reverse_rel_rw (l: L_u) (l_p: (L_wf l) /\ True) (VV: L_u): ((⌊ reverse (exist _ l l_p) -⌋) = VV) <-> (reverse_rel l VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite reverse__reverse_rel_rw : f_rel_funct_db.
#[global] Hint Resolve reverse__reverse_rel_rw : rel_ax_db.
#[global] Instance reverse_lookup_rw : dictionary rwLem reverse := { 
	lookup' := reverse__reverse_rel_rw
}.
Theorem reverse__reverse_rel (l_r: L) (VV: L_u): ((⌊ reverse l_r -⌋) = VV) <-> (reverse_rel (⌊ l_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite reverse__reverse_rel : f_rel_funct_db.
Theorem reverse__reverse_rel' (l: L_u) (l_r: L) (VV: L_u): (l = (⌊ l_r -⌋)) -> (((⌊ reverse l_r -⌋) = VV) <-> (reverse_rel l VV)). 
Proof. 
	intros ->. 
	refine (reverse__reverse_rel l_r VV). 
Qed. 
#[global] Hint Resolve reverse__reverse_rel' : f_rel_funct_db.
Definition reverse_rel_mk [l: L_u] (l_p: (L_wf l) /\ True): {VV: _ | reverse_rel l VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (reverse_rel l VV)) (reverse (exist _ l l_p)) _); 
	rewrite <- reverse__reverse_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve reverse_rel_mk : f_rel_funct_db.
#[global] Instance reversePack : (@Pack (L ::RT (fun (l_r: L) => nilRT)) (L_u ::UT nilUT) (ltac: (mkProjectsArgListTG (L ::RT (fun (l_r: L) => nilRT)) (L_u ::UT nilUT))) L_u (fun (x_41603409: (ArgList L ::RT (fun (l_r: L) => nilRT))) => (fun (v_x_41603409: L_u) => (ltac: (flattenP (fun (l_r: L) => (fun (VV: L_u) => ((L_wf VV) /\ True))) x_41603409 v_x_41603409))))).
Proof. 
	buildPackG reverse reverse_rel reverse__reverse_rel reverse_rel_funct. 
Defined.
Definition reverse_nonempty (l: L) (p: {{forall (reverseres: L_u), (reverse_rel (⌊ l -⌋) reverseres) -> (reverseres = Emp_u)}}): {{(⌊ l -⌋) = Emp_u}}. 
Proof. 
	destruct l as [l l_p]. 
	destruct p as [p p_p]. 
	try revert p_p; generalize dependent p; 
	induction l as [(*App*) x xs IH_xs | (*Emp*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ 
		(append_nonempty_ys 
		(subsumptionCast L_u (fun (xs: L_u) => ((L_wf xs) /\ True)) 
		(reverse 
		(exist (fun (l: L_u) => ((L_wf l) /\ True)) xs (ltac: (solver)))) (ltac: (solver))) 
		(subsumptionCast L_u (fun (ys: L_u) => ((L_wf ys) /\ True)) 
		(App (exist (fun (VV: Z) => True) x (ltac: (solver))) 
		(subsumptionCast L_u (fun (VV: L_u) => ((L_wf VV) /\ True)) Emp (ltac: (solver)))) (ltac: (solver))) 
		(exist (fun (p: Unit) => (forall (appendres: L_u), (append_rel 
		(⌊ reverse 
		(exist (fun (l: L_u) => ((L_wf l) /\ True)) xs (ltac: (solver))) -⌋) (App_u x Emp_u) appendres) -> (appendres = Emp_u))) p (ltac: (solver)))) _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
Defined. 
Definition take (n: Nats) (l: L): L. 
Proof. 
	destruct n as [n n_p]. 
	destruct l as [l l_p]. 
	try revert l_p; generalize dependent l; 
	induction n as [(*Suc*) n IH_n | (*Zero*) ]. 
	  - intros . 
		induction l as [(*App*) x xs IH_xs | (*Emp*) ]. 
		  -- intros . 
			refine (subsumptionCast _ _ 
		(App (exist (fun (VV: Z) => True) x (ltac: (solver))) 
		(IH_n (ltac: (try clear IH_n; 
	solver)) xs (ltac: (try clear IH_n; 
	solver)))) _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Emp _); 
			solver.   
	  - intros . 
		refine (subsumptionCast _ _ Emp _); 
		solver.  
Defined. 
Inductive take_rel : (Nats_u -> (L_u -> (L_u -> Prop))) := 
	 | take_Zero: (forall l , take_rel Zero_u l Emp_u)
	 | take_Suc_Emp: (forall n , take_rel (Suc_u n) Emp_u Emp_u)
	 | take_Suc_App: (forall n x xs , forall (takeres: L_u), (take_rel n xs takeres) -> (take_rel (Suc_u n) (App_u x xs) (App_u x takeres))). 
#[global] Hint Constructors take_rel : core_hint_db.
#[global] Instance take_lookup_rel : dictionary rel take := { 
	lookup' := take_rel
}.
#[global] Instance take_getF : getFunc take_rel := { 
	getF' := take
}.
Definition take_rel_funct [n: Nats_u] [l: L_u]: (forall (VV: L_u) (VV': L_u) (H: take_rel n l VV) (K: take_rel n l VV') , VV = VV'). 
Proof. 
	try revert l_p; generalize dependent l; 
	induction n as [(*Suc*) n IH_n | (*Zero*) ]; 
	intros ; 
	[induction l as [(*App*) x xs IH_xs | (*Emp*) ]; 
	intros | 
	]; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve take_rel_funct : f_rel_funct_db.
Theorem take_Zero_lem (l: _): (take_rel Zero_u l Emp_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite take_Zero_lem : f_rel_back.
Theorem take_Suc_Emp_lem (n: _): (take_rel (Suc_u n) Emp_u Emp_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite take_Suc_Emp_lem : f_rel_back.
Theorem take_Suc_App_lem (n: _) (x: _) (xs: _) (takeres: L_u) (h_81657627: take_rel n xs takeres): (take_rel (Suc_u n) (App_u x xs) (App_u x takeres)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite take_Suc_App_lem : f_rel_back.
Theorem take_rel_ex (n: Nats_u) (l: L_u) (n_p: (Nats_wf n) /\ True) (l_p: (L_wf l) /\ True): take_rel n l (⌊ take (exist _ n n_p) (exist _ l l_p) -⌋). 
Proof. 
	existence_lemma_pre take; 
	try revert l_p; generalize dependent l; 
	induction n as [(*Suc*) n IH_n | (*Zero*) ]; 
	intros ; 
	[induction l as [(*App*) x xs IH_xs | (*Emp*) ]; 
	intros ; 
	[fix_notations; 
	pose proof (IH_n (ltac: (try clear IH_n; 
	solver)) xs (ltac: (try clear IH_n; 
	solver))) as IH_20771368; 
	try clear IH_n; 
	try clear IH_xs| 
	fix_notations; 
	try clear IH_n]| 
	fix_notations]; 
	existence_lemma_quicksolve take; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve take_rel_ex : rel_ax_db.
Opaque take. 
Theorem take__take_rel_rw (n: Nats_u) (l: L_u) (n_p: (Nats_wf n) /\ True) (l_p: (L_wf l) /\ True) (VV: L_u): ((⌊ take (exist _ n n_p) (exist _ l l_p) -⌋) = VV) <-> (take_rel n l VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite take__take_rel_rw : f_rel_funct_db.
#[global] Hint Resolve take__take_rel_rw : rel_ax_db.
#[global] Instance take_lookup_rw : dictionary rwLem take := { 
	lookup' := take__take_rel_rw
}.
Theorem take__take_rel (n_r: Nats) (l_r: L) (VV: L_u): ((⌊ take n_r l_r -⌋) = VV) <-> (take_rel (⌊ n_r -⌋) (⌊ l_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite take__take_rel : f_rel_funct_db.
Theorem take__take_rel' (n: Nats_u) (l: L_u) (n_r: Nats) (l_r: L) (VV: L_u): (n = (⌊ n_r -⌋)) -> ((l = (⌊ l_r -⌋)) -> (((⌊ take n_r l_r -⌋) = VV) <-> (take_rel n l VV))). 
Proof. 
	intros -> ->. 
	refine (take__take_rel n_r l_r VV). 
Qed. 
#[global] Hint Resolve take__take_rel' : f_rel_funct_db.
Definition take_rel_mk [n: Nats_u] [l: L_u] (n_p: (Nats_wf n) /\ True) (l_p: (L_wf l) /\ True): {VV: _ | take_rel n l VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (take_rel n l VV)) (take (exist _ n n_p) (exist _ l l_p)) _); 
	rewrite <- take__take_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve take_rel_mk : f_rel_funct_db.
#[global] Instance takePack : (@Pack (Nats ::RT (fun (n_r: Nats) => (L ::RT (fun (l_r: L) => nilRT)))) (Nats_u ::UT (L_u ::UT nilUT)) (ltac: (mkProjectsArgListTG (Nats ::RT (fun (n_r: Nats) => (L ::RT (fun (l_r: L) => nilRT)))) (Nats_u ::UT (L_u ::UT nilUT)))) L_u (fun (x_18732454: (ArgList Nats ::RT (fun (n_r: Nats) => (L ::RT (fun (l_r: L) => nilRT))))) => (fun (v_x_18732454: L_u) => (ltac: (flattenP (fun (n_r: Nats) => (fun (l_r: L) => (fun (VV: L_u) => ((L_wf VV) /\ True)))) x_18732454 v_x_18732454))))).
Proof. 
	buildPackG take take_rel take__take_rel take_rel_funct. 
Defined.
Definition take_all (n: Nats) (l: {l: L_u | (L_wf l) /\ (forall (lengthres: Nats_u), (length_rel l lengthres) -> (geqN_rel (⌊ n -⌋) lengthres true))}): {{forall (takeres: L_u), (take_rel (⌊ n -⌋) (⌊ l -⌋) takeres) -> (takeres = (⌊ l -⌋))}}. 
Proof. 
	destruct n as [n n_p]. 
	destruct l as [l l_p]. 
	try revert l_p; generalize dependent l; 
	induction n as [(*Suc*) n IH_n | (*Zero*) ]. 
	  - intros . 
		induction l as [(*App*) x xs IH_xs | (*Emp*) ]. 
		  -- intros . 
			refine (subsumptionCast _ _ 
		(IH_n (ltac: (try clear IH_n; 
	solver)) xs (ltac: (try clear IH_n; 
	solver))) _); 
			solver.  
		  -- intros . 
			refine (exist _ unit _); 
			solver.   
	  - intros . 
		induction l as [(*App*) lq_anf7205759403792803801 lq_anf7205759403792803802 IH_lq_anf7205759403792803802 | (*Emp*) ]. 
		  -- intros . 
			intros ; 
			exfalso; 
			solver.  
		  -- intros . 
			refine (exist _ unit _); 
			solver.   
Defined. 
Definition zip (lq_tmp0: L) (lq_tmp1: L): L2. 
Proof. 
	destruct lq_tmp0 as [lq_tmp0 lq_tmp0_p]. 
	destruct lq_tmp1 as [lq_tmp1 lq_tmp1_p]. 
	try revert lq_tmp1_p; generalize dependent lq_tmp1; 
	induction lq_tmp0 as [(*App*) x xs IH_xs | (*Emp*) ]. 
	  - intros . 
		induction lq_tmp1 as [(*App*) y ys IH_ys | (*Emp*) ]. 
		  -- intros . 
			refine (subsumptionCast _ _ 
		(App2 
		(MkPair (exist (fun (VV: Z) => True) x (ltac: (solver))) (exist (fun (VV: Z) => True) y (ltac: (solver)))) 
		(IH_xs (ltac: (try clear IH_xs; 
	solver)) ys (ltac: (try clear IH_xs; 
	solver)))) _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Emp2 _); 
			solver.   
	  - intros . 
		refine (subsumptionCast _ _ Emp2 _); 
		solver.  
Defined. 
Inductive zip_rel : (L_u -> (L_u -> (L2_u -> Prop))) := 
	 | zip_Emp: (forall lq_tmp1 , zip_rel Emp_u lq_tmp1 Emp2_u)
	 | zip_App_Emp: (forall x xs , zip_rel (App_u x xs) Emp_u Emp2_u)
	 | zip_App_App: (forall x xs y ys , forall (zipres: L2_u), (zip_rel xs ys zipres) -> (zip_rel (App_u x xs) (App_u y ys) (App2_u (MkPair_u x y) zipres))). 
#[global] Hint Constructors zip_rel : core_hint_db.
#[global] Instance zip_lookup_rel : dictionary rel zip := { 
	lookup' := zip_rel
}.
#[global] Instance zip_getF : getFunc zip_rel := { 
	getF' := zip
}.
Definition zip_rel_funct [lq_tmp0: L_u] [lq_tmp1: L_u]: (forall (VV: L2_u) (VV': L2_u) (H: zip_rel lq_tmp0 lq_tmp1 VV) (K: zip_rel lq_tmp0 lq_tmp1 VV') , VV = VV'). 
Proof. 
	try revert lq_tmp1_p; generalize dependent lq_tmp1; 
	induction lq_tmp0 as [(*App*) x xs IH_xs | (*Emp*) ]; 
	intros ; 
	[induction lq_tmp1 as [(*App*) y ys IH_ys | (*Emp*) ]; 
	intros | 
	]; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve zip_rel_funct : f_rel_funct_db.
Theorem zip_Emp_lem (lq_tmp1: _): (zip_rel Emp_u lq_tmp1 Emp2_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite zip_Emp_lem : f_rel_back.
Theorem zip_App_Emp_lem (x: _) (xs: _): (zip_rel (App_u x xs) Emp_u Emp2_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite zip_App_Emp_lem : f_rel_back.
Theorem zip_App_App_lem (x: _) (xs: _) (y: _) (ys: _) (zipres: L2_u) (h_30299140: zip_rel xs ys zipres): (zip_rel (App_u x xs) (App_u y ys) (App2_u (MkPair_u x y) zipres)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite zip_App_App_lem : f_rel_back.
Theorem zip_rel_ex (lq_tmp0: L_u) (lq_tmp1: L_u) (lq_tmp0_p: (L_wf lq_tmp0) /\ True) (lq_tmp1_p: (L_wf lq_tmp1) /\ True): zip_rel lq_tmp0 lq_tmp1 
		(⌊ zip (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p) -⌋). 
Proof. 
	existence_lemma_pre zip; 
	try revert lq_tmp1_p; generalize dependent lq_tmp1; 
	induction lq_tmp0 as [(*App*) x xs IH_xs | (*Emp*) ]; 
	intros ; 
	[induction lq_tmp1 as [(*App*) y ys IH_ys | (*Emp*) ]; 
	intros ; 
	[fix_notations; 
	pose proof (IH_xs (ltac: (try clear IH_xs; 
	solver)) ys (ltac: (try clear IH_xs; 
	solver))) as IH_46568342; 
	try clear IH_xs; 
	try clear IH_ys| 
	fix_notations; 
	try clear IH_xs]| 
	fix_notations]; 
	existence_lemma_quicksolve zip; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve zip_rel_ex : rel_ax_db.
Opaque zip. 
Theorem zip__zip_rel_rw (lq_tmp0: L_u) (lq_tmp1: L_u) (lq_tmp0_p: (L_wf lq_tmp0) /\ True) (lq_tmp1_p: (L_wf lq_tmp1) /\ True) (VV: L2_u): ((⌊ zip (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p) -⌋) = VV) <-> (zip_rel lq_tmp0 lq_tmp1 VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite zip__zip_rel_rw : f_rel_funct_db.
#[global] Hint Resolve zip__zip_rel_rw : rel_ax_db.
#[global] Instance zip_lookup_rw : dictionary rwLem zip := { 
	lookup' := zip__zip_rel_rw
}.
Theorem zip__zip_rel (lq_tmp0_r: L) (lq_tmp1_r: L) (VV: L2_u): ((⌊ zip lq_tmp0_r lq_tmp1_r -⌋) = VV) <-> (zip_rel (⌊ lq_tmp0_r -⌋) (⌊ lq_tmp1_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite zip__zip_rel : f_rel_funct_db.
Theorem zip__zip_rel' (lq_tmp0: L_u) (lq_tmp1: L_u) (lq_tmp0_r: L) (lq_tmp1_r: L) (VV: L2_u): (lq_tmp0 = (⌊ lq_tmp0_r -⌋)) -> ((lq_tmp1 = (⌊ lq_tmp1_r -⌋)) -> (((⌊ zip lq_tmp0_r lq_tmp1_r -⌋) = VV) <-> (zip_rel lq_tmp0 lq_tmp1 VV))). 
Proof. 
	intros -> ->. 
	refine (zip__zip_rel lq_tmp0_r lq_tmp1_r VV). 
Qed. 
#[global] Hint Resolve zip__zip_rel' : f_rel_funct_db.
Definition zip_rel_mk [lq_tmp0: L_u] [lq_tmp1: L_u] (lq_tmp0_p: (L_wf lq_tmp0) /\ True) (lq_tmp1_p: (L_wf lq_tmp1) /\ True): {VV: _ | zip_rel lq_tmp0 lq_tmp1 VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (zip_rel lq_tmp0 lq_tmp1 VV)) 
		(zip (exist _ lq_tmp0 lq_tmp0_p) (exist _ lq_tmp1 lq_tmp1_p)) _); 
	rewrite <- zip__zip_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve zip_rel_mk : f_rel_funct_db.
#[global] Instance zipPack : (@Pack (L ::RT (fun (lq_tmp0_r: L) => (L ::RT (fun (lq_tmp1_r: L) => nilRT)))) (L_u ::UT (L_u ::UT nilUT)) (ltac: (mkProjectsArgListTG (L ::RT (fun (lq_tmp0_r: L) => (L ::RT (fun (lq_tmp1_r: L) => nilRT)))) (L_u ::UT (L_u ::UT nilUT)))) L2_u (fun (x_46281847: (ArgList L ::RT (fun (lq_tmp0_r: L) => (L ::RT (fun (lq_tmp1_r: L) => nilRT))))) => (fun (v_x_46281847: L2_u) => (ltac: (flattenP (fun (lq_tmp0_r: L) => (fun (lq_tmp1_r: L) => (fun (VV: L2_u) => ((L2_wf VV) /\ True)))) x_46281847 v_x_46281847))))).
Proof. 
	buildPackG zip zip_rel zip__zip_rel zip_rel_funct. 
Defined.
Definition length_zip (n: Nats) (l: {l: L_u | (L_wf l) /\ (forall (lengthres: Nats_u), (length_rel l lengthres) -> (lengthres = (⌊ n -⌋)))}) (m: {m: L_u | (L_wf m) /\ (forall (lengthres: Nats_u), (length_rel m lengthres) -> (lengthres = (⌊ n -⌋)))}): {{forall (zipres: L2_u), (zip_rel (⌊ l -⌋) (⌊ m -⌋) zipres) -> (forall (length2res: Nats_u), (length2_rel zipres length2res) -> (length2res = (⌊ n -⌋)))}}. 
Proof. 
	destruct n as [n n_p]. 
	destruct l as [l l_p]. 
	destruct m as [m m_p]. 
	try revert m_p; generalize dependent m; try revert l_p; generalize dependent l; 
	induction n as [(*Suc*) n IH_n | (*Zero*) ]. 
	  - intros . 
		induction l as [(*App*) x xs IH_xs | (*Emp*) ]. 
		  -- intros . 
			induction m as [(*App*) y ys IH_ys | (*Emp*) ]. 
			  --- intros . 
				refine (subsumptionCast _ _ 
		(IH_n (ltac: (try clear IH_n; 
	solver)) xs (ltac: (try clear IH_n; 
	solver)) ys (ltac: (try clear IH_n; 
	solver))) _); 
				solver.  
			  --- intros . 
				intros ; 
				exfalso; 
				solver.   
		  -- intros . 
			intros ; 
			exfalso; 
			solver.   
	  - intros . 
		induction l as [(*App*) lq_anf7205759403792803732 lq_anf7205759403792803733 IH_lq_anf7205759403792803733 | (*Emp*) ]. 
		  -- intros . 
			intros ; 
			exfalso; 
			solver.  
		  -- intros . 
			induction m as [(*App*) lq_anf7205759403792803730 lq_anf7205759403792803731 IH_lq_anf7205759403792803731 | (*Emp*) ]. 
			  --- intros . 
				intros ; 
				exfalso; 
				solver.  
			  --- intros . 
				refine (exist _ unit _); 
				solver.    
Defined. 
Definition length_zipWith (n: Nats) (f: (@Pack ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)) (ltac: (mkProjectsArgListTG ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)))) Z (fun (x_33150792: (ArgList {lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))))) => (fun (v_x_33150792: Z) => (ltac: (flattenP (fun (lq_tmp0: {lq_tmp0: Z | True}) => (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True))) x_33150792 v_x_33150792)))))) (l: {l: L_u | (L_wf l) /\ (forall (lengthres: Nats_u), (length_rel l lengthres) -> (lengthres = (⌊ n -⌋)))}) (m: {m: L_u | (L_wf m) /\ (forall (lengthres: Nats_u), (length_rel m lengthres) -> (lengthres = (⌊ n -⌋)))}): {{forall (zipres: L2_u), (zip_rel (⌊ l -⌋) (⌊ m -⌋) zipres) -> (forall (length2res: Nats_u), (length2_rel zipres length2res) -> (length2res = (⌊ n -⌋)))}}. 
Proof. 
	destruct n as [n n_p]. 
	destruct l as [l l_p]. 
	destruct m as [m m_p]. 
	try revert m_p; generalize dependent m; try revert l_p; generalize dependent l; try revert f_p; generalize dependent f; 
	induction n as [(*Suc*) n IH_n | (*Zero*) ]. 
	  - intros . 
		induction l as [(*App*) x xs IH_xs | (*Emp*) ]. 
		  -- intros . 
			induction m as [(*App*) y ys IH_ys | (*Emp*) ]. 
			  --- intros . 
				refine (subsumptionCast _ _ 
		(IH_n (ltac: (try clear IH_n; 
	solver)) f xs (ltac: (try clear IH_n; 
	solver)) ys (ltac: (try clear IH_n; 
	solver))) _); 
				solver.  
			  --- intros . 
				intros ; 
				exfalso; 
				solver.   
		  -- intros . 
			intros ; 
			exfalso; 
			solver.   
	  - intros . 
		induction l as [(*App*) lq_anf7205759403792803753 lq_anf7205759403792803754 IH_lq_anf7205759403792803754 | (*Emp*) ]. 
		  -- intros . 
			intros ; 
			exfalso; 
			solver.  
		  -- intros . 
			induction m as [(*App*) lq_anf7205759403792803751 lq_anf7205759403792803752 IH_lq_anf7205759403792803752 | (*Emp*) ]. 
			  --- intros . 
				intros ; 
				exfalso; 
				solver.  
			  --- intros . 
				refine (exist _ unit _); 
				solver.    
Defined. 
Definition zipWith (f: (@Pack ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)) (ltac: (mkProjectsArgListTG ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)))) Z (fun (x_33150792: (ArgList {lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))))) => (fun (v_x_33150792: Z) => (ltac: (flattenP (fun (lq_tmp0: {lq_tmp0: Z | True}) => (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True))) x_33150792 v_x_33150792)))))) (l: L) (m: L): L. 
Proof. 
	destruct l as [l l_p]. 
	destruct m as [m m_p]. 
	try revert m_p; generalize dependent m; try revert f_p; generalize dependent f; 
	induction l as [(*App*) x xs IH_xs | (*Emp*) ]. 
	  - intros . 
		induction m as [(*App*) y ys IH_ys | (*Emp*) ]. 
		  -- intros . 
			refine (subsumptionCast _ _ 
		(App 
		((getPackF f) (exist (fun (lq_tmp0: Z) => True) x (ltac: (solver))) (exist (fun (lq_tmp1: Z) => True) y (ltac: (solver)))) 
		(IH_xs (ltac: (try clear IH_xs; 
	solver)) f ys (ltac: (try clear IH_xs; 
	solver)))) _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Emp _); 
			solver.   
	  - intros . 
		refine (subsumptionCast _ _ Emp _); 
		solver.  
Defined. 
Inductive zipWith_rel : ((@uPack (Z ::UT (Z ::UT nilUT)) Z) -> (L_u -> (L_u -> (L_u -> Prop)))) := 
	 | zipWith_Emp: (forall (f: @uPack (Z ::UT (Z ::UT nilUT)) Z) m , zipWith_rel f Emp_u m Emp_u)
	 | zipWith_App_Emp: (forall (f: @uPack (Z ::UT (Z ::UT nilUT)) Z) x xs , zipWith_rel f (App_u x xs) Emp_u Emp_u)
	 | zipWith_App_App: (forall (f: @uPack (Z ::UT (Z ::UT nilUT)) Z) x xs y ys , forall (zipWithres: L_u), (zipWith_rel f xs ys zipWithres) -> (forall (fres: _), ((getUPackRel f) x y fres) -> (zipWith_rel f (App_u x xs) (App_u y ys) (App_u fres zipWithres)))). 
#[global] Hint Constructors zipWith_rel : core_hint_db.
#[global] Instance zipWith_lookup_rel : dictionary rel zipWith := { 
	lookup' := zipWith_rel
}.
#[global] Instance zipWith_getF : getFunc zipWith_rel := { 
	getF' := zipWith
}.
Definition zipWith_rel_funct [f: @uPack (Z ::UT (Z ::UT nilUT)) Z] [l: L_u] [m: L_u]: (forall (VV: L_u) (VV': L_u) (H: zipWith_rel f l m VV) (K: zipWith_rel f l m VV') , VV = VV'). 
Proof. 
	try revert m_p; generalize dependent m; try revert f_p; generalize dependent f; 
	induction l as [(*App*) x xs IH_xs | (*Emp*) ]; 
	intros ; 
	[induction m as [(*App*) y ys IH_ys | (*Emp*) ]; 
	intros | 
	]; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve zipWith_rel_funct : f_rel_funct_db.
Theorem zipWith_Emp_lem (f: @uPack (Z ::UT (Z ::UT nilUT)) Z) (m: _): (zipWith_rel f Emp_u m Emp_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite zipWith_Emp_lem : f_rel_back.
Theorem zipWith_App_Emp_lem (f: @uPack (Z ::UT (Z ::UT nilUT)) Z) (x: _) (xs: _): (zipWith_rel f (App_u x xs) Emp_u Emp_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite zipWith_App_Emp_lem : f_rel_back.
Theorem zipWith_App_App_lem (f: @uPack (Z ::UT (Z ::UT nilUT)) Z) (x: _) (xs: _) (y: _) (ys: _) (fres: _) (zipWithres: L_u) (h_45534364: (getUPackRel f) x y fres) (h_63896734: zipWith_rel f xs ys zipWithres): (zipWith_rel f (App_u x xs) (App_u y ys) (App_u fres zipWithres)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite zipWith_App_App_lem : f_rel_back.
Theorem zipWith_rel_ex (f: (@Pack ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)) (ltac: (mkProjectsArgListTG ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)))) Z (fun (x_33150792: (ArgList {lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))))) => (fun (v_x_33150792: Z) => (ltac: (flattenP (fun (lq_tmp0: {lq_tmp0: Z | True}) => (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True))) x_33150792 v_x_33150792)))))) (l: L_u) (m: L_u) (l_p: (L_wf l) /\ True) (m_p: (L_wf m) /\ True): zipWith_rel (packProj f) l m (⌊ zipWith f (exist _ l l_p) (exist _ m m_p) -⌋). 
Proof. 
	existence_lemma_pre zipWith; 
	try revert m_p; generalize dependent m; try revert f_p; generalize dependent f; 
	induction l as [(*App*) x xs IH_xs | (*Emp*) ]; 
	intros ; 
	[induction m as [(*App*) y ys IH_ys | (*Emp*) ]; 
	intros ; 
	[fix_notations; 
	pose proof (IH_xs (ltac: (try clear IH_xs; 
	solver)) f ys (ltac: (try clear IH_xs; 
	solver))) as IH_57799329; 
	try clear IH_xs; 
	try clear IH_ys| 
	fix_notations; 
	try clear IH_xs]| 
	fix_notations]; 
	existence_lemma_quicksolve zipWith; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve zipWith_rel_ex : rel_ax_db.
Opaque zipWith. 
Theorem zipWith__zipWith_rel_rw (f: (@Pack ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)) (ltac: (mkProjectsArgListTG ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)))) Z (fun (x_33150792: (ArgList {lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))))) => (fun (v_x_33150792: Z) => (ltac: (flattenP (fun (lq_tmp0: {lq_tmp0: Z | True}) => (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True))) x_33150792 v_x_33150792)))))) (l: L_u) (m: L_u) (l_p: (L_wf l) /\ True) (m_p: (L_wf m) /\ True) (VV: L_u): ((⌊ zipWith f (exist _ l l_p) (exist _ m m_p) -⌋) = VV) <-> (zipWith_rel (packProj f) l m VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite zipWith__zipWith_rel_rw : f_rel_funct_db.
#[global] Hint Resolve zipWith__zipWith_rel_rw : rel_ax_db.
#[global] Instance zipWith_lookup_rw : dictionary rwLem zipWith := { 
	lookup' := zipWith__zipWith_rel_rw
}.
Theorem zipWith__zipWith_rel (f_r: (@Pack ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)) (ltac: (mkProjectsArgListTG ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)))) Z (fun (x_33150792: (ArgList {lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))))) => (fun (v_x_33150792: Z) => (ltac: (flattenP (fun (lq_tmp0: {lq_tmp0: Z | True}) => (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True))) x_33150792 v_x_33150792)))))) (l_r: L) (m_r: L) (VV: L_u): ((⌊ zipWith f_r l_r m_r -⌋) = VV) <-> (zipWith_rel (packProj f_r) (⌊ l_r -⌋) (⌊ m_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite zipWith__zipWith_rel : f_rel_funct_db.
Theorem zipWith__zipWith_rel' (f: @uPack (Z ::UT (Z ::UT nilUT)) Z) (l: L_u) (m: L_u) (f_r: (@Pack ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)) (ltac: (mkProjectsArgListTG ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)))) Z (fun (x_33150792: (ArgList {lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))))) => (fun (v_x_33150792: Z) => (ltac: (flattenP (fun (lq_tmp0: {lq_tmp0: Z | True}) => (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True))) x_33150792 v_x_33150792)))))) (l_r: L) (m_r: L) (VV: L_u): (f = (packProj f_r)) -> ((l = (⌊ l_r -⌋)) -> ((m = (⌊ m_r -⌋)) -> (((⌊ zipWith f_r l_r m_r -⌋) = VV) <-> (zipWith_rel f l m VV)))). 
Proof. 
	intros -> -> ->. 
	refine (zipWith__zipWith_rel f_r l_r m_r VV). 
Qed. 
#[global] Hint Resolve zipWith__zipWith_rel' : f_rel_funct_db.
Definition zipWith_rel_mk [f: (@Pack ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)) (ltac: (mkProjectsArgListTG ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)))) (Z ::UT (Z ::UT nilUT)))) Z (fun (x_33150792: (ArgList {lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))))) => (fun (v_x_33150792: Z) => (ltac: (flattenP (fun (lq_tmp0: {lq_tmp0: Z | True}) => (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True))) x_33150792 v_x_33150792)))))] [l: L_u] [m: L_u] (l_p: (L_wf l) /\ True) (m_p: (L_wf m) /\ True): {VV: _ | zipWith_rel (packProj f) l m VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (zipWith_rel (packProj f) l m VV)) (zipWith f (exist _ l l_p) (exist _ m m_p)) _); 
	rewrite <- zipWith__zipWith_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve zipWith_rel_mk : f_rel_funct_db.
Definition zip_take (l: L) (m: L): {{forall (zipres: L2_u), (zip_rel (⌊ l -⌋) (⌊ m -⌋) zipres) -> (forall (lengthres: Nats_u), (length_rel (⌊ l -⌋) lengthres) -> (forall (takeres: L_u), (take_rel lengthres (⌊ m -⌋) takeres) -> (forall (length_res_2: Nats_u), (length_rel (⌊ m -⌋) length_res_2) -> (forall (take_res_2: L_u), (take_rel length_res_2 (⌊ l -⌋) take_res_2) -> (forall (zip_res_2: L2_u), (zip_rel take_res_2 takeres zip_res_2) -> (zipres == zip_res_2))))))}}. 
Proof. 
	destruct l as [l l_p]. 
	destruct m as [m m_p]. 
	try revert m_p; generalize dependent m; 
	induction l as [(*App*) x xs IH_xs | (*Emp*) ]. 
	  - intros . 
		induction m as [(*App*) y ys IH_ys | (*Emp*) ]. 
		  -- intros . 
			refine (subsumptionCast _ _ 
		(IH_xs (ltac: (try clear IH_xs; 
	solver)) ys (ltac: (try clear IH_xs; 
	solver))) _); 
			solver.  
		  -- intros . 
			refine (exist _ unit _); 
			solver.   
	  - intros . 
		refine (exist _ unit _); 
		solver.  
Defined. 