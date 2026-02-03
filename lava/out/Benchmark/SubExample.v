From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
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
Definition SubExample__sub (m: Nats) (n: {n: Nats_u | (Nats_wf n) /\ (geqN_rel (⌊ m -⌋) n true)}): {o: Nats_u | (Nats_wf o) /\ ((o <> Zero_u) <-> ((⌊ m -⌋) <> (⌊ n -⌋)))}. 
Proof. 
	destruct m as [m m_p]. 
	destruct n as [n n_p]. 
	try revert n_p; generalize dependent n; 
	induction m as [(*Suc*) m IH_m | (*Zero*) ]. 
	  - intros . 
		induction n as [(*Suc*) n IH_n | (*Zero*) ]. 
		  -- intros . 
			refine (subsumptionCast _ _ 
		(IH_m (ltac: (try clear IH_m; 
	solver)) n (ltac: (try clear IH_m; 
	solver))) _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ 
		(Suc 
		(exist (fun (n: Nats_u) => ((Nats_wf n) /\ True)) m (ltac: (solver)))) _); 
			solver.   
	  - intros . 
		induction n as [(*Suc*) lq_anf7205759403792813667 IH_lq_anf7205759403792813667 | (*Zero*) ]. 
		  -- intros . 
			intros ; 
			exfalso; 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Zero _); 
			solver.   
Defined. 
Inductive SubExample__sub_rel : (Nats_u -> (Nats_u -> (Nats_u -> Prop))) := 
	 | SubExample__sub_Zero_Zero: SubExample__sub_rel Zero_u Zero_u Zero_u
	 | SubExample__sub_Suc_Zero: (forall m , SubExample__sub_rel (Suc_u m) Zero_u (Suc_u m))
	 | SubExample__sub_Suc_Suc: (forall m n , forall (SubExample__subres: Nats_u), (SubExample__sub_rel m n SubExample__subres) -> (SubExample__sub_rel (Suc_u m) (Suc_u n) SubExample__subres)). 
#[global] Hint Constructors SubExample__sub_rel : core_hint_db.
#[global] Instance SubExample__sub_lookup_rel : dictionary rel SubExample__sub := { 
	lookup' := SubExample__sub_rel
}.
#[global] Instance SubExample__sub_getF : getFunc SubExample__sub_rel := { 
	getF' := SubExample__sub
}.
Definition SubExample__sub_rel_funct [m: Nats_u] [n: Nats_u]: (forall (o: Nats_u) (o': Nats_u) (H: SubExample__sub_rel m n o) (K: SubExample__sub_rel m n o') , o = o'). 
Proof. 
	try revert n_p; generalize dependent n; 
	induction m as [(*Suc*) m IH_m | (*Zero*) ]; 
	intros ; 
	[induction n as [(*Suc*) n IH_n | (*Zero*) ]; 
	intros | 
	induction n as [(*Suc*) lq_anf7205759403792813667 IH_lq_anf7205759403792813667 | (*Zero*) ]; 
	intros ]; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve SubExample__sub_rel_funct : f_rel_funct_db.
Theorem SubExample__sub_Zero_Zero_lem: (SubExample__sub_rel Zero_u Zero_u Zero_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite SubExample__sub_Zero_Zero_lem : f_rel_back.
Theorem SubExample__sub_Suc_Zero_lem (m: _): (SubExample__sub_rel (Suc_u m) Zero_u (Suc_u m)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite SubExample__sub_Suc_Zero_lem : f_rel_back.
Theorem SubExample__sub_Suc_Suc_lem (m: _) (n: _) (SubExample__subres: Nats_u) (h_31008789: SubExample__sub_rel m n SubExample__subres): (SubExample__sub_rel (Suc_u m) (Suc_u n) SubExample__subres) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite SubExample__sub_Suc_Suc_lem : f_rel_back.
Theorem SubExample__sub_rel_ex (m: Nats_u) (n: Nats_u) (m_p: (Nats_wf m) /\ True) (n_p: (Nats_wf n) /\ (geqN_rel m n true)): SubExample__sub_rel m n (⌊ SubExample__sub (exist _ m m_p) (exist _ n n_p) -⌋). 
Proof. 
	existence_lemma_pre SubExample__sub; 
	try revert n_p; generalize dependent n; 
	induction m as [(*Suc*) m IH_m | (*Zero*) ]; 
	intros ; 
	[induction n as [(*Suc*) n IH_n | (*Zero*) ]; 
	intros ; 
	[fix_notations; 
	pose proof (IH_m (ltac: (try clear IH_m; 
	solver)) n (ltac: (try clear IH_m; 
	solver))) as IH_13828668; 
	try clear IH_m; 
	try clear IH_n| 
	fix_notations; 
	try clear IH_m]| 
	induction n as [(*Suc*) lq_anf7205759403792813667 IH_lq_anf7205759403792813667 | (*Zero*) ]; 
	intros ; 
	[fix_notations; 
	try clear IH_lq_anf7205759403792813667| 
	fix_notations]]; 
	existence_lemma_quicksolve SubExample__sub; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve SubExample__sub_rel_ex : rel_ax_db.
Opaque SubExample__sub. 
Theorem SubExample__sub__SubExample__sub_rel_rw (m: Nats_u) (n: Nats_u) (m_p: (Nats_wf m) /\ True) (n_p: (Nats_wf n) /\ (geqN_rel m n true)) (o: Nats_u): ((⌊ SubExample__sub (exist _ m m_p) (exist _ n n_p) -⌋) = o) <-> (SubExample__sub_rel m n o). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite SubExample__sub__SubExample__sub_rel_rw : f_rel_funct_db.
#[global] Hint Resolve SubExample__sub__SubExample__sub_rel_rw : rel_ax_db.
#[global] Instance SubExample__sub_lookup_rw : dictionary rwLem SubExample__sub := { 
	lookup' := SubExample__sub__SubExample__sub_rel_rw
}.
Theorem SubExample__sub__SubExample__sub_rel (m_r: Nats) (n_r: {n: Nats_u | (Nats_wf n) /\ (geqN_rel (⌊ m_r -⌋) n true)}) (o: Nats_u): ((⌊ SubExample__sub m_r n_r -⌋) = o) <-> (SubExample__sub_rel (⌊ m_r -⌋) (⌊ n_r -⌋) o). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite SubExample__sub__SubExample__sub_rel : f_rel_funct_db.
Theorem SubExample__sub__SubExample__sub_rel' (m: Nats_u) (n: Nats_u) (m_r: Nats) (n_r: {n: Nats_u | (Nats_wf n) /\ (geqN_rel (⌊ m_r -⌋) n true)}) (o: Nats_u): (m = (⌊ m_r -⌋)) -> ((n = (⌊ n_r -⌋)) -> (((⌊ SubExample__sub m_r n_r -⌋) = o) <-> (SubExample__sub_rel m n o))). 
Proof. 
	intros -> ->. 
	refine (SubExample__sub__SubExample__sub_rel m_r n_r o). 
Qed. 
#[global] Hint Resolve SubExample__sub__SubExample__sub_rel' : f_rel_funct_db.
Definition SubExample__sub_rel_mk [m: Nats_u] [n: Nats_u] (m_p: (Nats_wf m) /\ True) (n_p: (Nats_wf n) /\ (geqN_rel m n true)): {o: _ | SubExample__sub_rel m n o}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (o: _) => (SubExample__sub_rel m n o)) (SubExample__sub (exist _ m m_p) (exist _ n n_p)) _); 
	rewrite <- SubExample__sub__SubExample__sub_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve SubExample__sub_rel_mk : f_rel_funct_db.
#[global] Instance SubExample__subPack : (@Pack (Nats ::RT (fun (m_r: Nats) => ({n: Nats_u | (Nats_wf n) /\ (geqN_rel (⌊ m_r -⌋) n true)} ::RT (fun (n_r: {n: Nats_u | (Nats_wf n) /\ (geqN_rel (⌊ m_r -⌋) n true)}) => nilRT)))) (Nats_u ::UT (Nats_u ::UT nilUT)) (ltac: (mkProjectsArgListTG (Nats ::RT (fun (m_r: Nats) => ({n: Nats_u | (Nats_wf n) /\ (geqN_rel (⌊ m_r -⌋) n true)} ::RT (fun (n_r: {n: Nats_u | (Nats_wf n) /\ (geqN_rel (⌊ m_r -⌋) n true)}) => nilRT)))) (Nats_u ::UT (Nats_u ::UT nilUT)))) Nats_u (fun (x_87946269: (ArgList Nats ::RT (fun (m_r: Nats) => ({n: Nats_u | (Nats_wf n) /\ (geqN_rel (⌊ m_r -⌋) n true)} ::RT (fun (n_r: {n: Nats_u | (Nats_wf n) /\ (geqN_rel (⌊ m_r -⌋) n true)}) => nilRT))))) => (fun (v_x_87946269: Nats_u) => (ltac: (flattenP (fun (m_r: Nats) => (fun (n_r: {n: Nats_u | (Nats_wf n) /\ (geqN_rel (⌊ m_r -⌋) n true)}) => (fun (o: Nats_u) => ((Nats_wf o) /\ ((o <> Zero_u) <-> ((⌊ m_r -⌋) <> (⌊ n_r -⌋))))))) x_87946269 v_x_87946269))))).
Proof. 
	buildPackG SubExample__sub SubExample__sub_rel SubExample__sub__SubExample__sub_rel SubExample__sub_rel_funct. 
Defined.
Definition surprise: {{forall (SubExample__subres: Nats_u), (SubExample__sub_rel (Suc_u Zero_u) (Suc_u (Suc_u Zero_u)) SubExample__subres) -> (SubExample__subres = Zero_u)}}. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Defined. 
Definition one: Nats. 
Proof. 
	refine (subsumptionCast _ _ 
		(Suc 
		(subsumptionCast Nats_u (fun (n: Nats_u) => ((Nats_wf n) /\ True)) Zero (ltac: (solver)))) _); 
	solver. 
Defined. 
Inductive one_rel : (Nats_u -> Prop) := 
	 | one_def: one_rel (Suc_u Zero_u). 
#[global] Hint Constructors one_rel : core_hint_db.
#[global] Instance one_lookup_rel : dictionary rel one := { 
	lookup' := one_rel
}.
#[global] Instance one_getF : getFunc one_rel := { 
	getF' := one
}.
Definition one_rel_funct: (forall (VV: Nats_u) (VV': Nats_u) (H: one_rel VV) (K: one_rel VV') , VV = VV'). 
Proof. 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve one_rel_funct : f_rel_funct_db.
Theorem one_def_lem: (one_rel (Suc_u Zero_u)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite one_def_lem : f_rel_back.
Theorem one_rel_ex: one_rel (⌊ one -⌋). 
Proof. 
	existence_lemma_pre one; 
	fix_notations; 
	existence_lemma_quicksolve one; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve one_rel_ex : rel_ax_db.
Opaque one. 
Theorem one__one_rel_rw (VV: Nats_u): ((⌊ one -⌋) = VV) <-> (one_rel VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite one__one_rel_rw : f_rel_funct_db.
#[global] Hint Resolve one__one_rel_rw : rel_ax_db.
#[global] Instance one_lookup_rw : dictionary rwLem one := { 
	lookup' := one__one_rel_rw
}.
Theorem one__one_rel (VV: Nats_u): ((⌊ one -⌋) = VV) <-> (one_rel VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite one__one_rel : f_rel_funct_db.
Theorem one__one_rel' (VV: Nats_u): ((⌊ one -⌋) = VV) <-> (one_rel VV). 
Proof. 
	intros . 
	refine (one__one_rel VV). 
Qed. 
#[global] Hint Resolve one__one_rel' : f_rel_funct_db.
Definition one_rel_mk: {VV: _ | one_rel VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (one_rel VV)) one _); 
	rewrite <- one__one_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve one_rel_mk : f_rel_funct_db.
Definition two: Nats. 
Proof. 
	refine (subsumptionCast _ _ 
		(Suc 
		(subsumptionCast Nats_u (fun (n: Nats_u) => ((Nats_wf n) /\ True)) one (ltac: (solver)))) _); 
	solver. 
Defined. 
Inductive two_rel : (Nats_u -> Prop) := 
	 | two_def: two_rel (Suc_u (⌊ one -⌋)). 
#[global] Hint Constructors two_rel : core_hint_db.
#[global] Instance two_lookup_rel : dictionary rel two := { 
	lookup' := two_rel
}.
#[global] Instance two_getF : getFunc two_rel := { 
	getF' := two
}.
Definition two_rel_funct: (forall (VV: Nats_u) (VV': Nats_u) (H: two_rel VV) (K: two_rel VV') , VV = VV'). 
Proof. 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve two_rel_funct : f_rel_funct_db.
Theorem two_def_lem: (two_rel (Suc_u (⌊ one -⌋))) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite two_def_lem : f_rel_back.
Theorem two_rel_ex: two_rel (⌊ two -⌋). 
Proof. 
	existence_lemma_pre two; 
	fix_notations; 
	existence_lemma_quicksolve two; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve two_rel_ex : rel_ax_db.
Opaque two. 
Theorem two__two_rel_rw (VV: Nats_u): ((⌊ two -⌋) = VV) <-> (two_rel VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite two__two_rel_rw : f_rel_funct_db.
#[global] Hint Resolve two__two_rel_rw : rel_ax_db.
#[global] Instance two_lookup_rw : dictionary rwLem two := { 
	lookup' := two__two_rel_rw
}.
Theorem two__two_rel (VV: Nats_u): ((⌊ two -⌋) = VV) <-> (two_rel VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite two__two_rel : f_rel_funct_db.
Theorem two__two_rel' (VV: Nats_u): ((⌊ two -⌋) = VV) <-> (two_rel VV). 
Proof. 
	intros . 
	refine (two__two_rel VV). 
Qed. 
#[global] Hint Resolve two__two_rel' : f_rel_funct_db.
Definition two_rel_mk: {VV: _ | two_rel VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (two_rel VV)) two _); 
	rewrite <- two__two_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve two_rel_mk : f_rel_funct_db.
Inductive Maybe_u : Set := 
	 | Nothing_u: Maybe_u. 
Fixpoint Maybe_eq (x: Maybe_u) (y: Maybe_u): bool := 
	match (x, y) with (Nothing_u, Nothing_u) => true end. 
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
	match x with Nothing_u => True end. 
Theorem Maybe_wf_ref [p: Maybe_u -> Prop] (tm: {v: Maybe_u | (Maybe_wf v) /\ (p v)}): Maybe_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation Maybe := {x: Maybe_u | (Maybe_wf x) /\ True}. 
Definition Nothing_lem: (Maybe_wf Nothing_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Nothing: Maybe := 
	exist _ Nothing_u Nothing_lem. 
#[global] Hint Resolve Maybe_wf_ref : wf_constr_db.
#[global] Hint Unfold Maybe_wf : wf_constr_db.
#[global] Hint Resolve Maybe_eq : ref_constr_db.
#[global] Hint Unfold Nothing : ref_constr_db.