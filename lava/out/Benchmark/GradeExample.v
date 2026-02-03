From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Inductive Modifier_u : Set := 
	 | Minus_u: Modifier_u
	 | Natural_u: Modifier_u
	 | Plus_u: Modifier_u. 
Fixpoint Modifier_eq (x: Modifier_u) (y: Modifier_u): bool := 
	match (x, y) with (Minus_u, Minus_u) => true | (Natural_u, Natural_u) => true | (Plus_u, Plus_u) => true | (_, _) => false end. 
Definition Modifier_eq_refl: (forall (x: Modifier_u) , is_true (Modifier_eq x x)). 
Proof. 
	eq_refl. 
Qed. 
#[global] Hint Resolve Modifier_eq_refl : eq_hint_db.
Definition Modifier_eqb_eq: (forall (s: Modifier_u) (t: Modifier_u) , (is_true (Modifier_eq s t)) -> (s = t)). 
Proof. 
	eqb_eq_lem. 
Qed. 
#[global] Hint Resolve Modifier_eqb_eq : eq_hint_db.
#[global] Instance leibnitz_eq_Modifier : LeibnitzEqB := { 
	equalB' := Modifier_eq;
	refl' := Modifier_eq_refl;
	eqb_eq' := Modifier_eqb_eq
}.
Fixpoint Modifier_wf (x: Modifier_u): Prop := 
	match x with Minus_u => True | Natural_u => True | Plus_u => True end. 
Theorem Modifier_wf_ref [p: Modifier_u -> Prop] (tm: {v: Modifier_u | (Modifier_wf v) /\ (p v)}): Modifier_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation Modifier := {x: Modifier_u | (Modifier_wf x) /\ True}. 
Definition Minus_lem: (Modifier_wf Minus_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Minus: Modifier := 
	exist _ Minus_u Minus_lem. 
Definition Natural_lem: (Modifier_wf Natural_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Natural: Modifier := 
	exist _ Natural_u Natural_lem. 
Definition Plus_lem: (Modifier_wf Plus_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Plus: Modifier := 
	exist _ Plus_u Plus_lem. 
#[global] Hint Resolve Modifier_wf_ref : wf_constr_db.
#[global] Hint Unfold Modifier_wf : wf_constr_db.
#[global] Hint Resolve Modifier_eq : ref_constr_db.
#[global] Hint Unfold Minus : ref_constr_db.
#[global] Hint Unfold Natural : ref_constr_db.
#[global] Hint Unfold Plus : ref_constr_db.
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
Inductive Letter_u : Set := 
	 | A_u: Letter_u
	 | B_u: Letter_u
	 | C_u: Letter_u
	 | D_u: Letter_u
	 | F_u: Letter_u. 
Fixpoint Letter_eq (x: Letter_u) (y: Letter_u): bool := 
	match (x, y) with (A_u, A_u) => true | (B_u, B_u) => true | (C_u, C_u) => true | (D_u, D_u) => true | (F_u, F_u) => true | (_, _) => false end. 
Definition Letter_eq_refl: (forall (x: Letter_u) , is_true (Letter_eq x x)). 
Proof. 
	eq_refl. 
Qed. 
#[global] Hint Resolve Letter_eq_refl : eq_hint_db.
Definition Letter_eqb_eq: (forall (s: Letter_u) (t: Letter_u) , (is_true (Letter_eq s t)) -> (s = t)). 
Proof. 
	eqb_eq_lem. 
Qed. 
#[global] Hint Resolve Letter_eqb_eq : eq_hint_db.
#[global] Instance leibnitz_eq_Letter : LeibnitzEqB := { 
	equalB' := Letter_eq;
	refl' := Letter_eq_refl;
	eqb_eq' := Letter_eqb_eq
}.
Fixpoint Letter_wf (x: Letter_u): Prop := 
	match x with A_u => True | B_u => True | C_u => True | D_u => True | F_u => True end. 
Theorem Letter_wf_ref [p: Letter_u -> Prop] (tm: {v: Letter_u | (Letter_wf v) /\ (p v)}): Letter_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation Letter := {x: Letter_u | (Letter_wf x) /\ True}. 
Definition A_lem: (Letter_wf A_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition A: Letter := 
	exist _ A_u A_lem. 
Definition B_lem: (Letter_wf B_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition B: Letter := 
	exist _ B_u B_lem. 
Definition C_lem: (Letter_wf C_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition C: Letter := 
	exist _ C_u C_lem. 
Definition D_lem: (Letter_wf D_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition D: Letter := 
	exist _ D_u D_lem. 
Definition F_lem: (Letter_wf F_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition F: Letter := 
	exist _ F_u F_lem. 
#[global] Hint Resolve Letter_wf_ref : wf_constr_db.
#[global] Hint Unfold Letter_wf : wf_constr_db.
#[global] Hint Resolve Letter_eq : ref_constr_db.
#[global] Hint Unfold A : ref_constr_db.
#[global] Hint Unfold B : ref_constr_db.
#[global] Hint Unfold C : ref_constr_db.
#[global] Hint Unfold D : ref_constr_db.
#[global] Hint Unfold F : ref_constr_db.
Definition lowerLetter (l: Letter): Letter. 
Proof. 
	destruct l as [l l_p]. 
	induction l as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ B _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ C _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ D _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ F _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ F _); 
		solver.  
Defined. 
Inductive lowerLetter_rel : (Letter_u -> (Letter_u -> Prop)) := 
	 | lowerLetter_A: lowerLetter_rel A_u B_u
	 | lowerLetter_B: lowerLetter_rel B_u C_u
	 | lowerLetter_C: lowerLetter_rel C_u D_u
	 | lowerLetter_D: lowerLetter_rel D_u F_u
	 | lowerLetter_F: lowerLetter_rel F_u F_u. 
#[global] Hint Constructors lowerLetter_rel : core_hint_db.
#[global] Instance lowerLetter_lookup_rel : dictionary rel lowerLetter := { 
	lookup' := lowerLetter_rel
}.
#[global] Instance lowerLetter_getF : getFunc lowerLetter_rel := { 
	getF' := lowerLetter
}.
Definition lowerLetter_rel_funct [l: Letter_u]: (forall (VV: Letter_u) (VV': Letter_u) (H: lowerLetter_rel l VV) (K: lowerLetter_rel l VV') , VV = VV'). 
Proof. 
	destruct l as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve lowerLetter_rel_funct : f_rel_funct_db.
Theorem lowerLetter_A_lem: (lowerLetter_rel A_u B_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite lowerLetter_A_lem : f_rel_back.
Theorem lowerLetter_B_lem: (lowerLetter_rel B_u C_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite lowerLetter_B_lem : f_rel_back.
Theorem lowerLetter_C_lem: (lowerLetter_rel C_u D_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite lowerLetter_C_lem : f_rel_back.
Theorem lowerLetter_D_lem: (lowerLetter_rel D_u F_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite lowerLetter_D_lem : f_rel_back.
Theorem lowerLetter_F_lem: (lowerLetter_rel F_u F_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite lowerLetter_F_lem : f_rel_back.
Theorem lowerLetter_rel_ex (l: Letter_u) (l_p: (Letter_wf l) /\ True): lowerLetter_rel l (⌊ lowerLetter (exist _ l l_p) -⌋). 
Proof. 
	existence_lemma_pre lowerLetter; 
	destruct l as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations]; 
	existence_lemma_quicksolve lowerLetter; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve lowerLetter_rel_ex : rel_ax_db.
Opaque lowerLetter. 
Theorem lowerLetter__lowerLetter_rel_rw (l: Letter_u) (l_p: (Letter_wf l) /\ True) (VV: Letter_u): ((⌊ lowerLetter (exist _ l l_p) -⌋) = VV) <-> (lowerLetter_rel l VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite lowerLetter__lowerLetter_rel_rw : f_rel_funct_db.
#[global] Hint Resolve lowerLetter__lowerLetter_rel_rw : rel_ax_db.
#[global] Instance lowerLetter_lookup_rw : dictionary rwLem lowerLetter := { 
	lookup' := lowerLetter__lowerLetter_rel_rw
}.
Theorem lowerLetter__lowerLetter_rel (l_r: Letter) (VV: Letter_u): ((⌊ lowerLetter l_r -⌋) = VV) <-> (lowerLetter_rel (⌊ l_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite lowerLetter__lowerLetter_rel : f_rel_funct_db.
Theorem lowerLetter__lowerLetter_rel' (l: Letter_u) (l_r: Letter) (VV: Letter_u): (l = (⌊ l_r -⌋)) -> (((⌊ lowerLetter l_r -⌋) = VV) <-> (lowerLetter_rel l VV)). 
Proof. 
	intros ->. 
	refine (lowerLetter__lowerLetter_rel l_r VV). 
Qed. 
#[global] Hint Resolve lowerLetter__lowerLetter_rel' : f_rel_funct_db.
Definition lowerLetter_rel_mk [l: Letter_u] (l_p: (Letter_wf l) /\ True): {VV: _ | lowerLetter_rel l VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (lowerLetter_rel l VV)) (lowerLetter (exist _ l l_p)) _); 
	rewrite <- lowerLetter__lowerLetter_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve lowerLetter_rel_mk : f_rel_funct_db.
#[global] Instance lowerLetterPack : (@Pack (Letter ::RT (fun (l_r: Letter) => nilRT)) (Letter_u ::UT nilUT) (ltac: (mkProjectsArgListTG (Letter ::RT (fun (l_r: Letter) => nilRT)) (Letter_u ::UT nilUT))) Letter_u (fun (x_49471188: (ArgList Letter ::RT (fun (l_r: Letter) => nilRT))) => (fun (v_x_49471188: Letter_u) => (ltac: (flattenP (fun (l_r: Letter) => (fun (VV: Letter_u) => ((Letter_wf VV) /\ True))) x_49471188 v_x_49471188))))).
Proof. 
	buildPackG lowerLetter lowerLetter_rel lowerLetter__lowerLetter_rel lowerLetter_rel_funct. 
Defined.
Definition lowerLetterFIsF: {{forall (lowerLetterres: Letter_u), (lowerLetter_rel F_u lowerLetterres) -> (lowerLetterres = F_u)}}. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Defined. 
Inductive Grades_u : Set := 
	 | Grade_u: Letter_u -> (Modifier_u -> Grades_u). 
Fixpoint Grades_eq (x: Grades_u) (y: Grades_u): bool := 
	match (x, y) with (Grade_u x x_1, Grade_u x' x_1') => ((true && (x ==? x')) && (x_1 ==? x_1')) end. 
Definition Grades_eq_refl: (forall (x: Grades_u) , is_true (Grades_eq x x)). 
Proof. 
	eq_refl. 
Qed. 
#[global] Hint Resolve Grades_eq_refl : eq_hint_db.
Definition Grades_eqb_eq: (forall (s: Grades_u) (t: Grades_u) , (is_true (Grades_eq s t)) -> (s = t)). 
Proof. 
	eqb_eq_lem. 
Qed. 
#[global] Hint Resolve Grades_eqb_eq : eq_hint_db.
#[global] Instance leibnitz_eq_Grades : LeibnitzEqB := { 
	equalB' := Grades_eq;
	refl' := Grades_eq_refl;
	eqb_eq' := Grades_eqb_eq
}.
Fixpoint Grades_wf (x: Grades_u): Prop := 
	match x with (Grade_u VV VV_) => (((Letter_wf VV) /\ True) /\ ((Modifier_wf VV_) /\ True)) end. 
Theorem Grades_wf_ref [p: Grades_u -> Prop] (tm: {v: Grades_u | (Grades_wf v) /\ (p v)}): Grades_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation Grades := {x: Grades_u | (Grades_wf x) /\ True}. 
Definition Grade_lem (VV: Letter) (VV_: Modifier): (Grades_wf (Grade_u (⌊ VV -⌋) (⌊ VV_ -⌋))) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Grade (VV: Letter) (VV_: Modifier): Grades := 
	exist _ (Grade_u (⌊ VV -⌋) (⌊ VV_ -⌋)) (Grade_lem VV VV_). 
#[global] Hint Resolve Grades_wf_ref : wf_constr_db.
#[global] Hint Unfold Grades_wf : wf_constr_db.
#[global] Hint Resolve Grades_eq : ref_constr_db.
#[global] Hint Unfold Grade : ref_constr_db.
Definition lowerGrade (g: Grades): Grades. 
Proof. 
	destruct g as [g g_p]. 
	induction g as [(*Grade*) l m]. 
	  - intros . 
		induction m as [(*Minus*)  | (*Natural*)  | (*Plus*) ]. 
		  -- intros . 
			induction l as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]. 
			  --- intros . 
				refine (subsumptionCast _ _ 
		(Grade 
		(lowerLetter 
		(subsumptionCast Letter_u (fun (l: Letter_u) => ((Letter_wf l) /\ True)) A (ltac: (solver)))) 
		(subsumptionCast Modifier_u (fun (VV: Modifier_u) => ((Modifier_wf VV) /\ True)) Plus (ltac: (solver)))) _); 
				solver.  
			  --- intros . 
				refine (subsumptionCast _ _ 
		(Grade 
		(lowerLetter 
		(subsumptionCast Letter_u (fun (l: Letter_u) => ((Letter_wf l) /\ True)) B (ltac: (solver)))) 
		(subsumptionCast Modifier_u (fun (VV: Modifier_u) => ((Modifier_wf VV) /\ True)) Plus (ltac: (solver)))) _); 
				solver.  
			  --- intros . 
				refine (subsumptionCast _ _ 
		(Grade 
		(lowerLetter 
		(subsumptionCast Letter_u (fun (l: Letter_u) => ((Letter_wf l) /\ True)) C (ltac: (solver)))) 
		(subsumptionCast Modifier_u (fun (VV: Modifier_u) => ((Modifier_wf VV) /\ True)) Plus (ltac: (solver)))) _); 
				solver.  
			  --- intros . 
				refine (subsumptionCast _ _ 
		(Grade 
		(lowerLetter 
		(subsumptionCast Letter_u (fun (l: Letter_u) => ((Letter_wf l) /\ True)) D (ltac: (solver)))) 
		(subsumptionCast Modifier_u (fun (VV: Modifier_u) => ((Modifier_wf VV) /\ True)) Plus (ltac: (solver)))) _); 
				solver.  
			  --- intros . 
				refine (subsumptionCast _ _ (Grade F Minus) _); 
				solver.   
		  -- intros . 
			refine (subsumptionCast _ _ 
		(Grade 
		(exist (fun (VV: Letter_u) => ((Letter_wf VV) /\ True)) l (ltac: (solver))) 
		(subsumptionCast Modifier_u (fun (VV: Modifier_u) => ((Modifier_wf VV) /\ True)) Minus (ltac: (solver)))) _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ 
		(Grade 
		(exist (fun (VV: Letter_u) => ((Letter_wf VV) /\ True)) l (ltac: (solver))) 
		(subsumptionCast Modifier_u (fun (VV: Modifier_u) => ((Modifier_wf VV) /\ True)) Natural (ltac: (solver)))) _); 
			solver.   
Defined. 
Inductive lowerGrade_rel : (Grades_u -> (Grades_u -> Prop)) := 
	 | lowerGrade_Grade: (forall l , lowerGrade_rel (Grade_u l Plus_u) (Grade_u l Natural_u))
	 | lowerGrade_Grade_: (forall l , lowerGrade_rel (Grade_u l Natural_u) (Grade_u l Minus_u))
	 | lowerGrade_Grade__: forall (lowerLetterres: Letter_u), (lowerLetter_rel A_u lowerLetterres) -> (lowerGrade_rel (Grade_u A_u Minus_u) (Grade_u lowerLetterres Plus_u))
	 | lowerGrade_Grade___: forall (lowerLetterres: Letter_u), (lowerLetter_rel B_u lowerLetterres) -> (lowerGrade_rel (Grade_u B_u Minus_u) (Grade_u lowerLetterres Plus_u))
	 | lowerGrade_Grade____: forall (lowerLetterres: Letter_u), (lowerLetter_rel C_u lowerLetterres) -> (lowerGrade_rel (Grade_u C_u Minus_u) (Grade_u lowerLetterres Plus_u))
	 | lowerGrade_Grade_____: forall (lowerLetterres: Letter_u), (lowerLetter_rel D_u lowerLetterres) -> (lowerGrade_rel (Grade_u D_u Minus_u) (Grade_u lowerLetterres Plus_u))
	 | lowerGrade_Grade______: lowerGrade_rel (Grade_u F_u Minus_u) (Grade_u F_u Minus_u). 
#[global] Hint Constructors lowerGrade_rel : core_hint_db.
#[global] Instance lowerGrade_lookup_rel : dictionary rel lowerGrade := { 
	lookup' := lowerGrade_rel
}.
#[global] Instance lowerGrade_getF : getFunc lowerGrade_rel := { 
	getF' := lowerGrade
}.
Definition lowerGrade_rel_funct [g: Grades_u]: (forall (VV: Grades_u) (VV': Grades_u) (H: lowerGrade_rel g VV) (K: lowerGrade_rel g VV') , VV = VV'). 
Proof. 
	induction g as [(*Grade*) l m]; 
	intros ; 
	[destruct m as [(*Minus*)  | (*Natural*)  | (*Plus*) ]; 
	intros ; 
	[destruct l as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros | 
	| 
	]]; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve lowerGrade_rel_funct : f_rel_funct_db.
Theorem lowerGrade_Grade_lem (l: _): (lowerGrade_rel (Grade_u l Plus_u) (Grade_u l Natural_u)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite lowerGrade_Grade_lem : f_rel_back.
Theorem lowerGrade_Grade__lem (l: _): (lowerGrade_rel (Grade_u l Natural_u) (Grade_u l Minus_u)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite lowerGrade_Grade__lem : f_rel_back.
Theorem lowerGrade_Grade___lem (lowerLetterres: Letter_u) (h_46012249: lowerLetter_rel A_u lowerLetterres): (lowerGrade_rel (Grade_u A_u Minus_u) (Grade_u lowerLetterres Plus_u)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite lowerGrade_Grade___lem : f_rel_back.
Theorem lowerGrade_Grade____lem (lowerLetterres: Letter_u) (h_10180783: lowerLetter_rel B_u lowerLetterres): (lowerGrade_rel (Grade_u B_u Minus_u) (Grade_u lowerLetterres Plus_u)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite lowerGrade_Grade____lem : f_rel_back.
Theorem lowerGrade_Grade_____lem (lowerLetterres: Letter_u) (h_20511933: lowerLetter_rel C_u lowerLetterres): (lowerGrade_rel (Grade_u C_u Minus_u) (Grade_u lowerLetterres Plus_u)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite lowerGrade_Grade_____lem : f_rel_back.
Theorem lowerGrade_Grade______lem (lowerLetterres: Letter_u) (h_28195801: lowerLetter_rel D_u lowerLetterres): (lowerGrade_rel (Grade_u D_u Minus_u) (Grade_u lowerLetterres Plus_u)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite lowerGrade_Grade______lem : f_rel_back.
Theorem lowerGrade_Grade_______lem: (lowerGrade_rel (Grade_u F_u Minus_u) (Grade_u F_u Minus_u)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite lowerGrade_Grade_______lem : f_rel_back.
Theorem lowerGrade_rel_ex (g: Grades_u) (g_p: (Grades_wf g) /\ True): lowerGrade_rel g (⌊ lowerGrade (exist _ g g_p) -⌋). 
Proof. 
	existence_lemma_pre lowerGrade; 
	induction g as [(*Grade*) l m]; 
	intros ; 
	[destruct m as [(*Minus*)  | (*Natural*)  | (*Plus*) ]; 
	intros ; 
	[destruct l as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations]| 
	fix_notations| 
	fix_notations]]; 
	existence_lemma_quicksolve lowerGrade; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve lowerGrade_rel_ex : rel_ax_db.
Opaque lowerGrade. 
Theorem lowerGrade__lowerGrade_rel_rw (g: Grades_u) (g_p: (Grades_wf g) /\ True) (VV: Grades_u): ((⌊ lowerGrade (exist _ g g_p) -⌋) = VV) <-> (lowerGrade_rel g VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite lowerGrade__lowerGrade_rel_rw : f_rel_funct_db.
#[global] Hint Resolve lowerGrade__lowerGrade_rel_rw : rel_ax_db.
#[global] Instance lowerGrade_lookup_rw : dictionary rwLem lowerGrade := { 
	lookup' := lowerGrade__lowerGrade_rel_rw
}.
Theorem lowerGrade__lowerGrade_rel (g_r: Grades) (VV: Grades_u): ((⌊ lowerGrade g_r -⌋) = VV) <-> (lowerGrade_rel (⌊ g_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite lowerGrade__lowerGrade_rel : f_rel_funct_db.
Theorem lowerGrade__lowerGrade_rel' (g: Grades_u) (g_r: Grades) (VV: Grades_u): (g = (⌊ g_r -⌋)) -> (((⌊ lowerGrade g_r -⌋) = VV) <-> (lowerGrade_rel g VV)). 
Proof. 
	intros ->. 
	refine (lowerGrade__lowerGrade_rel g_r VV). 
Qed. 
#[global] Hint Resolve lowerGrade__lowerGrade_rel' : f_rel_funct_db.
Definition lowerGrade_rel_mk [g: Grades_u] (g_p: (Grades_wf g) /\ True): {VV: _ | lowerGrade_rel g VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (lowerGrade_rel g VV)) (lowerGrade (exist _ g g_p)) _); 
	rewrite <- lowerGrade__lowerGrade_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve lowerGrade_rel_mk : f_rel_funct_db.
#[global] Instance lowerGradePack : (@Pack (Grades ::RT (fun (g_r: Grades) => nilRT)) (Grades_u ::UT nilUT) (ltac: (mkProjectsArgListTG (Grades ::RT (fun (g_r: Grades) => nilRT)) (Grades_u ::UT nilUT))) Grades_u (fun (x_69925386: (ArgList Grades ::RT (fun (g_r: Grades) => nilRT))) => (fun (v_x_69925386: Grades_u) => (ltac: (flattenP (fun (g_r: Grades) => (fun (VV: Grades_u) => ((Grades_wf VV) /\ True))) x_69925386 v_x_69925386))))).
Proof. 
	buildPackG lowerGrade lowerGrade_rel lowerGrade__lowerGrade_rel lowerGrade_rel_funct. 
Defined.
Definition applyLatePolicy (lateDays: {lateDays: Z | True}) (g: Grades): Grades. 
Proof. 
	destruct lateDays as [lateDays lateDays_p]. 
	destruct g as [g g_p]. 
	let E := fresh "E" in 
	destruct (lateDays <? 9) as [ | ] eqn:E; [refine (exist _ g _); 
	solver | let E := fresh "E" in 
	destruct (lateDays <? 17) as [ | ] eqn:E; [refine (subsumptionCast _ _ 
		(lowerGrade 
		(exist (fun (g: Grades_u) => ((Grades_wf g) /\ True)) g (ltac: (solver)))) _); 
	solver | let E := fresh "E" in 
	destruct (lateDays <? 21) as [ | ] eqn:E; [refine (subsumptionCast _ _ 
		(lowerGrade 
		(subsumptionCast Grades_u (fun (g: Grades_u) => ((Grades_wf g) /\ True)) 
		(lowerGrade 
		(exist (fun (g: Grades_u) => ((Grades_wf g) /\ True)) g (ltac: (solver)))) (ltac: (solver)))) _); 
	solver | refine (subsumptionCast _ _ 
		(lowerGrade 
		(subsumptionCast Grades_u (fun (g: Grades_u) => ((Grades_wf g) /\ True)) 
		(lowerGrade 
		(subsumptionCast Grades_u (fun (g: Grades_u) => ((Grades_wf g) /\ True)) 
		(lowerGrade 
		(exist (fun (g: Grades_u) => ((Grades_wf g) /\ True)) g (ltac: (solver)))) (ltac: (solver)))) (ltac: (solver)))) _); 
	solver]]]. 
Defined. 
Inductive applyLatePolicy_rel : (Z -> (Grades_u -> (Grades_u -> Prop))) := 
	 | applyLatePolicy_false_false_false: (forall g lateDays , (ltbZ_rel lateDays 9 false) -> ((ltbZ_rel lateDays 17 false) -> ((ltbZ_rel lateDays 21 false) -> (forall (lowerGraderes: Grades_u), (lowerGrade_rel g lowerGraderes) -> (forall (lowerGrade_res_2: Grades_u), (lowerGrade_rel lowerGraderes lowerGrade_res_2) -> (forall (lowerGrade_res_3: Grades_u), (lowerGrade_rel lowerGrade_res_2 lowerGrade_res_3) -> (applyLatePolicy_rel lateDays g lowerGrade_res_3)))))))
	 | applyLatePolicy_false_false_true: (forall g lateDays , (ltbZ_rel lateDays 9 false) -> ((ltbZ_rel lateDays 17 false) -> ((ltbZ_rel lateDays 21 true) -> (forall (lowerGraderes: Grades_u), (lowerGrade_rel g lowerGraderes) -> (forall (lowerGrade_res_2: Grades_u), (lowerGrade_rel lowerGraderes lowerGrade_res_2) -> (applyLatePolicy_rel lateDays g lowerGrade_res_2))))))
	 | applyLatePolicy_false_true: (forall g lateDays , (ltbZ_rel lateDays 9 false) -> ((ltbZ_rel lateDays 17 true) -> (forall (lowerGraderes: Grades_u), (lowerGrade_rel g lowerGraderes) -> (applyLatePolicy_rel lateDays g lowerGraderes))))
	 | applyLatePolicy_true: (forall g lateDays , (ltbZ_rel lateDays 9 true) -> (applyLatePolicy_rel lateDays g g)). 
#[global] Hint Constructors applyLatePolicy_rel : core_hint_db.
#[global] Instance applyLatePolicy_lookup_rel : dictionary rel applyLatePolicy := { 
	lookup' := applyLatePolicy_rel
}.
#[global] Instance applyLatePolicy_getF : getFunc applyLatePolicy_rel := { 
	getF' := applyLatePolicy
}.
Definition applyLatePolicy_rel_funct [lateDays: Z] [g: Grades_u]: (forall (VV: Grades_u) (VV': Grades_u) (H: applyLatePolicy_rel lateDays g VV) (K: applyLatePolicy_rel lateDays g VV') , VV = VV'). 
Proof. 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve applyLatePolicy_rel_funct : f_rel_funct_db.
Theorem applyLatePolicy_false_false_false_false_false_true_false_true_true_lem (lateDays: _) (g: _) (x_3: _): (applyLatePolicy_rel lateDays g x_3) <-> (((((((ltbZ_rel lateDays 9 false) /\ (ltbZ_rel lateDays 17 false)) /\ (ltbZ_rel lateDays 21 false)) /\ (exists (lowerGraderes: Grades_u), (lowerGrade_rel g lowerGraderes) /\ (exists (lowerGrade_res_2: Grades_u), (lowerGrade_rel lowerGraderes lowerGrade_res_2) /\ (exists (lowerGrade_res_3: Grades_u), (lowerGrade_rel lowerGrade_res_2 x_3) /\ (x_3 = lowerGrade_res_3))))) \/ ((((ltbZ_rel lateDays 9 false) /\ (ltbZ_rel lateDays 17 false)) /\ (ltbZ_rel lateDays 21 true)) /\ (exists (lowerGraderes: Grades_u), (lowerGrade_rel g lowerGraderes) /\ (exists (lowerGrade_res_2: Grades_u), (lowerGrade_rel lowerGraderes x_3) /\ (x_3 = lowerGrade_res_2))))) \/ (((ltbZ_rel lateDays 9 false) /\ (ltbZ_rel lateDays 17 true)) /\ (exists (lowerGraderes: Grades_u), (lowerGrade_rel g x_3) /\ (x_3 = lowerGraderes)))) \/ ((ltbZ_rel lateDays 9 true) /\ (x_3 = g))). 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite applyLatePolicy_false_false_false_false_false_true_false_true_true_lem : f_rel_back.
Theorem applyLatePolicy_rel_ex (lateDays: Z) (g: Grades_u) (lateDays_p: True) (g_p: (Grades_wf g) /\ True): applyLatePolicy_rel lateDays g 
		(⌊ applyLatePolicy (exist _ lateDays lateDays_p) (exist _ g g_p) -⌋). 
Proof. 
	existence_lemma_pre applyLatePolicy; 
	let E := fresh "E" in 
	destruct (lateDays <? 9) as [ | ] eqn:E; [fix_notations | let E := fresh "E" in 
	destruct (lateDays <? 17) as [ | ] eqn:E; [fix_notations | let E := fresh "E" in 
	destruct (lateDays <? 21) as [ | ] eqn:E; [fix_notations | fix_notations]]]; 
	existence_lemma_quicksolve applyLatePolicy; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve applyLatePolicy_rel_ex : rel_ax_db.
Opaque applyLatePolicy. 
Theorem applyLatePolicy__applyLatePolicy_rel_rw (lateDays: Z) (g: Grades_u) (lateDays_p: True) (g_p: (Grades_wf g) /\ True) (VV: Grades_u): ((⌊ applyLatePolicy (exist _ lateDays lateDays_p) (exist _ g g_p) -⌋) = VV) <-> (applyLatePolicy_rel lateDays g VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite applyLatePolicy__applyLatePolicy_rel_rw : f_rel_funct_db.
#[global] Hint Resolve applyLatePolicy__applyLatePolicy_rel_rw : rel_ax_db.
#[global] Instance applyLatePolicy_lookup_rw : dictionary rwLem applyLatePolicy := { 
	lookup' := applyLatePolicy__applyLatePolicy_rel_rw
}.
Theorem applyLatePolicy__applyLatePolicy_rel (lateDays_r: {lateDays: Z | True}) (g_r: Grades) (VV: Grades_u): ((⌊ applyLatePolicy lateDays_r g_r -⌋) = VV) <-> (applyLatePolicy_rel (⌊ lateDays_r -⌋) (⌊ g_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite applyLatePolicy__applyLatePolicy_rel : f_rel_funct_db.
Theorem applyLatePolicy__applyLatePolicy_rel' (lateDays: Z) (g: Grades_u) (lateDays_r: {lateDays: Z | True}) (g_r: Grades) (VV: Grades_u): (lateDays = (⌊ lateDays_r -⌋)) -> ((g = (⌊ g_r -⌋)) -> (((⌊ applyLatePolicy lateDays_r g_r -⌋) = VV) <-> (applyLatePolicy_rel lateDays g VV))). 
Proof. 
	intros -> ->. 
	refine (applyLatePolicy__applyLatePolicy_rel lateDays_r g_r VV). 
Qed. 
#[global] Hint Resolve applyLatePolicy__applyLatePolicy_rel' : f_rel_funct_db.
Definition applyLatePolicy_rel_mk [lateDays: Z] [g: Grades_u] (lateDays_p: True) (g_p: (Grades_wf g) /\ True): {VV: _ | applyLatePolicy_rel lateDays g VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (applyLatePolicy_rel lateDays g VV)) 
		(applyLatePolicy (exist _ lateDays lateDays_p) (exist _ g g_p)) _); 
	rewrite <- applyLatePolicy__applyLatePolicy_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve applyLatePolicy_rel_mk : f_rel_funct_db.
#[global] Instance applyLatePolicyPack : (@Pack ({lateDays: Z | True} ::RT (fun (lateDays_r: {lateDays: Z | True}) => (Grades ::RT (fun (g_r: Grades) => nilRT)))) (Z ::UT (Grades_u ::UT nilUT)) (ltac: (mkProjectsArgListTG ({lateDays: Z | True} ::RT (fun (lateDays_r: {lateDays: Z | True}) => (Grades ::RT (fun (g_r: Grades) => nilRT)))) (Z ::UT (Grades_u ::UT nilUT)))) Grades_u (fun (x_11342935: (ArgList {lateDays: Z | True} ::RT (fun (lateDays_r: {lateDays: Z | True}) => (Grades ::RT (fun (g_r: Grades) => nilRT))))) => (fun (v_x_11342935: Grades_u) => (ltac: (flattenP (fun (lateDays_r: {lateDays: Z | True}) => (fun (g_r: Grades) => (fun (VV: Grades_u) => ((Grades_wf VV) /\ True)))) x_11342935 v_x_11342935))))).
Proof. 
	buildPackG applyLatePolicy applyLatePolicy_rel applyLatePolicy__applyLatePolicy_rel applyLatePolicy_rel_funct. 
Defined.
Definition lowerGradeFMinus: {{forall (lowerGraderes: Grades_u), (lowerGrade_rel (Grade_u F_u Minus_u) lowerGraderes) -> (lowerGraderes == (Grade_u F_u Minus_u))}}. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Defined. 
Definition lowerGradeThrice: {{forall (lowerGraderes: Grades_u), (lowerGrade_rel (Grade_u B_u Minus_u) lowerGraderes) -> (forall (lowerGrade_res_2: Grades_u), (lowerGrade_rel lowerGraderes lowerGrade_res_2) -> (forall (lowerGrade_res_3: Grades_u), (lowerGrade_rel lowerGrade_res_2 lowerGrade_res_3) -> (lowerGrade_res_3 == (Grade_u C_u Minus_u))))}}. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Defined. 
Definition lowerGradeTwice: {{forall (lowerGraderes: Grades_u), (lowerGrade_rel (Grade_u B_u Minus_u) lowerGraderes) -> (forall (lowerGrade_res_2: Grades_u), (lowerGrade_rel lowerGraderes lowerGrade_res_2) -> (lowerGrade_res_2 == (Grade_u C_u Natural_u)))}}. 
Proof. 
	refine (exist _ unit _); 
	solver. 
Defined. 
Definition noPenaltyForMostlyOnTime (lateDays: {lateDays: Z | True}) (g: Grades) (h: {{ltbZ_rel (⌊ lateDays -⌋) 9 true}}): {{forall (applyLatePolicyres: Grades_u), (applyLatePolicy_rel (⌊ lateDays -⌋) (⌊ g -⌋) applyLatePolicyres) -> (applyLatePolicyres = (⌊ g -⌋))}}. 
Proof. 
	destruct lateDays as [lateDays lateDays_p]. 
	destruct g as [g g_p]. 
	destruct h as [h h_p]. 
	let E := fresh "E" in 
	destruct (lateDays <? 9) as [ | ] eqn:E; [refine (exist _ unit _); 
	solver | refine (exist _ h _); 
	solver]. 
Defined. 
Inductive Comparison_u : Set := 
	 | Eq_u: Comparison_u
	 | Gt_u: Comparison_u
	 | Lt_u: Comparison_u. 
Fixpoint Comparison_eq (x: Comparison_u) (y: Comparison_u): bool := 
	match (x, y) with (Eq_u, Eq_u) => true | (Gt_u, Gt_u) => true | (Lt_u, Lt_u) => true | (_, _) => false end. 
Definition Comparison_eq_refl: (forall (x: Comparison_u) , is_true (Comparison_eq x x)). 
Proof. 
	eq_refl. 
Qed. 
#[global] Hint Resolve Comparison_eq_refl : eq_hint_db.
Definition Comparison_eqb_eq: (forall (s: Comparison_u) (t: Comparison_u) , (is_true (Comparison_eq s t)) -> (s = t)). 
Proof. 
	eqb_eq_lem. 
Qed. 
#[global] Hint Resolve Comparison_eqb_eq : eq_hint_db.
#[global] Instance leibnitz_eq_Comparison : LeibnitzEqB := { 
	equalB' := Comparison_eq;
	refl' := Comparison_eq_refl;
	eqb_eq' := Comparison_eqb_eq
}.
Fixpoint Comparison_wf (x: Comparison_u): Prop := 
	match x with Eq_u => True | Gt_u => True | Lt_u => True end. 
Theorem Comparison_wf_ref [p: Comparison_u -> Prop] (tm: {v: Comparison_u | (Comparison_wf v) /\ (p v)}): Comparison_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation Comparison := {x: Comparison_u | (Comparison_wf x) /\ True}. 
Definition Eq_lem: (Comparison_wf Eq_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Eq: Comparison := 
	exist _ Eq_u Eq_lem. 
Definition Gt_lem: (Comparison_wf Gt_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Gt: Comparison := 
	exist _ Gt_u Gt_lem. 
Definition Lt_lem: (Comparison_wf Lt_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Lt: Comparison := 
	exist _ Lt_u Lt_lem. 
#[global] Hint Resolve Comparison_wf_ref : wf_constr_db.
#[global] Hint Unfold Comparison_wf : wf_constr_db.
#[global] Hint Resolve Comparison_eq : ref_constr_db.
#[global] Hint Unfold Eq : ref_constr_db.
#[global] Hint Unfold Gt : ref_constr_db.
#[global] Hint Unfold Lt : ref_constr_db.
Definition letterComparison (l1: Letter) (l2: Letter): Comparison. 
Proof. 
	destruct l1 as [l1 l1_p]. 
	destruct l2 as [l2 l2_p]. 
	try revert l2_p; generalize dependent l2; 
	induction l1 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]. 
	  - intros . 
		induction l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]. 
		  -- intros . 
			refine (subsumptionCast _ _ Eq _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Gt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Gt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Gt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Gt _); 
			solver.   
	  - intros . 
		induction l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]. 
		  -- intros . 
			refine (subsumptionCast _ _ Lt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Eq _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Gt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Gt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Gt _); 
			solver.   
	  - intros . 
		induction l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]. 
		  -- intros . 
			refine (subsumptionCast _ _ Lt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Lt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Eq _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Gt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Gt _); 
			solver.   
	  - intros . 
		induction l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]. 
		  -- intros . 
			refine (subsumptionCast _ _ Lt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Lt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Lt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Eq _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Gt _); 
			solver.   
	  - intros . 
		induction l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]. 
		  -- intros . 
			refine (subsumptionCast _ _ Lt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Lt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Lt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Lt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Eq _); 
			solver.   
Defined. 
Inductive letterComparison_rel : (Letter_u -> (Letter_u -> (Comparison_u -> Prop))) := 
	 | letterComparison_A_A: letterComparison_rel A_u A_u Eq_u
	 | letterComparison_A_B: letterComparison_rel A_u B_u Gt_u
	 | letterComparison_A_C: letterComparison_rel A_u C_u Gt_u
	 | letterComparison_A_D: letterComparison_rel A_u D_u Gt_u
	 | letterComparison_A_F: letterComparison_rel A_u F_u Gt_u
	 | letterComparison_B_A: letterComparison_rel B_u A_u Lt_u
	 | letterComparison_B_B: letterComparison_rel B_u B_u Eq_u
	 | letterComparison_B_C: letterComparison_rel B_u C_u Gt_u
	 | letterComparison_B_D: letterComparison_rel B_u D_u Gt_u
	 | letterComparison_B_F: letterComparison_rel B_u F_u Gt_u
	 | letterComparison_C_A: letterComparison_rel C_u A_u Lt_u
	 | letterComparison_C_B: letterComparison_rel C_u B_u Lt_u
	 | letterComparison_C_C: letterComparison_rel C_u C_u Eq_u
	 | letterComparison_C_D: letterComparison_rel C_u D_u Gt_u
	 | letterComparison_C_F: letterComparison_rel C_u F_u Gt_u
	 | letterComparison_D_A: letterComparison_rel D_u A_u Lt_u
	 | letterComparison_D_B: letterComparison_rel D_u B_u Lt_u
	 | letterComparison_D_C: letterComparison_rel D_u C_u Lt_u
	 | letterComparison_D_D: letterComparison_rel D_u D_u Eq_u
	 | letterComparison_D_F: letterComparison_rel D_u F_u Gt_u
	 | letterComparison_F_A: letterComparison_rel F_u A_u Lt_u
	 | letterComparison_F_B: letterComparison_rel F_u B_u Lt_u
	 | letterComparison_F_C: letterComparison_rel F_u C_u Lt_u
	 | letterComparison_F_D: letterComparison_rel F_u D_u Lt_u
	 | letterComparison_F_F: letterComparison_rel F_u F_u Eq_u. 
#[global] Hint Constructors letterComparison_rel : core_hint_db.
#[global] Instance letterComparison_lookup_rel : dictionary rel letterComparison := { 
	lookup' := letterComparison_rel
}.
#[global] Instance letterComparison_getF : getFunc letterComparison_rel := { 
	getF' := letterComparison
}.
Definition letterComparison_rel_funct [l1: Letter_u] [l2: Letter_u]: (forall (VV: Comparison_u) (VV': Comparison_u) (H: letterComparison_rel l1 l2 VV) (K: letterComparison_rel l1 l2 VV') , VV = VV'). 
Proof. 
	try revert l2_p; generalize dependent l2; 
	destruct l1 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros ; 
	[destruct l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros | 
	destruct l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros | 
	destruct l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros | 
	destruct l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros | 
	destruct l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros ]; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve letterComparison_rel_funct : f_rel_funct_db.
Theorem letterComparison_A_A_lem: (letterComparison_rel A_u A_u Eq_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letterComparison_A_A_lem : f_rel_back.
Theorem letterComparison_A_B_lem: (letterComparison_rel A_u B_u Gt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letterComparison_A_B_lem : f_rel_back.
Theorem letterComparison_A_C_lem: (letterComparison_rel A_u C_u Gt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letterComparison_A_C_lem : f_rel_back.
Theorem letterComparison_A_D_lem: (letterComparison_rel A_u D_u Gt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letterComparison_A_D_lem : f_rel_back.
Theorem letterComparison_A_F_lem: (letterComparison_rel A_u F_u Gt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letterComparison_A_F_lem : f_rel_back.
Theorem letterComparison_B_A_lem: (letterComparison_rel B_u A_u Lt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letterComparison_B_A_lem : f_rel_back.
Theorem letterComparison_B_B_lem: (letterComparison_rel B_u B_u Eq_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letterComparison_B_B_lem : f_rel_back.
Theorem letterComparison_B_C_lem: (letterComparison_rel B_u C_u Gt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letterComparison_B_C_lem : f_rel_back.
Theorem letterComparison_B_D_lem: (letterComparison_rel B_u D_u Gt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letterComparison_B_D_lem : f_rel_back.
Theorem letterComparison_B_F_lem: (letterComparison_rel B_u F_u Gt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letterComparison_B_F_lem : f_rel_back.
Theorem letterComparison_C_A_lem: (letterComparison_rel C_u A_u Lt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letterComparison_C_A_lem : f_rel_back.
Theorem letterComparison_C_B_lem: (letterComparison_rel C_u B_u Lt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letterComparison_C_B_lem : f_rel_back.
Theorem letterComparison_C_C_lem: (letterComparison_rel C_u C_u Eq_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letterComparison_C_C_lem : f_rel_back.
Theorem letterComparison_C_D_lem: (letterComparison_rel C_u D_u Gt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letterComparison_C_D_lem : f_rel_back.
Theorem letterComparison_C_F_lem: (letterComparison_rel C_u F_u Gt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letterComparison_C_F_lem : f_rel_back.
Theorem letterComparison_D_A_lem: (letterComparison_rel D_u A_u Lt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letterComparison_D_A_lem : f_rel_back.
Theorem letterComparison_D_B_lem: (letterComparison_rel D_u B_u Lt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letterComparison_D_B_lem : f_rel_back.
Theorem letterComparison_D_C_lem: (letterComparison_rel D_u C_u Lt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letterComparison_D_C_lem : f_rel_back.
Theorem letterComparison_D_D_lem: (letterComparison_rel D_u D_u Eq_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letterComparison_D_D_lem : f_rel_back.
Theorem letterComparison_D_F_lem: (letterComparison_rel D_u F_u Gt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letterComparison_D_F_lem : f_rel_back.
Theorem letterComparison_F_A_lem: (letterComparison_rel F_u A_u Lt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letterComparison_F_A_lem : f_rel_back.
Theorem letterComparison_F_B_lem: (letterComparison_rel F_u B_u Lt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letterComparison_F_B_lem : f_rel_back.
Theorem letterComparison_F_C_lem: (letterComparison_rel F_u C_u Lt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letterComparison_F_C_lem : f_rel_back.
Theorem letterComparison_F_D_lem: (letterComparison_rel F_u D_u Lt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letterComparison_F_D_lem : f_rel_back.
Theorem letterComparison_F_F_lem: (letterComparison_rel F_u F_u Eq_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite letterComparison_F_F_lem : f_rel_back.
Theorem letterComparison_rel_ex (l1: Letter_u) (l2: Letter_u) (l1_p: (Letter_wf l1) /\ True) (l2_p: (Letter_wf l2) /\ True): letterComparison_rel l1 l2 (⌊ letterComparison (exist _ l1 l1_p) (exist _ l2 l2_p) -⌋). 
Proof. 
	existence_lemma_pre letterComparison; 
	try revert l2_p; generalize dependent l2; 
	destruct l1 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros ; 
	[destruct l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations]| 
	destruct l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations]| 
	destruct l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations]| 
	destruct l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations]| 
	destruct l2 as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations| 
	fix_notations]]; 
	existence_lemma_quicksolve letterComparison; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve letterComparison_rel_ex : rel_ax_db.
Opaque letterComparison. 
Theorem letterComparison__letterComparison_rel_rw (l1: Letter_u) (l2: Letter_u) (l1_p: (Letter_wf l1) /\ True) (l2_p: (Letter_wf l2) /\ True) (VV: Comparison_u): ((⌊ letterComparison (exist _ l1 l1_p) (exist _ l2 l2_p) -⌋) = VV) <-> (letterComparison_rel l1 l2 VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite letterComparison__letterComparison_rel_rw : f_rel_funct_db.
#[global] Hint Resolve letterComparison__letterComparison_rel_rw : rel_ax_db.
#[global] Instance letterComparison_lookup_rw : dictionary rwLem letterComparison := { 
	lookup' := letterComparison__letterComparison_rel_rw
}.
Theorem letterComparison__letterComparison_rel (l1_r: Letter) (l2_r: Letter) (VV: Comparison_u): ((⌊ letterComparison l1_r l2_r -⌋) = VV) <-> (letterComparison_rel (⌊ l1_r -⌋) (⌊ l2_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite letterComparison__letterComparison_rel : f_rel_funct_db.
Theorem letterComparison__letterComparison_rel' (l1: Letter_u) (l2: Letter_u) (l1_r: Letter) (l2_r: Letter) (VV: Comparison_u): (l1 = (⌊ l1_r -⌋)) -> ((l2 = (⌊ l2_r -⌋)) -> (((⌊ letterComparison l1_r l2_r -⌋) = VV) <-> (letterComparison_rel l1 l2 VV))). 
Proof. 
	intros -> ->. 
	refine (letterComparison__letterComparison_rel l1_r l2_r VV). 
Qed. 
#[global] Hint Resolve letterComparison__letterComparison_rel' : f_rel_funct_db.
Definition letterComparison_rel_mk [l1: Letter_u] [l2: Letter_u] (l1_p: (Letter_wf l1) /\ True) (l2_p: (Letter_wf l2) /\ True): {VV: _ | letterComparison_rel l1 l2 VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (letterComparison_rel l1 l2 VV)) (letterComparison (exist _ l1 l1_p) (exist _ l2 l2_p)) _); 
	rewrite <- letterComparison__letterComparison_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve letterComparison_rel_mk : f_rel_funct_db.
#[global] Instance letterComparisonPack : (@Pack (Letter ::RT (fun (l1_r: Letter) => (Letter ::RT (fun (l2_r: Letter) => nilRT)))) (Letter_u ::UT (Letter_u ::UT nilUT)) (ltac: (mkProjectsArgListTG (Letter ::RT (fun (l1_r: Letter) => (Letter ::RT (fun (l2_r: Letter) => nilRT)))) (Letter_u ::UT (Letter_u ::UT nilUT)))) Comparison_u (fun (x_74941377: (ArgList Letter ::RT (fun (l1_r: Letter) => (Letter ::RT (fun (l2_r: Letter) => nilRT))))) => (fun (v_x_74941377: Comparison_u) => (ltac: (flattenP (fun (l1_r: Letter) => (fun (l2_r: Letter) => (fun (VV: Comparison_u) => ((Comparison_wf VV) /\ True)))) x_74941377 v_x_74941377))))).
Proof. 
	buildPackG letterComparison letterComparison_rel letterComparison__letterComparison_rel letterComparison_rel_funct. 
Defined.
Definition letterComparisonEq (l: Letter): {{forall (letterComparisonres: Comparison_u), (letterComparison_rel (⌊ l -⌋) (⌊ l -⌋) letterComparisonres) -> (letterComparisonres = Eq_u)}}. 
Proof. 
	destruct l as [l l_p]. 
	induction l as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]. 
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
Defined. 
Definition lowerLetterLowers (l: Letter) (p: {{forall (letterComparisonres: Comparison_u), (letterComparison_rel F_u (⌊ l -⌋) letterComparisonres) -> (letterComparisonres = Lt_u)}}): {{forall (lowerLetterres: Letter_u), (lowerLetter_rel (⌊ l -⌋) lowerLetterres) -> (forall (letterComparisonres: Comparison_u), (letterComparison_rel lowerLetterres (⌊ l -⌋) letterComparisonres) -> (letterComparisonres = Lt_u))}}. 
Proof. 
	destruct l as [l l_p]. 
	destruct p as [p p_p]. 
	try revert p_p; generalize dependent p; 
	induction l as [(*A*)  | (*B*)  | (*C*)  | (*D*)  | (*F*) ]. 
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
	  - intros . 
		refine (exist _ p _); 
		solver.  
Defined. 
Definition modifierComparison (m1: Modifier) (m2: Modifier): Comparison. 
Proof. 
	destruct m1 as [m1 m1_p]. 
	destruct m2 as [m2 m2_p]. 
	try revert m2_p; generalize dependent m2; 
	induction m1 as [(*Minus*)  | (*Natural*)  | (*Plus*) ]. 
	  - intros . 
		induction m2 as [(*Minus*)  | (*Natural*)  | (*Plus*) ]. 
		  -- intros . 
			refine (subsumptionCast _ _ Eq _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Lt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Lt _); 
			solver.   
	  - intros . 
		induction m2 as [(*Minus*)  | (*Natural*)  | (*Plus*) ]. 
		  -- intros . 
			refine (subsumptionCast _ _ Gt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Eq _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Lt _); 
			solver.   
	  - intros . 
		induction m2 as [(*Minus*)  | (*Natural*)  | (*Plus*) ]. 
		  -- intros . 
			refine (subsumptionCast _ _ Gt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Gt _); 
			solver.  
		  -- intros . 
			refine (subsumptionCast _ _ Eq _); 
			solver.   
Defined. 
Inductive modifierComparison_rel : (Modifier_u -> (Modifier_u -> (Comparison_u -> Prop))) := 
	 | modifierComparison_Plus_Plus: modifierComparison_rel Plus_u Plus_u Eq_u
	 | modifierComparison_Plus_Natural: modifierComparison_rel Plus_u Natural_u Gt_u
	 | modifierComparison_Plus_Minus: modifierComparison_rel Plus_u Minus_u Gt_u
	 | modifierComparison_Natural_Plus: modifierComparison_rel Natural_u Plus_u Lt_u
	 | modifierComparison_Natural_Natural: modifierComparison_rel Natural_u Natural_u Eq_u
	 | modifierComparison_Natural_Minus: modifierComparison_rel Natural_u Minus_u Gt_u
	 | modifierComparison_Minus_Plus: modifierComparison_rel Minus_u Plus_u Lt_u
	 | modifierComparison_Minus_Natural: modifierComparison_rel Minus_u Natural_u Lt_u
	 | modifierComparison_Minus_Minus: modifierComparison_rel Minus_u Minus_u Eq_u. 
#[global] Hint Constructors modifierComparison_rel : core_hint_db.
#[global] Instance modifierComparison_lookup_rel : dictionary rel modifierComparison := { 
	lookup' := modifierComparison_rel
}.
#[global] Instance modifierComparison_getF : getFunc modifierComparison_rel := { 
	getF' := modifierComparison
}.
Definition modifierComparison_rel_funct [m1: Modifier_u] [m2: Modifier_u]: (forall (VV: Comparison_u) (VV': Comparison_u) (H: modifierComparison_rel m1 m2 VV) (K: modifierComparison_rel m1 m2 VV') , VV = VV'). 
Proof. 
	try revert m2_p; generalize dependent m2; 
	destruct m1 as [(*Minus*)  | (*Natural*)  | (*Plus*) ]; 
	intros ; 
	[destruct m2 as [(*Minus*)  | (*Natural*)  | (*Plus*) ]; 
	intros | 
	destruct m2 as [(*Minus*)  | (*Natural*)  | (*Plus*) ]; 
	intros | 
	destruct m2 as [(*Minus*)  | (*Natural*)  | (*Plus*) ]; 
	intros ]; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve modifierComparison_rel_funct : f_rel_funct_db.
Theorem modifierComparison_Plus_Plus_lem: (modifierComparison_rel Plus_u Plus_u Eq_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite modifierComparison_Plus_Plus_lem : f_rel_back.
Theorem modifierComparison_Plus_Natural_lem: (modifierComparison_rel Plus_u Natural_u Gt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite modifierComparison_Plus_Natural_lem : f_rel_back.
Theorem modifierComparison_Plus_Minus_lem: (modifierComparison_rel Plus_u Minus_u Gt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite modifierComparison_Plus_Minus_lem : f_rel_back.
Theorem modifierComparison_Natural_Plus_lem: (modifierComparison_rel Natural_u Plus_u Lt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite modifierComparison_Natural_Plus_lem : f_rel_back.
Theorem modifierComparison_Natural_Natural_lem: (modifierComparison_rel Natural_u Natural_u Eq_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite modifierComparison_Natural_Natural_lem : f_rel_back.
Theorem modifierComparison_Natural_Minus_lem: (modifierComparison_rel Natural_u Minus_u Gt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite modifierComparison_Natural_Minus_lem : f_rel_back.
Theorem modifierComparison_Minus_Plus_lem: (modifierComparison_rel Minus_u Plus_u Lt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite modifierComparison_Minus_Plus_lem : f_rel_back.
Theorem modifierComparison_Minus_Natural_lem: (modifierComparison_rel Minus_u Natural_u Lt_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite modifierComparison_Minus_Natural_lem : f_rel_back.
Theorem modifierComparison_Minus_Minus_lem: (modifierComparison_rel Minus_u Minus_u Eq_u) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite modifierComparison_Minus_Minus_lem : f_rel_back.
Theorem modifierComparison_rel_ex (m1: Modifier_u) (m2: Modifier_u) (m1_p: (Modifier_wf m1) /\ True) (m2_p: (Modifier_wf m2) /\ True): modifierComparison_rel m1 m2 
		(⌊ modifierComparison (exist _ m1 m1_p) (exist _ m2 m2_p) -⌋). 
Proof. 
	existence_lemma_pre modifierComparison; 
	try revert m2_p; generalize dependent m2; 
	destruct m1 as [(*Minus*)  | (*Natural*)  | (*Plus*) ]; 
	intros ; 
	[destruct m2 as [(*Minus*)  | (*Natural*)  | (*Plus*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations| 
	fix_notations]| 
	destruct m2 as [(*Minus*)  | (*Natural*)  | (*Plus*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations| 
	fix_notations]| 
	destruct m2 as [(*Minus*)  | (*Natural*)  | (*Plus*) ]; 
	intros ; 
	[fix_notations| 
	fix_notations| 
	fix_notations]]; 
	existence_lemma_quicksolve modifierComparison; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve modifierComparison_rel_ex : rel_ax_db.
Opaque modifierComparison. 
Theorem modifierComparison__modifierComparison_rel_rw (m1: Modifier_u) (m2: Modifier_u) (m1_p: (Modifier_wf m1) /\ True) (m2_p: (Modifier_wf m2) /\ True) (VV: Comparison_u): ((⌊ modifierComparison (exist _ m1 m1_p) (exist _ m2 m2_p) -⌋) = VV) <-> (modifierComparison_rel m1 m2 VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite modifierComparison__modifierComparison_rel_rw : f_rel_funct_db.
#[global] Hint Resolve modifierComparison__modifierComparison_rel_rw : rel_ax_db.
#[global] Instance modifierComparison_lookup_rw : dictionary rwLem modifierComparison := { 
	lookup' := modifierComparison__modifierComparison_rel_rw
}.
Theorem modifierComparison__modifierComparison_rel (m1_r: Modifier) (m2_r: Modifier) (VV: Comparison_u): ((⌊ modifierComparison m1_r m2_r -⌋) = VV) <-> (modifierComparison_rel (⌊ m1_r -⌋) (⌊ m2_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite modifierComparison__modifierComparison_rel : f_rel_funct_db.
Theorem modifierComparison__modifierComparison_rel' (m1: Modifier_u) (m2: Modifier_u) (m1_r: Modifier) (m2_r: Modifier) (VV: Comparison_u): (m1 = (⌊ m1_r -⌋)) -> ((m2 = (⌊ m2_r -⌋)) -> (((⌊ modifierComparison m1_r m2_r -⌋) = VV) <-> (modifierComparison_rel m1 m2 VV))). 
Proof. 
	intros -> ->. 
	refine (modifierComparison__modifierComparison_rel m1_r m2_r VV). 
Qed. 
#[global] Hint Resolve modifierComparison__modifierComparison_rel' : f_rel_funct_db.
Definition modifierComparison_rel_mk [m1: Modifier_u] [m2: Modifier_u] (m1_p: (Modifier_wf m1) /\ True) (m2_p: (Modifier_wf m2) /\ True): {VV: _ | modifierComparison_rel m1 m2 VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (modifierComparison_rel m1 m2 VV)) (modifierComparison (exist _ m1 m1_p) (exist _ m2 m2_p)) _); 
	rewrite <- modifierComparison__modifierComparison_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve modifierComparison_rel_mk : f_rel_funct_db.
#[global] Instance modifierComparisonPack : (@Pack (Modifier ::RT (fun (m1_r: Modifier) => (Modifier ::RT (fun (m2_r: Modifier) => nilRT)))) (Modifier_u ::UT (Modifier_u ::UT nilUT)) (ltac: (mkProjectsArgListTG (Modifier ::RT (fun (m1_r: Modifier) => (Modifier ::RT (fun (m2_r: Modifier) => nilRT)))) (Modifier_u ::UT (Modifier_u ::UT nilUT)))) Comparison_u (fun (x_13952235: (ArgList Modifier ::RT (fun (m1_r: Modifier) => (Modifier ::RT (fun (m2_r: Modifier) => nilRT))))) => (fun (v_x_13952235: Comparison_u) => (ltac: (flattenP (fun (m1_r: Modifier) => (fun (m2_r: Modifier) => (fun (VV: Comparison_u) => ((Comparison_wf VV) /\ True)))) x_13952235 v_x_13952235))))).
Proof. 
	buildPackG modifierComparison modifierComparison_rel modifierComparison__modifierComparison_rel modifierComparison_rel_funct. 
Defined.