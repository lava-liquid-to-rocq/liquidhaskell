From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Inductive RBin_u : Type := 
	 | RB0_u: RBin_u -> RBin_u
	 | RB1_u: RBin_u -> RBin_u
	 | RZ_u: RBin_u. 
Fixpoint RBin_eq (x: RBin_u) (y: RBin_u): bool := 
	match (x, y) with (RB0_u x, RB0_u x') => (true && (RBin_eq x x')) | (RB1_u x, RB1_u x') => (true && (RBin_eq x x')) | (RZ_u, RZ_u) => true | (_, _) => false end. 
Theorem RBin_eq_refl: (forall (x: RBin_u) , is_true (RBin_eq x x)). 
Proof. 
	eq_refl_rec. 
Qed. 
#[global] Hint Resolve RBin_eq_refl : eq_hint_db.
Theorem RBin_eqb_eq: (forall (s: RBin_u) (t: RBin_u) , (is_true (RBin_eq s t)) -> (s = t)). 
Proof. 
	eqb_eq_lem. 
Qed. 
#[global] Hint Resolve RBin_eqb_eq : eq_hint_db.
#[global] Instance leibnitz_eq_RBin : LeibnitzEqB := { 
	equalB' := RBin_eq;
	refl' := RBin_eq_refl;
	eqb_eq' := RBin_eqb_eq
}.
Fixpoint RBin_wf (x: RBin_u): Prop := 
	match x with (RB0_u n) => ((RBin_wf n) /\ (n <> RZ_u)) | (RB1_u n) => ((RBin_wf n) /\ True) | RZ_u => True end. 
Theorem RBin_wf_ref [p: RBin_u -> Prop] (tm: {v: RBin_u | (RBin_wf v) /\ (p v)}): RBin_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation RBin := {x: RBin_u | (RBin_wf x) /\ True}. 
Definition RB0_lem (n: {n: RBin_u | (RBin_wf n) /\ (n <> RZ_u)}): (RBin_wf (RB0_u (⌊ n -⌋))) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition RB0 (n: {n: RBin_u | (RBin_wf n) /\ (n <> RZ_u)}): RBin := 
	exist _ (RB0_u (⌊ n -⌋)) (RB0_lem n). 
Definition RB1_lem (n: RBin): (RBin_wf (RB1_u (⌊ n -⌋))) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition RB1 (n: RBin): RBin := 
	exist _ (RB1_u (⌊ n -⌋)) (RB1_lem n). 
Definition RZ_lem: (RBin_wf RZ_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition RZ: RBin := 
	exist _ RZ_u RZ_lem. 
Definition wf_RB0_n [n: RBin_u] (p: RBin_wf (RB0_u n)): RBin_wf n. 
Proof. 
	quicksolve. 
Defined. 
Definition wf_RB1_n [n: RBin_u] (p: RBin_wf (RB1_u n)): RBin_wf n. 
Proof. 
	quicksolve. 
Defined. 
#[global] Hint Resolve RBin_wf_ref : wf_constr_db.
#[global] Hint Unfold RBin_wf : wf_constr_db.
#[global] Hint Resolve RBin_eq : ref_constr_db.
#[global] Hint Resolve wf_RB0_n : ref_constr_db.
#[global] Hint Resolve wf_RB1_n : ref_constr_db.
#[global] Hint Unfold RB0 : ref_constr_db.
#[global] Hint Unfold RB1 : ref_constr_db.
#[global] Hint Unfold RZ : ref_constr_db.
Inductive Bin_u : Type := 
	 | B0_u: Bin_u -> Bin_u
	 | B1_u: Bin_u -> Bin_u
	 | RBinsToBins__Z_u: Bin_u. 
Fixpoint Bin_eq (x: Bin_u) (y: Bin_u): bool := 
	match (x, y) with (B0_u x, B0_u x') => (true && (Bin_eq x x')) | (B1_u x, B1_u x') => (true && (Bin_eq x x')) | (RBinsToBins__Z_u, RBinsToBins__Z_u) => true | (_, _) => false end. 
Theorem Bin_eq_refl: (forall (x: Bin_u) , is_true (Bin_eq x x)). 
Proof. 
	eq_refl_rec. 
Qed. 
#[global] Hint Resolve Bin_eq_refl : eq_hint_db.
Theorem Bin_eqb_eq: (forall (s: Bin_u) (t: Bin_u) , (is_true (Bin_eq s t)) -> (s = t)). 
Proof. 
	eqb_eq_lem. 
Qed. 
#[global] Hint Resolve Bin_eqb_eq : eq_hint_db.
#[global] Instance leibnitz_eq_Bin : LeibnitzEqB := { 
	equalB' := Bin_eq;
	refl' := Bin_eq_refl;
	eqb_eq' := Bin_eqb_eq
}.
Fixpoint Bin_wf (x: Bin_u): Prop := 
	match x with (B0_u n) => ((Bin_wf n) /\ True) | (B1_u n) => ((Bin_wf n) /\ True) | RBinsToBins__Z_u => True end. 
Theorem Bin_wf_ref [p: Bin_u -> Prop] (tm: {v: Bin_u | (Bin_wf v) /\ (p v)}): Bin_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation Bin := {x: Bin_u | (Bin_wf x) /\ True}. 
Definition B0_lem (n: Bin): (Bin_wf (B0_u (⌊ n -⌋))) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition B0 (n: Bin): Bin := 
	exist _ (B0_u (⌊ n -⌋)) (B0_lem n). 
Definition B1_lem (n: Bin): (Bin_wf (B1_u (⌊ n -⌋))) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition B1 (n: Bin): Bin := 
	exist _ (B1_u (⌊ n -⌋)) (B1_lem n). 
Definition RBinsToBins__Z_lem: (Bin_wf RBinsToBins__Z_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition RBinsToBins__Z: Bin := 
	exist _ RBinsToBins__Z_u RBinsToBins__Z_lem. 
Definition wf_B0_n [n: Bin_u] (p: Bin_wf (B0_u n)): Bin_wf n. 
Proof. 
	quicksolve. 
Defined. 
Definition wf_B1_n [n: Bin_u] (p: Bin_wf (B1_u n)): Bin_wf n. 
Proof. 
	quicksolve. 
Defined. 
#[global] Hint Resolve Bin_wf_ref : wf_constr_db.
#[global] Hint Unfold Bin_wf : wf_constr_db.
#[global] Hint Resolve Bin_eq : ref_constr_db.
#[global] Hint Resolve wf_B0_n : ref_constr_db.
#[global] Hint Resolve wf_B1_n : ref_constr_db.
#[global] Hint Unfold B0 : ref_constr_db.
#[global] Hint Unfold B1 : ref_constr_db.
#[global] Hint Unfold RBinsToBins__Z : ref_constr_db.
Definition rbinToBin (b: RBin): Bin. 
Proof. 
	destruct b as [b b_p]. 
	induction b as [(*RB0*) n IH_n | (*RB1*) n IH_n | (*RZ*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ 
		(B0 
		(subsumptionCast Bin_u (fun (n: Bin_u) => ((Bin_wf n) /\ True)) (IH_n (ltac: (try clear IH_n; 
	solver))) (ltac: (solver)))) _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ 
		(B1 
		(subsumptionCast Bin_u (fun (n: Bin_u) => ((Bin_wf n) /\ True)) (IH_n (ltac: (try clear IH_n; 
	solver))) (ltac: (solver)))) _); 
		solver.  
	  - intros . 
		refine (subsumptionCast _ _ RBinsToBins__Z _); 
		solver.  
Defined. 