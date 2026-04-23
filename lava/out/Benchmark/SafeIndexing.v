From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Set Universe Polymorphism.
Inductive IList_u : Type := 
	 | Cons_u: Z -> (IList_u -> IList_u)
	 | Nil_u: IList_u. 
Fixpoint IList_eq (x: IList_u) (y: IList_u): bool := 
	match (x, y) with (Cons_u x x_1, Cons_u x' x_1') => ((true && (x ==? x')) && (IList_eq x_1 x_1')) | (Nil_u, Nil_u) => true | (_, _) => false end. 
Theorem IList_eq_refl: (forall (x: IList_u) , is_true (IList_eq x x)). 
Proof. 
	eq_refl_rec. 
Qed. 
#[global] Hint Resolve IList_eq_refl : eq_hint_db.
Theorem IList_eqb_eq: (forall (s: IList_u) (t: IList_u) , (is_true (IList_eq s t)) -> (s = t)). 
Proof. 
	eqb_eq_lem. 
Qed. 
#[global] Hint Resolve IList_eqb_eq : eq_hint_db.
#[global] Instance leibnitz_eq_IList : LeibnitzEqB := { 
	equalB' := IList_eq;
	refl' := IList_eq_refl;
	eqb_eq' := IList_eqb_eq
}.
Fixpoint IList_wf (x: IList_u): Prop := 
	match x with (Cons_u n l) => ((ltbZ_rel 5 n true) /\ ((IList_wf l) /\ True)) | Nil_u => True end. 
Theorem IList_wf_ref [p: IList_u -> Prop] (tm: {v: IList_u | (IList_wf v) /\ (p v)}): IList_wf (⌊ tm -⌋). 
Proof. 
	destruct tm as [tm tm_p]. 
	solver. 
Qed. 
Global Notation IList := {x: IList_u | (IList_wf x) /\ True}. 
Definition Cons_lem (n: {n: Z | ltbZ_rel 5 n true}) (l: IList): (IList_wf (Cons_u (⌊ n -⌋) (⌊ l -⌋))) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Cons (n: {n: Z | ltbZ_rel 5 n true}) (l: IList): IList := 
	exist _ (Cons_u (⌊ n -⌋) (⌊ l -⌋)) (Cons_lem n l). 
Definition Nil_lem: (IList_wf Nil_u) /\ True. 
Proof. 
	repeat first [split; solver]. 
Defined. 
Definition Nil: IList := 
	exist _ Nil_u Nil_lem. 
Definition wf_Cons_l [n: Z] [l: IList_u] (p: IList_wf (Cons_u n l)): IList_wf l. 
Proof. 
	quicksolve. 
Defined. 
#[global] Hint Resolve IList_wf_ref : wf_constr_db.
#[global] Hint Unfold IList_wf : wf_constr_db.
#[global] Hint Resolve IList_eq : ref_constr_db.
#[global] Hint Resolve wf_Cons_l : ref_constr_db.
#[global] Hint Unfold Cons : ref_constr_db.
#[global] Hint Unfold Nil : ref_constr_db.
Definition llen_spec (l: IList): Type := 
	{v: Z | gebZ_rel v 0 true}. 
#[global] Hint Unfold llen_spec : lia_unfold.
Definition llen (l: IList): llen_spec l. 
Proof. 
	destruct l as [l l_p]. 
	induction l as [(*Cons*) ds_d4yR l' IH_l' | (*Nil*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ 
		((subsumptionCast Z (fun (x_1: Z) => True) (IH_l' (ltac: (try clear IH_l'; 
	solver))) (ltac: (solver))) +Z (exist (fun (x_2: Z) => True) 1 (ltac: (solver)))) _); 
		solver.  
	  - intros . 
		refine (exist _ 0 _); 
		solver.  
Defined. 
Inductive llen_rel : (IList_u -> (Z -> Prop)) := 
	 | llen_Cons: (forall ds_d4yR l' , forall (llenres: Z), (llen_rel l' llenres) -> (forall (addZres: Z), (addZ_rel llenres 1 addZres) -> (llen_rel (Cons_u ds_d4yR l') addZres)))
	 | llen_Nil: llen_rel Nil_u 0. 
#[global] Hint Constructors llen_rel : core_hint_db.
#[global] Instance llen_lookup_rel : dictionary rel llen := { 
	lookup' := llen_rel
}.
#[global] Instance llen_getF : getFunc llen_rel := { 
	getF' := llen
}.
Theorem llen_rel_funct [l: IList_u]: (forall (v: Z) (v': Z) (H: llen_rel l v) (K: llen_rel l v') , v = v'). 
Proof. 
	induction l as [(*Cons*) ds_d4yR l' IH_l' | (*Nil*) ]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve llen_rel_funct : f_rel_funct_db.
Theorem llen_Cons_lem (ds_d4yR: _) (l': _) (addZres: Z): (llen_rel (Cons_u ds_d4yR l') addZres) <-> (exists (llenres: Z), (llen_rel l' llenres) /\ (addZ_rel llenres 1 addZres)). 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite llen_Cons_lem : f_rel_back.
Theorem llen_Nil_lem (res: Z): (llen_rel Nil_u res) <-> (res = 0). 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite llen_Nil_lem : f_rel_back.
Theorem llen_rel_ex (l: IList_u) (l_p: (IList_wf l) /\ True): llen_rel l (⌊ llen (exist _ l l_p) -⌋). 
Proof. 
	Opaque llen.
	existence_lemma_pre llen; 
	induction l as [(*Cons*) ds_d4yR l' IH_l' | (*Nil*) ]; 
	intros ; 
	[fix_notations; 
	pose proof (IH_l' (ltac: (try clear IH_l'; 
	solver))) as IH_11973733; 
	try clear IH_l'| 
	fix_notations]; 
	simpl in *. 
	Transparent llen.
	all: existence_lemma_quicksolve llen; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve llen_rel_ex : rel_ax_db.
#[global] Opaque llen. 
Theorem llen__llen_rel_rw (l: IList_u) (l_p: (IList_wf l) /\ True) (v: Z): ((⌊ llen (exist _ l l_p) -⌋) = v) <-> (llen_rel l v). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite llen__llen_rel_rw : f_rel_funct_db.
#[global] Hint Resolve llen__llen_rel_rw : rel_ax_db.
#[global] Instance llen_lookup_rw : dictionary rwLem llen := { 
	lookup' := llen__llen_rel_rw
}.
Theorem llen__llen_rel (l_r: IList) (v: Z): ((⌊ llen l_r -⌋) = v) <-> (llen_rel (⌊ l_r -⌋) v). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite llen__llen_rel : f_rel_funct_db.
Theorem llen__llen_rel' (l: IList_u) (l_r: IList) (v: Z): (l = (⌊ l_r -⌋)) -> (((⌊ llen l_r -⌋) = v) <-> (llen_rel l v)). 
Proof. 
	intros ->. 
	refine (llen__llen_rel l_r v). 
Qed. 
#[global] Hint Resolve llen__llen_rel' : f_rel_funct_db.
Theorem llen_rel_mk [l: IList_u] (l_p: (IList_wf l) /\ True): {v: _ | llen_rel l v}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (v: _) => (llen_rel l v)) (llen (exist _ l l_p)) _); 
	rewrite <- llen__llen_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve llen_rel_mk : f_rel_funct_db.
#[global] Instance llenPack : (@Pack (IList ::RT (fun (l_r: IList) => nilRT)) (IList_u ::UT nilUT) (ltac: (mkProjectsArgListTG (IList ::RT (fun (l_r: IList) => nilRT)) (IList_u ::UT nilUT))) Z (fun (x_86852483: (ArgList IList ::RT (fun (l_r: IList) => nilRT))) => (fun (v_x_86852483: Z) => (ltac: (flattenP (fun (l_r: IList) => (fun (v: Z) => (gebZ_rel v 0 true))) x_86852483 v_x_86852483))))).
Proof. 
	buildPackG llen llen_rel llen__llen_rel llen_rel_funct. 
Defined.
Definition append_spec (xs: IList) (ys: IList): Type := 
	{v: IList_u | (IList_wf v) /\ (exists (llenres: Z), (llen_rel v llenres) /\ (exists (llen_res_2: Z), (llen_rel (⌊ xs -⌋) llen_res_2) /\ (exists (llen_res_3: Z), (llen_rel (⌊ ys -⌋) llen_res_3) /\ (exists (addZres: Z), (addZ_rel llen_res_2 llen_res_3 addZres) /\ (llenres == addZres)))))}. 
#[global] Hint Unfold append_spec : lia_unfold.
Definition append (xs: IList) (ys: IList): append_spec xs ys. 
Proof. 
	destruct xs as [xs xs_p]. 
	destruct ys as [ys ys_p]. 
	try revert ys_p; generalize dependent ys; 
	induction xs as [(*Cons*) x xs IH_xs | (*Nil*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ 
		(Cons 
		(exist (fun (n: Z) => (ltbZ_rel 5 n true)) x (ltac: (solver))) 
		(subsumptionCast IList_u (fun (l: IList_u) => ((IList_wf l) /\ True)) 
		(IH_xs (ltac: (try clear IH_xs; 
	solver)) ys (ltac: (try clear IH_xs; 
	solver))) (ltac: (solver)))) _); 
		solver.  
	  - intros . 
		refine (exist _ ys _); 
		solver.  
Defined. 
Inductive append_rel : (IList_u -> (IList_u -> (IList_u -> Prop))) := 
	 | append_Cons: (forall x xs ys , forall (appendres: IList_u), (append_rel xs ys appendres) -> (append_rel (Cons_u x xs) ys (Cons_u x appendres)))
	 | append_Nil: (forall ys , append_rel Nil_u ys ys). 
#[global] Hint Constructors append_rel : core_hint_db.
#[global] Instance append_lookup_rel : dictionary rel append := { 
	lookup' := append_rel
}.
#[global] Instance append_getF : getFunc append_rel := { 
	getF' := append
}.
Theorem append_rel_funct [xs: IList_u] [ys: IList_u]: (forall (v: IList_u) (v': IList_u) (H: append_rel xs ys v) (K: append_rel xs ys v') , v = v'). 
Proof. 
	try revert ys_p; generalize dependent ys; 
	induction xs as [(*Cons*) x xs IH_xs | (*Nil*) ]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve append_rel_funct : f_rel_funct_db.
Theorem append_Cons_lem (x: _) (xs: _) (ys: _) (appendres: IList_u) (h_86920335: append_rel xs ys appendres): (append_rel (Cons_u x xs) ys (Cons_u x appendres)) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite append_Cons_lem : f_rel_back.
Theorem append_Nil_lem (ys: _): (append_rel Nil_u ys ys) <-> True. 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite append_Nil_lem : f_rel_back.
Theorem append_rel_ex (xs: IList_u) (ys: IList_u) (xs_p: (IList_wf xs) /\ True) (ys_p: (IList_wf ys) /\ True): append_rel xs ys (⌊ append (exist _ xs xs_p) (exist _ ys ys_p) -⌋). 
Proof. 
	Opaque append.
	existence_lemma_pre append; 
	try revert ys_p; generalize dependent ys; 
	induction xs as [(*Cons*) x xs IH_xs | (*Nil*) ]; 
	intros ; 
	[fix_notations; 
	pose proof (IH_xs (ltac: (try clear IH_xs; 
	solver)) ys (ltac: (try clear IH_xs; 
	solver))) as IH_46568342; 
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
Theorem append__append_rel_rw (xs: IList_u) (ys: IList_u) (xs_p: (IList_wf xs) /\ True) (ys_p: (IList_wf ys) /\ True) (v: IList_u): ((⌊ append (exist _ xs xs_p) (exist _ ys ys_p) -⌋) = v) <-> (append_rel xs ys v). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite append__append_rel_rw : f_rel_funct_db.
#[global] Hint Resolve append__append_rel_rw : rel_ax_db.
#[global] Instance append_lookup_rw : dictionary rwLem append := { 
	lookup' := append__append_rel_rw
}.
Theorem append__append_rel (xs_r: IList) (ys_r: IList) (v: IList_u): ((⌊ append xs_r ys_r -⌋) = v) <-> (append_rel (⌊ xs_r -⌋) (⌊ ys_r -⌋) v). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite append__append_rel : f_rel_funct_db.
Theorem append__append_rel' (xs: IList_u) (ys: IList_u) (xs_r: IList) (ys_r: IList) (v: IList_u): (xs = (⌊ xs_r -⌋)) -> ((ys = (⌊ ys_r -⌋)) -> (((⌊ append xs_r ys_r -⌋) = v) <-> (append_rel xs ys v))). 
Proof. 
	intros -> ->. 
	refine (append__append_rel xs_r ys_r v). 
Qed. 
#[global] Hint Resolve append__append_rel' : f_rel_funct_db.
Theorem append_rel_mk [xs: IList_u] [ys: IList_u] (xs_p: (IList_wf xs) /\ True) (ys_p: (IList_wf ys) /\ True): {v: _ | append_rel xs ys v}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (v: _) => (append_rel xs ys v)) (append (exist _ xs xs_p) (exist _ ys ys_p)) _); 
	rewrite <- append__append_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve append_rel_mk : f_rel_funct_db.
#[global] Instance appendPack : (@Pack (IList ::RT (fun (xs_r: IList) => (IList ::RT (fun (ys_r: IList) => nilRT)))) (IList_u ::UT (IList_u ::UT nilUT)) (ltac: (mkProjectsArgListTG (IList ::RT (fun (xs_r: IList) => (IList ::RT (fun (ys_r: IList) => nilRT)))) (IList_u ::UT (IList_u ::UT nilUT)))) IList_u (fun (x_73412615: (ArgList IList ::RT (fun (xs_r: IList) => (IList ::RT (fun (ys_r: IList) => nilRT))))) => (fun (v_x_73412615: IList_u) => (ltac: (flattenP (fun (xs_r: IList) => (fun (ys_r: IList) => (fun (v: IList_u) => ((IList_wf v) /\ (exists (llenres: Z), (llen_rel v llenres) /\ (exists (llen_res_2: Z), (llen_rel (⌊ xs_r -⌋) llen_res_2) /\ (exists (llen_res_3: Z), (llen_rel (⌊ ys_r -⌋) llen_res_3) /\ (exists (addZres: Z), (addZ_rel llen_res_2 llen_res_3 addZres) /\ (llenres == addZres))))))))) x_73412615 v_x_73412615))))).
Proof. 
	buildPackG append append_rel append__append_rel append_rel_funct. 
Defined.
Definition get_spec (xs: IList) (i: {i: Z | exists (llenres: Z), (llen_rel (⌊ xs -⌋) llenres) /\ ((0 <= i) /\ (i < llenres))}): Type := 
	{v: Z | ltbZ_rel 5 v true}. 
#[global] Hint Unfold get_spec : lia_unfold.
Definition get (xs: IList) (i: {i: Z | exists (llenres: Z), (llen_rel (⌊ xs -⌋) llenres) /\ ((0 <= i) /\ (i < llenres))}): get_spec xs i. 
Proof. 
	destruct xs as [xs xs_p]. 
	destruct i as [i i_p]. 
	try revert i_p; generalize dependent i; 
	induction xs as [(*Cons*) x xs' IH_xs' | (*Nil*) ]. 
	  - intros . 
		let E := fresh "E" in 
		destruct (i ==? 0) as [ | ] eqn:E; [refine (exist _ x _); 
		solver | refine (subsumptionCast _ _ 
		(IH_xs' (ltac: (try clear IH_xs'; 
	solver)) (i - 1) (ltac: (try clear IH_xs'; 
	solver))) _); 
		solver].  
	  - intros . 
		intros ; 
		exfalso; 
		solver.  
Defined. 
Inductive get_rel : (IList_u -> (Z -> (Z -> Prop))) := 
	 | get_Cons_false: (forall i x xs' , (i <> 0) -> (forall (subZres: Z), (subZ_rel i 1 subZres) -> (forall (getres: Z), (get_rel xs' subZres getres) -> (get_rel (Cons_u x xs') i getres))))
	 | get_Cons_true: (forall i x xs' , (i == 0) -> (get_rel (Cons_u x xs') i x)). 
#[global] Hint Constructors get_rel : core_hint_db.
#[global] Instance get_lookup_rel : dictionary rel get := { 
	lookup' := get_rel
}.
#[global] Instance get_getF : getFunc get_rel := { 
	getF' := get
}.
Theorem get_rel_funct [xs: IList_u] [i: Z]: (forall (v: Z) (v': Z) (H: get_rel xs i v) (K: get_rel xs i v') , v = v'). 
Proof. 
	try revert i_p; generalize dependent i; 
	induction xs as [(*Cons*) x xs' IH_xs' | (*Nil*) ]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve get_rel_funct : f_rel_funct_db.
Theorem get_Cons_false_Cons_true_lem (x: _) (xs': _) (i: _) (getres: Z): (get_rel (Cons_u x xs') i getres) <-> (((i <> 0) /\ (exists (subZres: Z), (subZ_rel i 1 subZres) /\ (get_rel xs' subZres getres))) \/ ((i == 0) /\ (x = getres))). 
Proof. 
	rel_back' ((i ==? 0) _::_ _nil). 
Qed. 
#[global] Hint Rewrite get_Cons_false_Cons_true_lem : f_rel_back.
Theorem get_rel_ex (xs: IList_u) (i: Z) (xs_p: (IList_wf xs) /\ True) (i_p: exists (llenres: Z), (llen_rel xs llenres) /\ ((0 <= i) /\ (i < llenres))): get_rel xs i (⌊ get (exist _ xs xs_p) (exist _ i i_p) -⌋). 
Proof. 
	Opaque get.
	existence_lemma_pre get; 
	try revert i_p; generalize dependent i; 
	induction xs as [(*Cons*) x xs' IH_xs' | (*Nil*) ]; 
	intros ; 
	[let E := fresh "E" in 
	destruct (i ==? 0) as [ | ] eqn:E; [fix_notations; 
	try clear IH_xs' | fix_notations; 
	pose proof (IH_xs' (ltac: (try clear IH_xs'; 
	solver)) (i - 1) (ltac: (try clear IH_xs'; 
	solver))) as IH_33585716; 
	try clear IH_xs']| 
	fix_notations]; 
	simpl in *. 
	Transparent get.
	all: existence_lemma_quicksolve get; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve get_rel_ex : rel_ax_db.
#[global] Opaque get. 
Theorem get__get_rel_rw (xs: IList_u) (i: Z) (xs_p: (IList_wf xs) /\ True) (i_p: exists (llenres: Z), (llen_rel xs llenres) /\ ((0 <= i) /\ (i < llenres))) (v: Z): ((⌊ get (exist _ xs xs_p) (exist _ i i_p) -⌋) = v) <-> (get_rel xs i v). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite get__get_rel_rw : f_rel_funct_db.
#[global] Hint Resolve get__get_rel_rw : rel_ax_db.
#[global] Instance get_lookup_rw : dictionary rwLem get := { 
	lookup' := get__get_rel_rw
}.
Theorem get__get_rel (xs_r: IList) (i_r: {i: Z | exists (llenres: Z), (llen_rel (⌊ xs_r -⌋) llenres) /\ ((0 <= i) /\ (i < llenres))}) (v: Z): ((⌊ get xs_r i_r -⌋) = v) <-> (get_rel (⌊ xs_r -⌋) (⌊ i_r -⌋) v). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite get__get_rel : f_rel_funct_db.
Theorem get__get_rel' (xs: IList_u) (i: Z) (xs_r: IList) (i_r: {i: Z | exists (llenres: Z), (llen_rel (⌊ xs_r -⌋) llenres) /\ ((0 <= i) /\ (i < llenres))}) (v: Z): (xs = (⌊ xs_r -⌋)) -> ((i = (⌊ i_r -⌋)) -> (((⌊ get xs_r i_r -⌋) = v) <-> (get_rel xs i v))). 
Proof. 
	intros -> ->. 
	refine (get__get_rel xs_r i_r v). 
Qed. 
#[global] Hint Resolve get__get_rel' : f_rel_funct_db.
Theorem get_rel_mk [xs: IList_u] [i: Z] (xs_p: (IList_wf xs) /\ True) (i_p: exists (llenres: Z), (llen_rel xs llenres) /\ ((0 <= i) /\ (i < llenres))): {v: _ | get_rel xs i v}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (v: _) => (get_rel xs i v)) (get (exist _ xs xs_p) (exist _ i i_p)) _); 
	rewrite <- get__get_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve get_rel_mk : f_rel_funct_db.
#[global] Instance getPack : (@Pack (IList ::RT (fun (xs_r: IList) => ({i: Z | exists (llenres: Z), (llen_rel (⌊ xs_r -⌋) llenres) /\ ((0 <= i) /\ (i < llenres))} ::RT (fun (i_r: {i: Z | exists (llenres: Z), (llen_rel (⌊ xs_r -⌋) llenres) /\ ((0 <= i) /\ (i < llenres))}) => nilRT)))) (IList_u ::UT (Z ::UT nilUT)) (ltac: (mkProjectsArgListTG (IList ::RT (fun (xs_r: IList) => ({i: Z | exists (llenres: Z), (llen_rel (⌊ xs_r -⌋) llenres) /\ ((0 <= i) /\ (i < llenres))} ::RT (fun (i_r: {i: Z | exists (llenres: Z), (llen_rel (⌊ xs_r -⌋) llenres) /\ ((0 <= i) /\ (i < llenres))}) => nilRT)))) (IList_u ::UT (Z ::UT nilUT)))) Z (fun (x_11925917: (ArgList IList ::RT (fun (xs_r: IList) => ({i: Z | exists (llenres: Z), (llen_rel (⌊ xs_r -⌋) llenres) /\ ((0 <= i) /\ (i < llenres))} ::RT (fun (i_r: {i: Z | exists (llenres: Z), (llen_rel (⌊ xs_r -⌋) llenres) /\ ((0 <= i) /\ (i < llenres))}) => nilRT))))) => (fun (v_x_11925917: Z) => (ltac: (flattenP (fun (xs_r: IList) => (fun (i_r: {i: Z | exists (llenres: Z), (llen_rel (⌊ xs_r -⌋) llenres) /\ ((0 <= i) /\ (i < llenres))}) => (fun (v: Z) => (ltbZ_rel 5 v true)))) x_11925917 v_x_11925917))))).
Proof. 
	buildPackG get get_rel get__get_rel get_rel_funct. 
Defined.
Definition thm1_spec (xs: IList) (x: {x: Z | ltbZ_rel 5 x true}) (i: {i: Z | exists (llenres: Z), (llen_rel (⌊ xs -⌋) llenres) /\ ((0 <= i) /\ (i < llenres))}): Type := 
	{{exists (getres: Z), (get_rel (⌊ xs -⌋) (⌊ i -⌋) getres) /\ (exists (addZres: Z), (addZ_rel (⌊ i -⌋) 1 addZres) /\ (exists (get_res_2: Z), (get_rel (Cons_u (⌊ x -⌋) (⌊ xs -⌋)) addZres get_res_2) /\ (getres == get_res_2)))}}. 
#[global] Hint Unfold thm1_spec : lia_unfold.
Theorem thm1 (xs: IList) (x: {x: Z | ltbZ_rel 5 x true}) (i: {i: Z | exists (llenres: Z), (llen_rel (⌊ xs -⌋) llenres) /\ ((0 <= i) /\ (i < llenres))}): thm1_spec xs x i. 
Proof. 
	destruct xs as [xs xs_p]. 
	destruct x as [x x_p]. 
	destruct i as [i i_p]. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition thm2_spec (xs: IList) (ys: IList) (i: {i: Z | exists (llenres: Z), (llen_rel (⌊ xs -⌋) llenres) /\ ((0 <= i) /\ (i < llenres))}): Type := 
	{{exists (getres: Z), (get_rel (⌊ xs -⌋) (⌊ i -⌋) getres) /\ (exists (llenres: Z), (llen_rel (⌊ ys -⌋) llenres) /\ (exists (addZres: Z), (addZ_rel (⌊ i -⌋) llenres addZres) /\ (exists (appendres: IList_u), (append_rel (⌊ ys -⌋) (⌊ xs -⌋) appendres) /\ (exists (get_res_2: Z), (get_rel appendres addZres get_res_2) /\ (getres == get_res_2)))))}}. 
#[global] Hint Unfold thm2_spec : lia_unfold.
Theorem thm2 (xs: IList) (ys: IList) (i: {i: Z | exists (llenres: Z), (llen_rel (⌊ xs -⌋) llenres) /\ ((0 <= i) /\ (i < llenres))}): thm2_spec xs ys i. 
Proof. 
	destruct xs as [xs xs_p]. 
	destruct ys as [ys ys_p]. 
	destruct i as [i i_p]. 
	try revert i_p; generalize dependent i; try revert xs_p; generalize dependent xs; 
	induction ys as [(*Cons*) y ys IH_ys | (*Nil*) ]. 
	  - intros . 
		pose proof (thm1 
		(subsumptionCast IList_u (fun (xs: IList_u) => ((IList_wf xs) /\ True)) 
		(append 
		(exist (fun (xs: IList_u) => ((IList_wf xs) /\ True)) ys (ltac: (solver))) 
		(exist (fun (ys: IList_u) => ((IList_wf ys) /\ True)) xs (ltac: (solver)))) (ltac: (solver))) 
		(exist (fun (x: Z) => (ltbZ_rel 5 x true)) y (ltac: (solver))) 
		(subsumptionCast Z 
		(fun (i: Z) => (exists (llenres: Z), (llen_rel 
		(⌊ append 
		(exist (fun (xs: IList_u) => ((IList_wf xs) /\ True)) ys (ltac: (solver))) 
		(exist (fun (ys: IList_u) => ((IList_wf ys) /\ True)) xs (ltac: (solver))) -⌋) llenres) /\ ((0 <= i) /\ (i < llenres)))) 
		((exist (fun (x_1: Z) => True) i (ltac: (solver))) +Z (subsumptionCast Z (fun (x_2: Z) => True) 
		(llen 
		(exist (fun (l: IList_u) => ((IList_wf l) /\ True)) ys (ltac: (solver)))) (ltac: (solver)))) (ltac: (solver)))) as H_46661263. 
		simpl in H_46661263. 
		refine (subsumptionCast _ _ 
		(IH_ys (ltac: (try clear IH_ys; 
	solver)) xs (ltac: (try clear IH_ys; 
	solver)) i (ltac: (try clear IH_ys; 
	solver))) _); 
		solver.  
	  - intros . 
		refine (exist _ unit _); 
		solver.  
Qed. 