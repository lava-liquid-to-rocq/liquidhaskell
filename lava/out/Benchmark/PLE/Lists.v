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
Definition append_spec (lq_tmp0: L) (lq_tmp1: L): Type := 
	L. 
#[global] Hint Unfold append_spec : lia_unfold.
Definition append (lq_tmp0: L) (lq_tmp1: L): append_spec lq_tmp0 lq_tmp1. 
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
Definition propConst1_spec (lq_tmp0: {{True}}): Type := 
	{{exists (appendres: L_u), (append_rel (C_u 1 Emp_u) Emp_u appendres) /\ (exists (append_res_2: L_u), (append_rel appendres Emp_u append_res_2) /\ (append_res_2 == (C_u 1 Emp_u)))}}. 
#[global] Hint Unfold propConst1_spec : lia_unfold.
Theorem propConst1 (lq_tmp0: {{True}}): propConst1_spec lq_tmp0. 
Proof. 
	destruct lq_tmp0 as [lq_tmp0 lq_tmp0_p]. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition propConst2_spec (lq_tmp0: {{True}}): Type := 
	{{exists (appendres: L_u), (append_rel (C_u 1 (C_u 2 Emp_u)) Emp_u appendres) /\ (exists (append_res_2: L_u), (append_rel appendres Emp_u append_res_2) /\ (append_res_2 == (C_u 1 (C_u 2 Emp_u))))}}. 
#[global] Hint Unfold propConst2_spec : lia_unfold.
Theorem propConst2 (lq_tmp0: {{True}}): propConst2_spec lq_tmp0. 
Proof. 
	destruct lq_tmp0 as [lq_tmp0 lq_tmp0_p]. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition propConst3_spec (lq_tmp0: {{True}}): Type := 
	{{exists (appendres: L_u), (append_rel (C_u 1 (C_u 2 (C_u 3 Emp_u))) Emp_u appendres) /\ (exists (append_res_2: L_u), (append_rel appendres Emp_u append_res_2) /\ (append_res_2 == (C_u 1 (C_u 2 (C_u 3 Emp_u)))))}}. 
#[global] Hint Unfold propConst3_spec : lia_unfold.
Theorem propConst3 (lq_tmp0: {{True}}): propConst3_spec lq_tmp0. 
Proof. 
	destruct lq_tmp0 as [lq_tmp0 lq_tmp0_p]. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition length_spec (lq_tmp0: L): Type := 
	{VV: Z | gebZ_rel VV 0 true}. 
#[global] Hint Unfold length_spec : lia_unfold.
Definition length (lq_tmp0: L): length_spec lq_tmp0. 
Proof. 
	destruct lq_tmp0 as [lq_tmp0 lq_tmp0_p]. 
	induction lq_tmp0 as [(*C*) ds_d3vT xs IH_xs | (*Emp*) ]. 
	  - intros . 
		refine (subsumptionCast _ _ 
		((exist (fun (x_1: Z) => True) 1 (ltac: (solver))) +Z (subsumptionCast Z (fun (x_2: Z) => True) (IH_xs (ltac: (try clear IH_xs; 
	solver))) (ltac: (solver)))) _); 
		solver.  
	  - intros . 
		refine (exist _ 0 _); 
		solver.  
Defined. 
Inductive length_rel : (L_u -> (Z -> Prop)) := 
	 | length_Emp: length_rel Emp_u 0
	 | length_C: (forall ds_d3vT xs , forall (lengthres: Z), (length_rel xs lengthres) -> (forall (addZres: Z), (addZ_rel 1 lengthres addZres) -> (length_rel (C_u ds_d3vT xs) addZres))). 
#[global] Hint Constructors length_rel : core_hint_db.
#[global] Instance length_lookup_rel : dictionary rel length := { 
	lookup' := length_rel
}.
#[global] Instance length_getF : getFunc length_rel := { 
	getF' := length
}.
Theorem length_rel_funct [lq_tmp0: L_u]: (forall (VV: Z) (VV': Z) (H: length_rel lq_tmp0 VV) (K: length_rel lq_tmp0 VV') , VV = VV'). 
Proof. 
	induction lq_tmp0 as [(*C*) ds_d3vT xs IH_xs | (*Emp*) ]; 
	intros ; 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve length_rel_funct : f_rel_funct_db.
Theorem length_Emp_lem (res: Z): (length_rel Emp_u res) <-> (res = 0). 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite length_Emp_lem : f_rel_back.
Theorem length_C_lem (ds_d3vT: _) (xs: _) (addZres: Z): (length_rel (C_u ds_d3vT xs) addZres) <-> (exists (lengthres: Z), (length_rel xs lengthres) /\ (addZ_rel 1 lengthres addZres)). 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite length_C_lem : f_rel_back.
Theorem length_rel_ex (lq_tmp0: L_u) (lq_tmp0_p: (L_wf lq_tmp0) /\ True): length_rel lq_tmp0 (⌊ length (exist _ lq_tmp0 lq_tmp0_p) -⌋). 
Proof. 
	Opaque length.
	existence_lemma_pre length; 
	induction lq_tmp0 as [(*C*) ds_d3vT xs IH_xs | (*Emp*) ]; 
	intros ; 
	[fix_notations; 
	pose proof (IH_xs (ltac: (try clear IH_xs; 
	solver))) as IH_55394889; 
	try clear IH_xs| 
	fix_notations]; 
	simpl in *. 
	Transparent length.
	all: existence_lemma_quicksolve length; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve length_rel_ex : rel_ax_db.
#[global] Opaque length. 
Theorem length__length_rel_rw (lq_tmp0: L_u) (lq_tmp0_p: (L_wf lq_tmp0) /\ True) (VV: Z): ((⌊ length (exist _ lq_tmp0 lq_tmp0_p) -⌋) = VV) <-> (length_rel lq_tmp0 VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite length__length_rel_rw : f_rel_funct_db.
#[global] Hint Resolve length__length_rel_rw : rel_ax_db.
#[global] Instance length_lookup_rw : dictionary rwLem length := { 
	lookup' := length__length_rel_rw
}.
Theorem length__length_rel (lq_tmp0_r: L) (VV: Z): ((⌊ length lq_tmp0_r -⌋) = VV) <-> (length_rel (⌊ lq_tmp0_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite length__length_rel : f_rel_funct_db.
Theorem length__length_rel' (lq_tmp0: L_u) (lq_tmp0_r: L) (VV: Z): (lq_tmp0 = (⌊ lq_tmp0_r -⌋)) -> (((⌊ length lq_tmp0_r -⌋) = VV) <-> (length_rel lq_tmp0 VV)). 
Proof. 
	intros ->. 
	refine (length__length_rel lq_tmp0_r VV). 
Qed. 
#[global] Hint Resolve length__length_rel' : f_rel_funct_db.
Theorem length_rel_mk [lq_tmp0: L_u] (lq_tmp0_p: (L_wf lq_tmp0) /\ True): {VV: _ | length_rel lq_tmp0 VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ (fun (VV: _) => (length_rel lq_tmp0 VV)) (length (exist _ lq_tmp0 lq_tmp0_p)) _); 
	rewrite <- length__length_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve length_rel_mk : f_rel_funct_db.
#[global] Instance lengthPack : (@Pack (L ::RT (fun (lq_tmp0_r: L) => nilRT)) (L_u ::UT nilUT) (ltac: (mkProjectsArgListTG (L ::RT (fun (lq_tmp0_r: L) => nilRT)) (L_u ::UT nilUT))) Z (fun (x_15721783: (ArgList L ::RT (fun (lq_tmp0_r: L) => nilRT))) => (fun (v_x_15721783: Z) => (ltac: (flattenP (fun (lq_tmp0_r: L) => (fun (VV: Z) => (gebZ_rel VV 0 true))) x_15721783 v_x_15721783))))).
Proof. 
	buildPackG length length_rel length__length_rel length_rel_funct. 
Defined.
Definition prop_spec (x: {x: Z | True}) (xs: L) (ys: L) (zs: L): Type := 
	{{exists (appendres: L_u), (append_rel (C_u (⌊ x -⌋) (⌊ xs -⌋)) (⌊ ys -⌋) appendres) /\ (exists (append_res_2: L_u), (append_rel appendres (⌊ zs -⌋) append_res_2) /\ (exists (append_res_3: L_u), (append_rel (⌊ xs -⌋) (⌊ ys -⌋) append_res_3) /\ (exists (append_res_4: L_u), (append_rel append_res_3 (⌊ zs -⌋) append_res_4) /\ (append_res_2 == (C_u (⌊ x -⌋) append_res_4)))))}}. 
#[global] Hint Unfold prop_spec : lia_unfold.
Theorem prop (x: {x: Z | True}) (xs: L) (ys: L) (zs: L): prop_spec x xs ys zs. 
Proof. 
	destruct x as [x x_p]. 
	destruct xs as [xs xs_p]. 
	destruct ys as [ys ys_p]. 
	destruct zs as [zs zs_p]. 
	refine (exist _ unit _).
  time cleanup. 
  (* assert (L_wf appendres) as H.
  { recreate_var (append_rel xs ys) bla. 
    unify_vars. quicksolve.
. } *)
  (*match goal with
  | |- exists (w:_), ?relAp w => isRelAppl relAp;
    let v := fresh "v_" in 
    recreate_var relAp v;
    exists v; try assumption
  end.*)
  let pred := fresh "pred" in
  get_dom_ref append pred.
  assert (C_u x appendres = C_u x appendres) as vRefl by reflexivity.
  (* assert_wit  (C_u x appendres) pred wit_name.*)

  get_f_ts (append_rel (C_u x appendres) zs) f_ts.
  pose append as fApp.
  pose (C_u x appendres _::_ zs _::_ _nil) as tl.


  (* starting first loop *)
  pose fApp as fApp'; subst fApp;
  let dom_ref := fresh "t_dom_ref" in
  get_dom_ref fApp' dom_ref;

  (* 
  assert_wit (C_u x appendres) dom_ref arg_wit_name. *)
  first [
    assert_wit (C_u x appendres) dom_ref arg_wit_name
  | pose (dom_ref (C_u x appendres)) as bla;
    assRefl bla as blaRefl; 
    unfold dom_ref in blaRefl; simpl in blaRefl; 
    match type of blaRefl with
    | ?tp = _ => clear blaRefl; idtac tp;
      match tp with
      | (?wf ?x /\ ?p) /\ ?q => 
        first [
          assert_wit x (fun x => wf x /\ p /\ q) arg_wit_name
        | match goal with
          | [h: ?relAp x |- _] => 
            isRelAppl relAp; 
            idtac x h;

            (* fetch f and the values ts to which f_rel is applied in f_rel_ap *)
            let g_ts := fresh "g_ts" in
            get_f_ts relAp g_ts; 
            let tempEq := fresh "tempEq" in
            assRefl g_ts as tempEq;
            let g := fresh "g" in
            match type of tempEq with
            | (?g, ?ts) = _ => clear tempEq; idtac g;
              let gdomRef := fresh "gdomRef" in
              let x_wit := fresh "x_wit_" in
              get_dom_ref g gdomRef;
              idtac "ha";
              assert_wit x gdomRef x_wit;
              try assert tp as arg_wit_name by (split_hyps; unify_vars; quicksolve)
            end
          end
        ]
      end
    end
  ].

  unfold append_spec in *.
  pose proof (eq_refl ⌊ bla -⌋) as blaRefl; 
  unfold bla in blaRefl;
  match type of blaRefl with
  | ?tm = _ => clear blaRefl; idtac tm;
    axProjTm tm
  end.
  axProjTm bla.
  try assert tp as arg_wit_name by (split_hyps; unify_vars; quicksolve)
  (
    assRefl tl as tlEq; 
    match type of tlEq with
    | _nil = _ => fail
    | ?t _::_ ?tail = _ => idtac "running main loop in assert_wit with tail " t " _::_ " tail; 
      pose fApp as fApp'; subst fApp;
      
      let dom_ref := fresh "t_dom_ref" in
      get_dom_ref fApp' dom_ref;
      let arg_wit_name := fresh "arg_wit_name_" in

      assert_wit t dom_ref arg_wit_name;
      let arg_wit_tp := type of arg_wit_name in
      idtac "recursive call created witness " arg_wit_name " : " arg_wit_tp ". "; 
      pose (fApp' (exist _ t arg_wit_name)) as fApp;
      try subst arg_wit_name; subst fApp'; simpl_proj;
      pose tail as tl
    end; clear tlEq
  ).
  repeat (
    assRefl tl as tlEq; 
    match type of tlEq with
    | _nil = _ => fail
    | ?t _::_ ?tail = _ => idtac "running main loop in assert_wit with tail " t " _::_ " tail; 
      pose fApp as fApp'; subst fApp;
      
      let dom_ref := fresh "t_dom_ref" in
      get_dom_ref fApp' dom_ref;
      let arg_wit_name := fresh "arg_wit_name_" in

      assert_wit t dom_ref arg_wit_name;
      let arg_wit_tp := type of arg_wit_name in
      idtac "recursive call created witness " arg_wit_name " : " arg_wit_tp ". "; 
      pose (fApp' (exist _ t arg_wit_name)) as fApp;
      try subst arg_wit_name; subst fApp'; simpl_proj;
      pose tail as tl
    end; clear tlEq
  ).

  match type of vRefl with
  | ?v = _ => clear vRefl;
  match goal with
  | [h: ?f_rel_ap v |- _] => 
    isRelAppl f_rel_ap; (* idtac "case in assert_wit for unrefined variable axiomatized using the following application of a graph relation: " f_rel_ap; *)

    (* fetch f and the values ts to which f_rel is applied in f_rel_ap *)
    let f_ts := fresh "f_ts" in
    get_f_ts f_rel_ap f_ts; 
    
    let tempEq := fresh "tempEq" in
    assRefl f_ts as tempEq;
    match type of tempEq with
    | (?f, ?ts) = _ => clear tempEq;
      let fApp := fresh "fApp" in
      let fApp' := fresh "fApp'" in
      let tl := fresh "tsTail" in
      let tlEq := fresh "tsTailEq" in
      pose f as fApp;
      pose ts as tl;
      (* recursively assert the refinements of the ts and apply f to them *)
      repeat (
        assRefl tl as tlEq; 
        match type of tlEq with
        | _nil = _ => fail
        | ?t _::_ ?tail = _ => idtac "running main loop in assert_wit with tail " t " _::_ " tail; 
          pose fApp as fApp'; subst fApp;
          
          let dom_ref := fresh "t_dom_ref" in
          get_dom_ref fApp' dom_ref;
          let arg_wit_name := fresh "arg_wit_name_" in

          assert_wit t dom_ref arg_wit_name;
          let arg_wit_tp := type of arg_wit_name in
          idtac "recursive call created witness " arg_wit_name " : " arg_wit_tp ". "; 
          pose (fApp' (exist _ t arg_wit_name)) as fApp;
          try subst arg_wit_name; subst fApp'; simpl_proj;
          pose tail as tl
        end; clear tlEq
      ); (* idtac "finish main loop"; *) clear tl;
      (* we now have a fully applied version of f in fApp, we destruct it to get the refinement witness for it *)
      let appl_wit := fresh "appl_wit_" in
      assert _ as appl_wit by (exact ⌈ fApp ⌉); subst fApp; simpl_proj; 
      
      let fApplTp := type of appl_wit in
      try axProjTm fApplTp;
      (* tryif destruct fApp as [_ appl_wit] then idtac else idtac "failed to extract the refinement witness from " fApp; *)
      assert (pred v) as wit_name by (unfold pred; simpl; try 
        first [clear pred | subst pred]; first [exact appl_wit; clear appl_wit | quick_wff_wit | quick_simpl; unify_vars; try (specialize_hyps; try unify_vars); try quicksolve; (*print_proof_state;*) timeout 10 (unshelve eauto 50 with solver_db)])
    end
    end; subst pred; simpl in wit_name
  end.






	solver. 
Qed. 