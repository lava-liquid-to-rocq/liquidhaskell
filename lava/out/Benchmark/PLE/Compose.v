From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Set Universe Polymorphism.
Definition prop2_spec (f: (@Pack ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_86410777: (ArgList {lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => nilRT))) => (fun (v_x_86410777: Z) => (ltac: (flattenP (fun (lq_tmp0: {lq_tmp0: Z | True}) => (fun (VV: Z) => True)) x_86410777 v_x_86410777)))))) (g: (@Pack ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_61572807: (ArgList {lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT))) => (fun (v_x_61572807: Z) => (ltac: (flattenP (fun (lq_tmp2: {lq_tmp2: Z | True}) => (fun (VV: Z) => True)) x_61572807 v_x_61572807)))))) (x: {x: Z | True}): Type := 
	{{True}}. 
#[global] Hint Unfold prop2_spec : lia_unfold.
Theorem prop2 (f: (@Pack ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_86410777: (ArgList {lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => nilRT))) => (fun (v_x_86410777: Z) => (ltac: (flattenP (fun (lq_tmp0: {lq_tmp0: Z | True}) => (fun (VV: Z) => True)) x_86410777 v_x_86410777)))))) (g: (@Pack ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_61572807: (ArgList {lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT))) => (fun (v_x_61572807: Z) => (ltac: (flattenP (fun (lq_tmp2: {lq_tmp2: Z | True}) => (fun (VV: Z) => True)) x_61572807 v_x_61572807)))))) (x: {x: Z | True}): prop2_spec f g x. 
Proof. 
	destruct x as [x x_p]. 
	refine (exist _ unit _); 
	solver. 
Qed. 
Definition compose_spec (lq_tmp0: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_39721497: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))) => (fun (v_x_39721497: Z) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True)) x_39721497 v_x_39721497)))))) (lq_tmp3: (@Pack ({lq_tmp4: Z | True} ::RT (fun (lq_tmp4: {lq_tmp4: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp4: Z | True} ::RT (fun (lq_tmp4: {lq_tmp4: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_26591512: (ArgList {lq_tmp4: Z | True} ::RT (fun (lq_tmp4: {lq_tmp4: Z | True}) => nilRT))) => (fun (v_x_26591512: Z) => (ltac: (flattenP (fun (lq_tmp4: {lq_tmp4: Z | True}) => (fun (VV: Z) => True)) x_26591512 v_x_26591512)))))) (lq_tmp6: {lq_tmp6: Z | True}): Type := 
	{VV: Z | True}. 
#[global] Hint Unfold compose_spec : lia_unfold.
Definition compose (lq_tmp0: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_39721497: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))) => (fun (v_x_39721497: Z) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True)) x_39721497 v_x_39721497)))))) (lq_tmp3: (@Pack ({lq_tmp4: Z | True} ::RT (fun (lq_tmp4: {lq_tmp4: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp4: Z | True} ::RT (fun (lq_tmp4: {lq_tmp4: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_26591512: (ArgList {lq_tmp4: Z | True} ::RT (fun (lq_tmp4: {lq_tmp4: Z | True}) => nilRT))) => (fun (v_x_26591512: Z) => (ltac: (flattenP (fun (lq_tmp4: {lq_tmp4: Z | True}) => (fun (VV: Z) => True)) x_26591512 v_x_26591512)))))) (lq_tmp6: {lq_tmp6: Z | True}): compose_spec lq_tmp0 lq_tmp3 lq_tmp6. 
Proof. 
	destruct lq_tmp6 as [lq_tmp6 lq_tmp6_p]. 
	refine (subsumptionCast _ _ 
		((getPackF lq_tmp0) 
		(subsumptionCast Z (fun (lq_tmp1: Z) => True) 
		((getPackF lq_tmp3) (exist (fun (lq_tmp4: Z) => True) lq_tmp6 (ltac: (solver)))) (ltac: (solver)))) _); 
	solver. 
Defined. 
Inductive compose_rel : ((@uPack (Z ::UT nilUT) Z) -> ((@uPack (Z ::UT nilUT) Z) -> (Z -> (Z -> Prop)))) := 
	 | compose_def: (forall (lq_tmp0: @uPack (Z ::UT nilUT) Z) (lq_tmp3: @uPack (Z ::UT nilUT) Z) lq_tmp6 , forall (lq_tmp3res: _), ((getUPackRel lq_tmp3) lq_tmp6 lq_tmp3res) -> (forall (lq_tmp0res: _), ((getUPackRel lq_tmp0) lq_tmp3res lq_tmp0res) -> (compose_rel lq_tmp0 lq_tmp3 lq_tmp6 lq_tmp0res))). 
#[global] Hint Constructors compose_rel : core_hint_db.
#[global] Instance compose_lookup_rel : dictionary rel compose := { 
	lookup' := compose_rel
}.
#[global] Instance compose_getF : getFunc compose_rel := { 
	getF' := compose
}.
Theorem compose_rel_funct [lq_tmp0: @uPack (Z ::UT nilUT) Z] [lq_tmp3: @uPack (Z ::UT nilUT) Z] [lq_tmp6: Z]: (forall (VV: Z) (VV': Z) (H: compose_rel lq_tmp0 lq_tmp3 lq_tmp6 VV) (K: compose_rel lq_tmp0 lq_tmp3 lq_tmp6 VV') , VV = VV'). 
Proof. 
	rel_functionhood_body. 
Qed. 
#[global] Hint Resolve compose_rel_funct : f_rel_funct_db.
Theorem compose_def_lem (lq_tmp0: @uPack (Z ::UT nilUT) Z) (lq_tmp3: @uPack (Z ::UT nilUT) Z) (lq_tmp6: _) (lq_tmp0res: _): (compose_rel lq_tmp0 lq_tmp3 lq_tmp6 lq_tmp0res) <-> (exists (lq_tmp3res: _), ((getUPackRel lq_tmp3) lq_tmp6 lq_tmp3res) /\ ((getUPackRel lq_tmp0) lq_tmp3res lq_tmp0res)). 
Proof. 
	rel_back' ( _nil). 
Qed. 
#[global] Hint Rewrite compose_def_lem : f_rel_back.
Theorem compose_rel_ex (lq_tmp0: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_39721497: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))) => (fun (v_x_39721497: Z) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True)) x_39721497 v_x_39721497)))))) (lq_tmp3: (@Pack ({lq_tmp4: Z | True} ::RT (fun (lq_tmp4: {lq_tmp4: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp4: Z | True} ::RT (fun (lq_tmp4: {lq_tmp4: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_26591512: (ArgList {lq_tmp4: Z | True} ::RT (fun (lq_tmp4: {lq_tmp4: Z | True}) => nilRT))) => (fun (v_x_26591512: Z) => (ltac: (flattenP (fun (lq_tmp4: {lq_tmp4: Z | True}) => (fun (VV: Z) => True)) x_26591512 v_x_26591512)))))) (lq_tmp6: Z) (lq_tmp6_p: True): compose_rel (packProj lq_tmp0) (packProj lq_tmp3) lq_tmp6 (⌊ compose lq_tmp0 lq_tmp3 (exist _ lq_tmp6 lq_tmp6_p) -⌋). 
Proof. 
	Opaque compose.
	existence_lemma_pre compose; 
	fix_notations; 
	simpl in *. 
	Transparent compose.
	all: existence_lemma_quicksolve compose; 
	f__f_rel_ex_body; 
	f_rel_finish. 
Qed. 
#[global] Hint Resolve compose_rel_ex : rel_ax_db.
#[global] Opaque compose. 
Theorem compose__compose_rel_rw (lq_tmp0: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_39721497: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))) => (fun (v_x_39721497: Z) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True)) x_39721497 v_x_39721497)))))) (lq_tmp3: (@Pack ({lq_tmp4: Z | True} ::RT (fun (lq_tmp4: {lq_tmp4: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp4: Z | True} ::RT (fun (lq_tmp4: {lq_tmp4: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_26591512: (ArgList {lq_tmp4: Z | True} ::RT (fun (lq_tmp4: {lq_tmp4: Z | True}) => nilRT))) => (fun (v_x_26591512: Z) => (ltac: (flattenP (fun (lq_tmp4: {lq_tmp4: Z | True}) => (fun (VV: Z) => True)) x_26591512 v_x_26591512)))))) (lq_tmp6: Z) (lq_tmp6_p: True) (VV: Z): ((⌊ compose lq_tmp0 lq_tmp3 (exist _ lq_tmp6 lq_tmp6_p) -⌋) = VV) <-> (compose_rel (packProj lq_tmp0) (packProj lq_tmp3) lq_tmp6 VV). 
Proof. 
	f__f_rel_rw. 
Qed. 
#[global] Hint Rewrite compose__compose_rel_rw : f_rel_funct_db.
#[global] Hint Resolve compose__compose_rel_rw : rel_ax_db.
#[global] Instance compose_lookup_rw : dictionary rwLem compose := { 
	lookup' := compose__compose_rel_rw
}.
Theorem compose__compose_rel (lq_tmp0_r: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_39721497: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))) => (fun (v_x_39721497: Z) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True)) x_39721497 v_x_39721497)))))) (lq_tmp3_r: (@Pack ({lq_tmp4: Z | True} ::RT (fun (lq_tmp4: {lq_tmp4: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp4: Z | True} ::RT (fun (lq_tmp4: {lq_tmp4: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_26591512: (ArgList {lq_tmp4: Z | True} ::RT (fun (lq_tmp4: {lq_tmp4: Z | True}) => nilRT))) => (fun (v_x_26591512: Z) => (ltac: (flattenP (fun (lq_tmp4: {lq_tmp4: Z | True}) => (fun (VV: Z) => True)) x_26591512 v_x_26591512)))))) (lq_tmp6_r: {lq_tmp6: Z | True}) (VV: Z): ((⌊ compose lq_tmp0_r lq_tmp3_r lq_tmp6_r -⌋) = VV) <-> (compose_rel (packProj lq_tmp0_r) (packProj lq_tmp3_r) (⌊ lq_tmp6_r -⌋) VV). 
Proof. 
	f__f_rel. 
Qed. 
#[global] Hint Rewrite compose__compose_rel : f_rel_funct_db.
Theorem compose__compose_rel' (lq_tmp0: @uPack (Z ::UT nilUT) Z) (lq_tmp3: @uPack (Z ::UT nilUT) Z) (lq_tmp6: Z) (lq_tmp0_r: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_39721497: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))) => (fun (v_x_39721497: Z) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True)) x_39721497 v_x_39721497)))))) (lq_tmp3_r: (@Pack ({lq_tmp4: Z | True} ::RT (fun (lq_tmp4: {lq_tmp4: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp4: Z | True} ::RT (fun (lq_tmp4: {lq_tmp4: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_26591512: (ArgList {lq_tmp4: Z | True} ::RT (fun (lq_tmp4: {lq_tmp4: Z | True}) => nilRT))) => (fun (v_x_26591512: Z) => (ltac: (flattenP (fun (lq_tmp4: {lq_tmp4: Z | True}) => (fun (VV: Z) => True)) x_26591512 v_x_26591512)))))) (lq_tmp6_r: {lq_tmp6: Z | True}) (VV: Z): (lq_tmp0 = (packProj lq_tmp0_r)) -> ((lq_tmp3 = (packProj lq_tmp3_r)) -> ((lq_tmp6 = (⌊ lq_tmp6_r -⌋)) -> (((⌊ compose lq_tmp0_r lq_tmp3_r lq_tmp6_r -⌋) = VV) <-> (compose_rel lq_tmp0 lq_tmp3 lq_tmp6 VV)))). 
Proof. 
	intros -> -> ->. 
	refine (compose__compose_rel lq_tmp0_r lq_tmp3_r lq_tmp6_r VV). 
Qed. 
#[global] Hint Resolve compose__compose_rel' : f_rel_funct_db.
Theorem compose_rel_mk [lq_tmp0: (@Pack ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_39721497: (ArgList {lq_tmp1: Z | True} ::RT (fun (lq_tmp1: {lq_tmp1: Z | True}) => nilRT))) => (fun (v_x_39721497: Z) => (ltac: (flattenP (fun (lq_tmp1: {lq_tmp1: Z | True}) => (fun (VV: Z) => True)) x_39721497 v_x_39721497)))))] [lq_tmp3: (@Pack ({lq_tmp4: Z | True} ::RT (fun (lq_tmp4: {lq_tmp4: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp4: Z | True} ::RT (fun (lq_tmp4: {lq_tmp4: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_26591512: (ArgList {lq_tmp4: Z | True} ::RT (fun (lq_tmp4: {lq_tmp4: Z | True}) => nilRT))) => (fun (v_x_26591512: Z) => (ltac: (flattenP (fun (lq_tmp4: {lq_tmp4: Z | True}) => (fun (VV: Z) => True)) x_26591512 v_x_26591512)))))] [lq_tmp6: Z] (lq_tmp6_p: True): {VV: _ | compose_rel (packProj lq_tmp0) (packProj lq_tmp3) lq_tmp6 VV}. 
Proof. 
	intros ; 
	refine (subsumptionCast _ 
		(fun (VV: _) => (compose_rel (packProj lq_tmp0) (packProj lq_tmp3) lq_tmp6 VV)) (compose lq_tmp0 lq_tmp3 (exist _ lq_tmp6 lq_tmp6_p)) _); 
	rewrite <- compose__compose_rel'; 
	quicksolve. 
Qed. 
#[global] Hint Resolve compose_rel_mk : f_rel_funct_db.
Definition prop1_spec (f: (@Pack ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_86410777: (ArgList {lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => nilRT))) => (fun (v_x_86410777: Z) => (ltac: (flattenP (fun (lq_tmp0: {lq_tmp0: Z | True}) => (fun (VV: Z) => True)) x_86410777 v_x_86410777)))))) (g: (@Pack ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_61572807: (ArgList {lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT))) => (fun (v_x_61572807: Z) => (ltac: (flattenP (fun (lq_tmp2: {lq_tmp2: Z | True}) => (fun (VV: Z) => True)) x_61572807 v_x_61572807)))))) (x: {x: Z | True}): Type := 
	{{forall (gres: _), ((getPackRel g) (⌊ x -⌋) gres) -> (forall (fres: _), ((getPackRel f) gres fres) -> (forall (composeres: Z), (compose_rel (packProj f) (packProj g) (⌊ x -⌋) composeres) -> (fres == composeres)))}}. 
#[global] Hint Unfold prop1_spec : lia_unfold.
Theorem prop1 (f: (@Pack ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_86410777: (ArgList {lq_tmp0: Z | True} ::RT (fun (lq_tmp0: {lq_tmp0: Z | True}) => nilRT))) => (fun (v_x_86410777: Z) => (ltac: (flattenP (fun (lq_tmp0: {lq_tmp0: Z | True}) => (fun (VV: Z) => True)) x_86410777 v_x_86410777)))))) (g: (@Pack ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT) (ltac: (mkProjectsArgListTG ({lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT)) (Z ::UT nilUT))) Z (fun (x_61572807: (ArgList {lq_tmp2: Z | True} ::RT (fun (lq_tmp2: {lq_tmp2: Z | True}) => nilRT))) => (fun (v_x_61572807: Z) => (ltac: (flattenP (fun (lq_tmp2: {lq_tmp2: Z | True}) => (fun (VV: Z) => True)) x_61572807 v_x_61572807)))))) (x: {x: Z | True}): prop1_spec f g x. 
Proof. 
	destruct x as [x x_p]. 
	refine (exist _ unit _); 
	solver. 
Qed. 