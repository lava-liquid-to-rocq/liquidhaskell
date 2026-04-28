From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Set Universe Polymorphism.
Definition fvInLambda_spec (x: {x: Z | True}): Type := 
	{VV: Z | True}. 
#[global] Hint Unfold fvInLambda_spec : lia_unfold.
Definition fvInLambda (x: {x: Z | True}): fvInLambda_spec x. 
Proof. 
	destruct x as [x x_p]. 
	assert (f_48681711: (forall (y: {y: Z | True}) , {v: Z | exists (addZres: Z), (addZ_rel x (⌊ y -⌋) addZres) /\ (v == addZres)})) by (intros y; 
	destruct y as [y y_p]; 
	refine (subsumptionCast _ _ 
		((exist (fun (x_1: Z) => True) x (ltac: (solver))) +Z (exist (fun (x_2: Z) => True) y (ltac: (solver)))) _); 
	solver). 
	unshelve refine (let f : ltac:(buildPackG_spec f_48681711) := (ltac:(fun_to_pack f_48681711)) in _). 
	refine (subsumptionCast _ _ 
		(let arg_91127321 := exist (fun (y: Z) => True) x (ltac: (solver)) in ((getPackF f) arg_91127321)) _); 
	solver. 
Defined. 
Definition appId_spec (x: {x: Z | True}): Type := 
	{VV: Z | True}. 
#[global] Hint Unfold appId_spec : lia_unfold.
Definition appId (x: {x: Z | True}): appId_spec x. 
Proof. 
	destruct x as [x x_p]. 
	assert (f_73066757: (forall (y: {y: Z | True}) , {v: Z | v = (⌊ y -⌋)})) by (intros y; 
	destruct y as [y y_p]; 
	refine (exist _ y _); 
	solver). 
	unshelve refine (let f : ltac:(buildPackG_spec f_73066757) := (ltac:(fun_to_pack f_73066757)) in _). 
	refine (subsumptionCast _ _ 
		(let arg_91127321 := exist (fun (y: Z) => True) x (ltac: (solver)) in ((getPackF f) arg_91127321)) _); 
	solver. 
Defined. 