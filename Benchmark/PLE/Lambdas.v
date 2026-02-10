From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Definition fvInLambda (x: {x: Z | True}): {VV: Z | True}. 
Proof. 
	destruct x as [x x_p]. 
	assert (f_84163371: (forall (y: {y: Z | True}) , {v: Z | forall (addZres: Z), (addZ_rel x (⌊ y -⌋) addZres) -> (v == addZres)})) by (intros y; 
	destruct y as [y y_p]; 
	refine (subsumptionCast _ _ 
		((exist (fun (x_1: Z) => True) x (ltac: (solver))) +Z (exist (fun (x_2: Z) => True) y (ltac: (solver)))) _); 
	solver). 
	unshelve refine (let f : ltac:(buildPackG_spec f_84163371) := (ltac:(fun_to_pack f_84163371)) in _). 
	refine (subsumptionCast _ _ 
		((getPackF f) (exist (fun (y: Z) => True) x (ltac: (solver)))) _); 
	solver. 
Defined. 
Definition appId (x: {x: Z | True}): {VV: Z | True}. 
Proof. 
	destruct x as [x x_p]. 
	assert (f_73066757: (forall (y: {y: Z | True}) , {v: Z | v = (⌊ y -⌋)})) by (intros y; 
	destruct y as [y y_p]; 
	refine (exist _ y _); 
	solver). 
	unshelve refine (let f : ltac:(buildPackG_spec f_73066757) := (ltac:(fun_to_pack f_73066757)) in _). 
	refine (subsumptionCast _ _ 
		((getPackF f) (exist (fun (y: Z) => True) x (ltac: (solver)))) _); 
	solver. 
Defined. 