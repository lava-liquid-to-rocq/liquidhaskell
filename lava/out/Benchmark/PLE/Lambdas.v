From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
From Coq Require Import Unicode.Utf8.
Ltac solver := quicksolve.

Definition fvInLambda (x : {x: Z | True}): {VV: Z | True}.
Proof.
  destruct x as [x x_p].
  assert (f_15080524 : ∀ (y : {VV: Z | True}),
                       {v: Z | ∀ addZ_res, addZ_rel x ⌊ y ⌋ addZ_res → v == addZ_res}).
  { intros [y y_p];
    refine (subsumptionCast
            Z
            (λ (v : Z), ∀ addZ_res, addZ_rel x ⌊ y ⌋ addZ_res → v == addZ_res)
            (# x +Z # y)
            ltac:(solver)). }
  unshelve refine (let f : ltac:(buildPackG_spec f_15080524) := (ltac:(fun_to_pack f_15080524)) in _).
  refine (subsumptionCast Z (λ (VV : Z), True) (getPackF f (# x)) ltac:(solver)).
Defined.

Definition appId (x : {x: Z | True}): {VV: Z | True}.
Proof.
  destruct x as [x x_p].
  assert (f_70768816 : ∀ (y : {VV: Z | True}), {v: Z | v == ⌊ y ⌋}).
  { intros [y y_p]; refine (subsumptionCast Z (λ (v : Z), v == ⌊ y ⌋) (# y) ltac:(solver)). }
  unshelve refine (let f : ltac:(buildPackG_spec f_70768816) := (ltac:(fun_to_pack f_70768816)) in _).
  refine (subsumptionCast Z (λ (VV : Z), True) (getPackF f (# x)) ltac:(solver)).
Defined.
