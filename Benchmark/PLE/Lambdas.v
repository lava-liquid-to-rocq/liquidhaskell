From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Set Universe Polymorphism.
From Coq Require Import Unicode.Utf8.

Definition fvInLambda_spec (x : {x: Z | True}): Type :=
  {VV: Z | True}.

#[global] Hint Unfold fvInLambda_spec: lia_unfold.

Definition fvInLambda (x : {x: Z | True}): fvInLambda_spec x.
Proof.
  destruct x as [x x_p].
  assert (f_14072909 : ∀ (y : {VV: Z | True}),
                       {v: Z | ∃ (addZ_res : Z), addZ_rel x ⌊ y -⌋ addZ_res ∧ v == addZ_res}).
  { intros [y y_p];
    refine (subsumptionCast
            Z
            (λ (v : Z), ∃ (addZ_res : Z), addZ_rel x y addZ_res ∧ v == addZ_res)
            (# x +Z # y)
            ltac:(solver)). }
  unshelve refine (let f: ltac:(buildPackG_spec f_14072909) :=
                 ltac:(fun_to_pack f_14072909) in
                 _).
  refine (subsumptionCast Z (λ (VV : Z), True) (getPackF f (# x)) ltac:(solver)).
Defined.

Definition appId_spec (x : {x: Z | True}): Type :=
  {VV: Z | True}.

#[global] Hint Unfold appId_spec: lia_unfold.

Definition appId (x : {x: Z | True}): appId_spec x.
Proof.
  destruct x as [x x_p].
  assert (f_87506985 : ∀ (y : {VV: Z | True}), {v: Z | v == ⌊ y -⌋}).
  { intros [y y_p]; refine (subsumptionCast Z (λ (v : Z), v == y) (# y) ltac:(solver)). }
  unshelve refine (let f: ltac:(buildPackG_spec f_87506985) :=
                 ltac:(fun_to_pack f_87506985) in
                 _).
  refine (subsumptionCast Z (λ (VV : Z), True) (getPackF f (# x)) ltac:(solver)).
Defined.
