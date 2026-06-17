From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Set Universe Polymorphism.
From Coq Require Import Unicode.Utf8.

Load Benchmark.SoftwareFoundationsBasics.

Definition plus_n_Sm_spec (ds_d9bM m : MyNat): Type :=
  {{∃ (plus_res : MyNat_u),
    plus_rel ⌊ ds_d9bM -⌋ ⌊ m -⌋ plus_res
    ∧ ∃ (plus_res_2 : MyNat_u),
      plus_rel ⌊ ds_d9bM -⌋ (S_u ⌊ m -⌋) plus_res_2 ∧ S_u plus_res == plus_res_2}}.

#[global] Hint Unfold plus_n_Sm_spec: lia_unfold.

Theorem plus_n_Sm (ds_d9bM m : MyNat): plus_n_Sm_spec ds_d9bM m.
Proof.
  destruct ds_d9bM as [ds_d9bM ds_d9bM_p].
  destruct m as [m m_p].
  try revert m_p; generalize dependent m; induction ds_d9bM as [| n' IH_n']; intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (plus_res : MyNat_u),
             plus_rel O_u m plus_res
             ∧ ∃ (plus_res_2 : MyNat_u), plus_rel O_u (S_u m) plus_res_2 ∧ S_u plus_res == plus_res_2)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (plus_res : MyNat_u),
             plus_rel (S_u n') m plus_res
             ∧ ∃ (plus_res_2 : MyNat_u), plus_rel (S_u n') (S_u m) plus_res_2 ∧ S_u plus_res == plus_res_2)
            (IH_n' ltac:(try clear IH_n'; solver) m ltac:(try clear IH_n'; solver))
            ltac:(solver)).
Qed.

Definition mul_0_r_spec (ds_d9bN : MyNat): Type :=
  {{∃ (mult_res : MyNat_u), mult_rel ⌊ ds_d9bN -⌋ O_u mult_res ∧ mult_res == O_u}}.

#[global] Hint Unfold mul_0_r_spec: lia_unfold.

Theorem mul_0_r (ds_d9bN : MyNat): mul_0_r_spec ds_d9bN.
Proof.
  destruct ds_d9bN as [ds_d9bN ds_d9bN_p].
  induction ds_d9bN as [| n' IH_n'].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (mult_res : MyNat_u), mult_rel O_u O_u mult_res ∧ mult_res == O_u)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (mult_res : MyNat_u), mult_rel (S_u n') O_u mult_res ∧ mult_res == O_u)
            (IH_n' ltac:(try clear IH_n'; solver))
            ltac:(solver)).
Qed.

Definition minus_n_n_spec (ds_d9bO : MyNat): Type :=
  {{∃ (minus_res : MyNat_u), minus_rel ⌊ ds_d9bO -⌋ ⌊ ds_d9bO -⌋ minus_res ∧ minus_res == O_u}}.

#[global] Hint Unfold minus_n_n_spec: lia_unfold.

Theorem minus_n_n (ds_d9bO : MyNat): minus_n_n_spec ds_d9bO.
Proof.
  destruct ds_d9bO as [ds_d9bO ds_d9bO_p].
  induction ds_d9bO as [| n' IH_n'].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (minus_res : MyNat_u), minus_rel O_u O_u minus_res ∧ minus_res == O_u)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (minus_res : MyNat_u), minus_rel (S_u n') (S_u n') minus_res ∧ minus_res == O_u)
            (IH_n' ltac:(try clear IH_n'; solver))
            ltac:(solver)).
Qed.

Definition add_0_r_spec (ds_d9bP : MyNat): Type :=
  {{∃ (plus_res : MyNat_u), plus_rel ⌊ ds_d9bP -⌋ O_u plus_res ∧ plus_res == ⌊ ds_d9bP -⌋}}.

#[global] Hint Unfold add_0_r_spec: lia_unfold.

Theorem add_0_r (ds_d9bP : MyNat): add_0_r_spec ds_d9bP.
Proof.
  destruct ds_d9bP as [ds_d9bP ds_d9bP_p].
  induction ds_d9bP as [| n' IH_n'].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (plus_res : MyNat_u), plus_rel O_u O_u plus_res ∧ plus_res == O_u)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (plus_res : MyNat_u), plus_rel (S_u n') O_u plus_res ∧ plus_res == S_u n')
            (IH_n' ltac:(try clear IH_n'; solver))
            ltac:(solver)).
Qed.

Definition add_comm_spec (ds_d9bQ m : MyNat): Type :=
  {{∃ (plus_res : MyNat_u),
    plus_rel ⌊ ds_d9bQ -⌋ ⌊ m -⌋ plus_res
    ∧ ∃ (plus_res_2 : MyNat_u), plus_rel ⌊ m -⌋ ⌊ ds_d9bQ -⌋ plus_res_2 ∧ plus_res == plus_res_2}}.

#[global] Hint Unfold add_comm_spec: lia_unfold.

Theorem add_comm (ds_d9bQ m : MyNat): add_comm_spec ds_d9bQ m.
Proof.
  destruct ds_d9bQ as [ds_d9bQ ds_d9bQ_p].
  destruct m as [m m_p].
  try revert m_p; generalize dependent m; induction ds_d9bQ as [| n' IH_n']; intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (plus_res : MyNat_u),
             plus_rel O_u m plus_res
             ∧ ∃ (plus_res_2 : MyNat_u), plus_rel m O_u plus_res_2 ∧ plus_res == plus_res_2)
            (add_0_r (exist (λ (m : MyNat_u), MyNat_wf m ∧ True) m ltac:(solver)))
            ltac:(solver)).
  - assert (h_15156453 : plus n' m ==? plus m n').
    { refine (IH_n' ltac:(try clear IH_n'; solver) m ltac:(try clear IH_n'; solver)). }
    refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (plus_res : MyNat_u),
             plus_rel (S_u n') m plus_res
             ∧ ∃ (plus_res_2 : MyNat_u), plus_rel m (S_u n') plus_res_2 ∧ plus_res == plus_res_2)
            (plus_n_Sm
             (exist (λ (m : MyNat_u), MyNat_wf m ∧ True) m ltac:(solver))
             (exist (λ (VV : MyNat_u), MyNat_wf VV ∧ True) n' ltac:(solver)))
            ltac:(solver)).
Qed.
