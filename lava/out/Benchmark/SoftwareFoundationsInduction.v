From coqDeps Require Export LiquidPreludeUtil.
Open Scope Z_scope.
Open Scope Int_scope.
Set Universe Polymorphism.
From Coq Require Import Unicode.Utf8.

Load Benchmark.SoftwareFoundationsBasics.

Definition plus_n_Sm_spec (ds_d993 m : MyNat): Type :=
  {{∃ (plus_res : MyNat_u),
    plus_rel ⌊ ds_d993 -⌋ ⌊ m -⌋ plus_res
    ∧ ∃ (plus_res_2 : MyNat_u),
      plus_rel ⌊ ds_d993 -⌋ (S_u ⌊ m -⌋) plus_res_2 ∧ S_u plus_res == plus_res_2}}.

#[global] Hint Unfold plus_n_Sm_spec: lia_unfold.

Theorem plus_n_Sm (ds_d993 m : MyNat): plus_n_Sm_spec ds_d993 m.
Proof.
  destruct ds_d993 as [ds_d993 ds_d993_p].
  destruct m as [m m_p].
  try revert m_p; generalize dependent m; induction ds_d993 as [| n' IH_n']; intros.
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

Definition mul_0_r_spec (ds_d994 : MyNat): Type :=
  {{∃ (mult_res : MyNat_u), mult_rel ⌊ ds_d994 -⌋ O_u mult_res ∧ mult_res == O_u}}.

#[global] Hint Unfold mul_0_r_spec: lia_unfold.

Theorem mul_0_r (ds_d994 : MyNat): mul_0_r_spec ds_d994.
Proof.
  destruct ds_d994 as [ds_d994 ds_d994_p].
  induction ds_d994 as [| n' IH_n'].
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

Definition minus_n_n_spec (ds_d995 : MyNat): Type :=
  {{∃ (minus_res : MyNat_u), minus_rel ⌊ ds_d995 -⌋ ⌊ ds_d995 -⌋ minus_res ∧ minus_res == O_u}}.

#[global] Hint Unfold minus_n_n_spec: lia_unfold.

Theorem minus_n_n (ds_d995 : MyNat): minus_n_n_spec ds_d995.
Proof.
  destruct ds_d995 as [ds_d995 ds_d995_p].
  induction ds_d995 as [| n' IH_n'].
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

Definition add_0_r_spec (ds_d996 : MyNat): Type :=
  {{∃ (plus_res : MyNat_u), plus_rel ⌊ ds_d996 -⌋ O_u plus_res ∧ plus_res == ⌊ ds_d996 -⌋}}.

#[global] Hint Unfold add_0_r_spec: lia_unfold.

Theorem add_0_r (ds_d996 : MyNat): add_0_r_spec ds_d996.
Proof.
  destruct ds_d996 as [ds_d996 ds_d996_p].
  induction ds_d996 as [| n' IH_n'].
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

Definition add_comm_spec (ds_d997 m : MyNat): Type :=
  {{∃ (plus_res : MyNat_u),
    plus_rel ⌊ ds_d997 -⌋ ⌊ m -⌋ plus_res
    ∧ ∃ (plus_res_2 : MyNat_u), plus_rel ⌊ m -⌋ ⌊ ds_d997 -⌋ plus_res_2 ∧ plus_res == plus_res_2}}.

#[global] Hint Unfold add_comm_spec: lia_unfold.

Theorem add_comm (ds_d997 m : MyNat): add_comm_spec ds_d997 m.
Proof.
  destruct ds_d997 as [ds_d997 ds_d997_p].
  destruct m as [m m_p].
  try revert m_p; generalize dependent m; induction ds_d997 as [| n' IH_n']; intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (plus_res : MyNat_u),
             plus_rel O_u m plus_res
             ∧ ∃ (plus_res_2 : MyNat_u), plus_rel m O_u plus_res_2 ∧ plus_res == plus_res_2)
            (add_0_r (exist (λ (m : MyNat_u), MyNat_wf m ∧ True) m ltac:(solver)))
            ltac:(solver)).
  - try assert (VVinj_wit_67733700 : (λ (VV : MyNat_u), MyNat_wf VV ∧ True) n') by (solver).
    pose (exist (λ (VV : MyNat_u), MyNat_wf VV ∧ True) n' VVinj_wit_67733700) as h_18440229_1.
    try assert (minj_wit_48152372 : (λ (m : MyNat_u), MyNat_wf m ∧ True) m) by (solver).
    pose (exist (λ (m : MyNat_u), MyNat_wf m ∧ True) m minj_wit_48152372) as h_18440229_2.
    pose (IH_n'
          ltac:(try clear IH_n'; solver)
          ⌊ h_18440229_2 -⌋
          ltac:(try clear IH_n'; solver)) as h_18440229.
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
