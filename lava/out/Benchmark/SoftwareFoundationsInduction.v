

Load Benchmark.SoftwareFoundationsBasics.

Definition plus_n_Sm_spec (ds_d9ab m : MyNat): Type :=
  {{∃ (plus_res : MyNat_u),
    plus_rel ⌊ ds_d9ab -⌋ ⌊ m -⌋ plus_res
    ∧ ∃ (plus_res_2 : MyNat_u),
      plus_rel ⌊ ds_d9ab -⌋ (S_u ⌊ m -⌋) plus_res_2 ∧ S_u plus_res == plus_res_2}}.

#[global] Hint Unfold plus_n_Sm_spec: lia_unfold.

Theorem plus_n_Sm (ds_d9ab m : MyNat): plus_n_Sm_spec ds_d9ab m.
Proof.
  destruct ds_d9ab as [ds_d9ab ds_d9ab_p].
  destruct m as [m m_p].
  try revert m_p; generalize dependent m; induction ds_d9ab as [| n' IH_n']; intros.
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

Definition mul_0_r_spec (ds_d9ac : MyNat): Type :=
  {{∃ (mult_res : MyNat_u), mult_rel ⌊ ds_d9ac -⌋ O_u mult_res ∧ mult_res == O_u}}.

#[global] Hint Unfold mul_0_r_spec: lia_unfold.

Theorem mul_0_r (ds_d9ac : MyNat): mul_0_r_spec ds_d9ac.
Proof.
  destruct ds_d9ac as [ds_d9ac ds_d9ac_p].
  induction ds_d9ac as [| n' IH_n'].
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

Definition minus_n_n_spec (ds_d9ad : MyNat): Type :=
  {{∃ (minus_res : MyNat_u), minus_rel ⌊ ds_d9ad -⌋ ⌊ ds_d9ad -⌋ minus_res ∧ minus_res == O_u}}.

#[global] Hint Unfold minus_n_n_spec: lia_unfold.

Theorem minus_n_n (ds_d9ad : MyNat): minus_n_n_spec ds_d9ad.
Proof.
  destruct ds_d9ad as [ds_d9ad ds_d9ad_p].
  induction ds_d9ad as [| n' IH_n'].
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

Definition add_0_r_spec (ds_d9ae : MyNat): Type :=
  {{∃ (plus_res : MyNat_u), plus_rel ⌊ ds_d9ae -⌋ O_u plus_res ∧ plus_res == ⌊ ds_d9ae -⌋}}.

#[global] Hint Unfold add_0_r_spec: lia_unfold.

Theorem add_0_r (ds_d9ae : MyNat): add_0_r_spec ds_d9ae.
Proof.
  destruct ds_d9ae as [ds_d9ae ds_d9ae_p].
  induction ds_d9ae as [| n' IH_n'].
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

Definition add_comm_spec (ds_d9af m : MyNat): Type :=
  {{∃ (plus_res : MyNat_u),
    plus_rel ⌊ ds_d9af -⌋ ⌊ m -⌋ plus_res
    ∧ ∃ (plus_res_2 : MyNat_u), plus_rel ⌊ m -⌋ ⌊ ds_d9af -⌋ plus_res_2 ∧ plus_res == plus_res_2}}.

#[global] Hint Unfold add_comm_spec: lia_unfold.

Theorem add_comm (ds_d9af m : MyNat): add_comm_spec ds_d9af m.
Proof.
  destruct ds_d9af as [ds_d9af ds_d9af_p].
  destruct m as [m m_p].
  try revert m_p; generalize dependent m; induction ds_d9af as [| n' IH_n']; intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (plus_res : MyNat_u),
             plus_rel O_u m plus_res
             ∧ ∃ (plus_res_2 : MyNat_u), plus_rel m O_u plus_res_2 ∧ plus_res == plus_res_2)
            (add_0_r (exist (λ (m : MyNat_u), MyNat_wf m ∧ True) m ltac:(solver)))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (plus_res : MyNat_u),
             plus_rel (S_u n') m plus_res
             ∧ ∃ (plus_res_2 : MyNat_u), plus_rel m (S_u n') plus_res_2 ∧ plus_res == plus_res_2)
            (let _: ∃ (plus_res : MyNat_u),
                    plus_rel n' m plus_res
                    ∧ ∃ (plus_res_2 : MyNat_u), plus_rel m n' plus_res_2 ∧ plus_res == plus_res_2 :=
             ⌈ IH_n' ltac:(try clear IH_n'; solver) m ltac:(try clear IH_n'; solver) ⌉ in
             plus_n_Sm
             (exist (λ (m : MyNat_u), MyNat_wf m ∧ True) m ltac:(solver))
             (exist (λ (VV : MyNat_u), MyNat_wf VV ∧ True) n' ltac:(solver)))
            ltac:(solver)).
Qed.
