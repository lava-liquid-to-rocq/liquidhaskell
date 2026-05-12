

Load Benchmark.SoftwareFoundationsBasics.

Definition plus_n_Sm_spec (ds_d9ag m : MyNat): Type :=
  {{∃ (plus_res : MyNat_u),
    plus_rel ⌊ ds_d9ag ⌋ ⌊ m ⌋ plus_res
    ∧ ∃ (plus_res_2 : MyNat_u),
      plus_rel ⌊ ds_d9ag ⌋ (S_u ⌊ m ⌋) plus_res_2 ∧ S_u plus_res == plus_res_2}}.

#[global] Hint Unfold plus_n_Sm_spec: lia_unfold.

Theorem plus_n_Sm (ds_d9ag m : MyNat): plus_n_Sm_spec ds_d9ag m.
Proof.
  destruct ds_d9ag as [ds_d9ag ds_d9ag_p].
  destruct m as [m m_p].
  try revert m_p; generalize dependent m; induction ds_d9ag as [| n' IH_n']; intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (plus_res : MyNat_u),
             plus_rel ds_d9ag m plus_res
             ∧ ∃ (plus_res_2 : MyNat_u), plus_rel ds_d9ag (S_u m) plus_res_2 ∧ S_u plus_res == plus_res_2)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (plus_res : MyNat_u),
             plus_rel ds_d9ag m plus_res
             ∧ ∃ (plus_res_2 : MyNat_u), plus_rel ds_d9ag (S_u m) plus_res_2 ∧ S_u plus_res == plus_res_2)
            (IH_n' ltac:(try clear IH_n'; solver) m ltac:(try clear IH_n'; solver))
            ltac:(solver)).
Qed.

Definition mul_0_r_spec (ds_d9ah : MyNat): Type :=
  {{∃ (mult_res : MyNat_u), mult_rel ⌊ ds_d9ah ⌋ O_u mult_res ∧ mult_res == O_u}}.

#[global] Hint Unfold mul_0_r_spec: lia_unfold.

Theorem mul_0_r (ds_d9ah : MyNat): mul_0_r_spec ds_d9ah.
Proof.
  destruct ds_d9ah as [ds_d9ah ds_d9ah_p].
  induction ds_d9ah as [| n' IH_n'].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (mult_res : MyNat_u), mult_rel ds_d9ah O_u mult_res ∧ mult_res == O_u)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (mult_res : MyNat_u), mult_rel ds_d9ah O_u mult_res ∧ mult_res == O_u)
            (IH_n' ltac:(try clear IH_n'; solver))
            ltac:(solver)).
Qed.

Definition minus_n_n_spec (ds_d9ai : MyNat): Type :=
  {{∃ (minus_res : MyNat_u), minus_rel ⌊ ds_d9ai ⌋ ⌊ ds_d9ai ⌋ minus_res ∧ minus_res == O_u}}.

#[global] Hint Unfold minus_n_n_spec: lia_unfold.

Theorem minus_n_n (ds_d9ai : MyNat): minus_n_n_spec ds_d9ai.
Proof.
  destruct ds_d9ai as [ds_d9ai ds_d9ai_p].
  induction ds_d9ai as [| n' IH_n'].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (minus_res : MyNat_u), minus_rel ds_d9ai ds_d9ai minus_res ∧ minus_res == O_u)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (minus_res : MyNat_u), minus_rel ds_d9ai ds_d9ai minus_res ∧ minus_res == O_u)
            (IH_n' ltac:(try clear IH_n'; solver))
            ltac:(solver)).
Qed.

Definition add_0_r_spec (ds_d9aj : MyNat): Type :=
  {{∃ (plus_res : MyNat_u), plus_rel ⌊ ds_d9aj ⌋ O_u plus_res ∧ plus_res == ⌊ ds_d9aj ⌋}}.

#[global] Hint Unfold add_0_r_spec: lia_unfold.

Theorem add_0_r (ds_d9aj : MyNat): add_0_r_spec ds_d9aj.
Proof.
  destruct ds_d9aj as [ds_d9aj ds_d9aj_p].
  induction ds_d9aj as [| n' IH_n'].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (plus_res : MyNat_u), plus_rel ds_d9aj O_u plus_res ∧ plus_res == ds_d9aj)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∃ (plus_res : MyNat_u), plus_rel ds_d9aj O_u plus_res ∧ plus_res == ds_d9aj)
            (IH_n' ltac:(try clear IH_n'; solver))
            ltac:(solver)).
Qed.

Definition add_comm_spec (ds_d9ak m : MyNat): Type :=
  {{∃ (plus_res : MyNat_u),
    plus_rel ⌊ ds_d9ak ⌋ ⌊ m ⌋ plus_res
    ∧ ∃ (plus_res_2 : MyNat_u), plus_rel ⌊ m ⌋ ⌊ ds_d9ak ⌋ plus_res_2 ∧ plus_res == plus_res_2}}.

#[global] Hint Unfold add_comm_spec: lia_unfold.

Theorem add_comm (ds_d9ak m : MyNat): add_comm_spec ds_d9ak m.
Proof.
  destruct ds_d9ak as [ds_d9ak ds_d9ak_p].
  destruct m as [m m_p].
  try revert m_p; generalize dependent m; induction ds_d9ak as [| n' IH_n']; intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (plus_res : MyNat_u),
             plus_rel ds_d9ak m plus_res
             ∧ ∃ (plus_res_2 : MyNat_u), plus_rel m ds_d9ak plus_res_2 ∧ plus_res == plus_res_2)
            (add_0_r (exist (λ (m : MyNat_u), MyNat_wf m ∧ True) m ltac:(solver)))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∃ (plus_res : MyNat_u),
             plus_rel ds_d9ak m plus_res
             ∧ ∃ (plus_res_2 : MyNat_u), plus_rel m ds_d9ak plus_res_2 ∧ plus_res == plus_res_2)
            (let _: ∃ (plus_res : MyNat_u),
                    plus_rel n' m plus_res
                    ∧ ∃ (plus_res_2 : MyNat_u), plus_rel m n' plus_res_2 ∧ plus_res == plus_res_2 :=
             ⌈ IH_n' ltac:(try clear IH_n'; solver) m ltac:(try clear IH_n'; solver) ⌉ in
             plus_n_Sm
             (exist (λ (m : MyNat_u), MyNat_wf m ∧ True) m ltac:(solver))
             (exist (λ (VV : MyNat_u), MyNat_wf VV ∧ True) n' ltac:(solver)))
            ltac:(solver)).
Qed.
