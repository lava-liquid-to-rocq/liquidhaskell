

Load Benchmark.SoftwareFoundationsBasics.

Definition plus_n_Sm_spec (n m : MyNat): Type :=
  {{∀ plus_res,
    plus_rel ⌊ n ⌋ ⌊ m ⌋ plus_res
    → ∀ plus_res_2, plus_rel ⌊ n ⌋ (S_u ⌊ m ⌋) plus_res_2 → S_u plus_res == plus_res_2}}.

#[global] Hint Unfold plus_n_Sm_spec: lia_unfold.

Theorem plus_n_Sm (n m : MyNat): plus_n_Sm_spec n m.
Proof.
  destruct n as [n n_p].
  destruct m as [m m_p].
  try revert m_p; generalize dependent m; induction n as [| n' IH_n']; intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∀ plus_res,
             plus_rel ⌊ n ⌋ ⌊ m ⌋ plus_res
             → ∀ plus_res_2, plus_rel ⌊ n ⌋ (S_u ⌊ m ⌋) plus_res_2 → S_u plus_res == plus_res_2)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∀ plus_res,
             plus_rel ⌊ n ⌋ ⌊ m ⌋ plus_res
             → ∀ plus_res_2, plus_rel ⌊ n ⌋ (S_u ⌊ m ⌋) plus_res_2 → S_u plus_res == plus_res_2)
            (IH_n' ltac:(try clear IH_n'; solver) m ltac:(try clear IH_n'; solver))
            ltac:(solver)).
Qed.

Definition mul_0_r_spec (n : MyNat): Type :=
  {{∀ mult_res, mult_rel ⌊ n ⌋ O_u mult_res → mult_res == O_u}}.

#[global] Hint Unfold mul_0_r_spec: lia_unfold.

Theorem mul_0_r (n : MyNat): mul_0_r_spec n.
Proof.
  destruct n as [n n_p].
  induction n as [| n' IH_n'].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∀ mult_res, mult_rel ⌊ n ⌋ O_u mult_res → mult_res == O_u)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∀ mult_res, mult_rel ⌊ n ⌋ O_u mult_res → mult_res == O_u)
            (IH_n' ltac:(try clear IH_n'; solver))
            ltac:(solver)).
Qed.

Definition minus_n_n_spec (n : MyNat): Type :=
  {{∀ minus_res, minus_rel ⌊ n ⌋ ⌊ n ⌋ minus_res → minus_res == O_u}}.

#[global] Hint Unfold minus_n_n_spec: lia_unfold.

Theorem minus_n_n (n : MyNat): minus_n_n_spec n.
Proof.
  destruct n as [n n_p].
  induction n as [| n' IH_n'].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∀ minus_res, minus_rel ⌊ n ⌋ ⌊ n ⌋ minus_res → minus_res == O_u)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∀ minus_res, minus_rel ⌊ n ⌋ ⌊ n ⌋ minus_res → minus_res == O_u)
            (IH_n' ltac:(try clear IH_n'; solver))
            ltac:(solver)).
Qed.

Definition add_0_r_spec (n : MyNat): Type :=
  {{∀ plus_res, plus_rel ⌊ n ⌋ O_u plus_res → plus_res == ⌊ n ⌋}}.

#[global] Hint Unfold add_0_r_spec: lia_unfold.

Theorem add_0_r (n : MyNat): add_0_r_spec n.
Proof.
  destruct n as [n n_p].
  induction n as [| n' IH_n'].
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∀ plus_res, plus_rel ⌊ n ⌋ O_u plus_res → plus_res == ⌊ n ⌋)
            (# unit)
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit), ∀ plus_res, plus_rel ⌊ n ⌋ O_u plus_res → plus_res == ⌊ n ⌋)
            (IH_n' ltac:(try clear IH_n'; solver))
            ltac:(solver)).
Qed.

Definition add_comm_spec (n m : MyNat): Type :=
  {{∀ plus_res,
    plus_rel ⌊ n ⌋ ⌊ m ⌋ plus_res
    → ∀ plus_res_2, plus_rel ⌊ m ⌋ ⌊ n ⌋ plus_res_2 → plus_res == plus_res_2}}.

#[global] Hint Unfold add_comm_spec: lia_unfold.

Theorem add_comm (n m : MyNat): add_comm_spec n m.
Proof.
  destruct n as [n n_p].
  destruct m as [m m_p].
  try revert m_p; generalize dependent m; induction n as [| n' IH_n']; intros.
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∀ plus_res,
             plus_rel ⌊ n ⌋ ⌊ m ⌋ plus_res
             → ∀ plus_res_2, plus_rel ⌊ m ⌋ ⌊ n ⌋ plus_res_2 → plus_res == plus_res_2)
            (add_0_r (exist (λ (m : MyNat_u), MyNat_wf m ∧ True) m ltac:(solver)))
            ltac:(solver)).
  - refine (subsumptionCast
            Unit
            (λ (VV : Unit),
             ∀ plus_res,
             plus_rel ⌊ n ⌋ ⌊ m ⌋ plus_res
             → ∀ plus_res_2, plus_rel ⌊ m ⌋ ⌊ n ⌋ plus_res_2 → plus_res == plus_res_2)
            (let _: ∀ plus_res,
                    plus_rel n' m plus_res → ∀ plus_res_2, plus_rel m n' plus_res_2 → plus_res == plus_res_2 :=
             ⌈ IH_n' ltac:(try clear IH_n'; solver) m ltac:(try clear IH_n'; solver) ⌉ in
             plus_n_Sm
             (exist (λ (m : MyNat_u), MyNat_wf m ∧ True) m ltac:(solver))
             (exist (λ (VV : MyNat_u), MyNat_wf VV ∧ True) n' ltac:(solver)))
            ltac:(solver)).
Qed.
