Module Snipe.
(* Print LoadPath. *)
(* From SMTCoq Require SMTCoq. *)
(* From Sniper Require Sniper. *)
Require Import Bool.

Require Import ZArith.

Require Import Init.Datatypes (tt).
(* Include Sniper. (* makes the snipe tactic available *) *)
(* Include Tactics. (* makes the SMTCoq tactics available *) *)
Ltac smt_solve := easy.
  (* solve [unshelve verit_bool].*)
(* Ltac sniper := 
  snipe. *)
End Snipe.

Ltac smt :=
  (* Check if the smt solver tactic is currectly set up *)
  tryif (
    let H := fresh "H" in
    assert True as H by (first [Snipe.smt_solve | fail]); clear H
  ) then
    first [Snipe.smt_solve | fail] (* the backtracking suppresses useless debug output when the tactic fails anyways. *)
  else fail. 

Goal True.
Proof.
  tryif Snipe.smt_solve then idtac else now idtac "verit tactic unable to prove True!". 
Qed.