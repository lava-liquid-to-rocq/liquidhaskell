Load LHCoqTactics.
Create HintDb int_rel_back.
#[global] Hint Resolve addZ_rel_funct : f_rel_funct_db.
#[global] Hint Resolve addZ_rel_ex : rel_ax_db.
#[global] Hint Resolve lebZ_rel_funct : f_rel_funct_db.
#[global] Hint Resolve lebZ_rel_ex : rel_ax_db.
#[global] Hint Resolve ltbZ_rel_funct : f_rel_funct_db.
#[global] Hint Resolve ltbZ_rel_ex : rel_ax_db.
#[global] Hint Resolve eqbZ_rel_funct : f_rel_funct_db.
#[global] Hint Resolve eqbZ_rel_ex : rel_ax_db.
#[global] Hint Resolve gebZ_rel_funct : f_rel_funct_db.
#[global] Hint Resolve gebZ_rel_ex : rel_ax_db.
#[global] Hint Resolve gtbZ_rel_funct : f_rel_funct_db.
#[global] Hint Resolve gtbZ_rel_ex : rel_ax_db.
#[global] Hint Resolve subZ_rel_funct : f_rel_funct_db.
#[global] Hint Resolve subZ_rel_ex : rel_ax_db.
#[global] Hint Resolve multZ_rel_funct : f_rel_funct_db.
#[global] Hint Resolve multZ_rel_ex : rel_ax_db.
#[global] Hint Resolve divZ_rel_funct : f_rel_funct_db.
#[global] Hint Resolve divZ_rel_ex : rel_ax_db.

#[global] Hint Rewrite addZ_lem : f_rel_back.
#[global] Hint Rewrite addZ__addZ_rel_rw : f_rel_funct_db.
#[global] Hint Rewrite lebZ_lem_true : int_rel_back.
#[global] Hint Rewrite lebZ_lem : int_rel_back.
#[global] Hint Rewrite lebZ__lebZ_rel_rw : f_rel_funct_db.
#[global] Hint Rewrite ltbZ_lem_true : int_rel_back.
#[global] Hint Rewrite ltbZ_lem : int_rel_back.
#[global] Hint Rewrite ltbZ__ltbZ_rel_rw : f_rel_funct_db.
#[global] Hint Rewrite eqbZ_lem_true : int_rel_back.
#[global] Hint Rewrite eqbZ_lem : int_rel_back.
#[global] Hint Rewrite eqbZ__eqbZ_rel_rw : f_rel_funct_db.
#[global] Hint Rewrite gebZ_lem_true : int_rel_back.
#[global] Hint Rewrite gebZ_lem : int_rel_back.
#[global] Hint Rewrite gebZ__gebZ_rel_rw : f_rel_funct_db.
#[global] Hint Rewrite gtbZ_lem_true : int_rel_back.
#[global] Hint Rewrite gtbZ_lem : int_rel_back.
#[global] Hint Rewrite gtbZ__gtbZ_rel_rw : f_rel_funct_db.
#[global] Hint Rewrite subZ_lem : f_rel_back.
#[global] Hint Rewrite subZ__subZ_rel_rw : f_rel_funct_db.
#[global] Hint Rewrite multZ_lem : f_rel_back.
#[global] Hint Rewrite multZ__multZ_rel_rw : f_rel_funct_db.
#[global] Hint Rewrite divZ_lem : f_rel_back.
#[global] Hint Rewrite divZ__divZ_rel_rw : f_rel_funct_db.

#[global] Hint Rewrite proj_addZ :lia_rewrites.
#[global] Hint Rewrite proj_subZ :lia_rewrites.
#[global] Hint Rewrite proj_multZ :lia_rewrites.
#[global] Hint Rewrite proj_divZ :lia_rewrites.

#[global] Hint Rewrite addZ_rel_rw :lia_rewrites.
#[global] Hint Rewrite subZ_rel_rw :lia_rewrites.
#[global] Hint Rewrite multZ_rel_rw :lia_rewrites.
#[global] Hint Rewrite divZ_rel_rw :lia_rewrites.

#[global] Hint Rewrite ltbZ_rel_rw :lia_rewrites.
#[global] Hint Rewrite lebZ_rel_rw :lia_rewrites.
#[global] Hint Rewrite gebZ_rel_rw :lia_rewrites.
#[global] Hint Rewrite gtbZ_rel_rw :lia_rewrites.

#[global] Instance addZ_addZF : getFunc addZ_rel := { 
	getF' := addZ
}.

#[global] Instance lebZ_getF : getFunc lebZ_rel := { 
	getF' := lebZ
}.
#[global] Instance ltbZ_getF : getFunc ltbZ_rel := { 
	getF' := ltbZ
}.
#[global] Instance gtbZ_getF : getFunc gtbZ_rel := { 
	getF' := gtbZ
}.
#[global] Instance gebZ_getF : getFunc gebZ_rel := { 
	getF' := gebZ
}.
#[global] Instance subZ_getF : getFunc subZ_rel := { 
	getF' := subZ
}.
#[global] Instance multZ_getF : getFunc multZ_rel := { 
	getF' := multZ
}.
#[global] Instance divZ_getF : getFunc divZ_rel := { 
	getF' := divZ
}.
(* Todo: put the other lookup instances here as well *)

Ltac lia_preprocessor := repeat_or_fail (progress (
  concat_either 
    (concat_either 
      (destructEqnResAppProj; repeat progress autorewrite with fix_notation_hints in *)
      (lia_preprocessor_step; try split_hyps; try unify_vars)) 
    (concat_either (progress repeat autounfold with lia_unfold in *) (progress repeat autorewrite with lia_rewrites in *)))).

Ltac preprocessor_ b :=
  let inv := fresh "inverted" in
  pose _nil as inv;
  concat_either (timeout 300 progress cleanup_after_hints_ b) (lia_preprocessor);
  try (inversion_specialization inv);
  repeat (concat_either (timeout 300 progress cleanup_after_hints) (lia_preprocessor)).

Ltac preprocessor := preprocessor_ True.

Ltac saturating_solver := simpl in *; first [
  quick_wff_wit
  | lia_preprocessor; lia 
  | repeat unshelve cleanup_hints; 
    preprocessor; 
    first [lia | oracle | idtac "Shelving goal "; print_proof_state; shelve]
  ].

(*
Ltac solver := repeat first [
  quick_wff_wit 
  | lia_preprocessor; lia 
  | oracle
  (* | preprocessor_ False; 
    first [lia | finish | preprocessor; first [lia | finish] ] *)
  | fail (* repeat unshelve cleanup_hints; 
    preprocessor; 
    first [lia | oracle | shelve] *)
  ].
*)
Ltac solver_loop :=
  repeat_or_fail concat_either (quick_wff_wit) (
    concat_either (quicksolve) (
      progress concat_either (
        simpl in *; (*try timeout 2 repeat nonbranching_destruct;*)
        timeout 1200 cleanup_after_hints) (
        lia_preprocessor
        (*concat_either (lia_preprocessor) (split_hyps)*)
      )
    )
  ); intros.

Ltac solver := simpl in *; solve [
    solver_loop; progress saturate_context; solver_loop
    | idtac ""; idtac "Falling back to saturating_solver"; fail (*saturating_solver *)].
#[global] Hint Extern 20 () => solver : solver_db. 

Ltac unsaturating_solver := first [
  quick_wff_wit
  | lia_preprocessor; lia 
  | solver_loop; progress saturate_context; 
    first [lia | solver_loop | 
      repeat destructEqnResAppProj;
      repeat progress autorewrite with fix_notation_hints in *;
      idtac "Shelving goal "; print_proof_state; shelve]
  ].

Ltac equationsPreSolver := 
  repeat destructEqnResAppProj;
  repeat progress autorewrite with fix_notation_hints in *;
  try initial_simple_cleanup_steps;
  try fast_done.

Ltac equationsSolver := 
  equationsPreSolver;
  unshelve solver.

Ltac equationsUnsaturatingSolver := 
  equationsPreSolver;
  unshelve unsaturating_solver.

Obligation Tactic := equationsSolver.

Definition injref {A:Type} {P: A -> Prop} (tm:A) (z:P tm): {x:A | P x} := exist _ tm z.
Notation " ↼ tm" := (injref tm (ltac:(solver))) (at level 1).

Ltac f__f_rel_mk := unfold proj; unfold refinement_proj; 
  (*unfold packProj; unfold packPr; *)
  first [ intros; now autorewrite with f_rel_funct_db | solver].
