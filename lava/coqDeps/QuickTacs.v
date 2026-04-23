Load SubsumptionTacs.

Inductive Unit : Set := unit.
Global Notation "{{ p }}" := ({_:Unit | p}).
Ltac destruct_unit := match goal with
  | [ |- ?U = unit] =>
      destruct U; reflexivity
  | [ |- unit = ?U] =>
      destruct U; reflexivity
  | [ |- ?U = ?V] =>
      let tp := type of U in
      match tp with
      Unit => destruct U; destruct_unit
      end
  | [ |- ?U = ?V] =>
      let tp := type of V in
      match tp with
      Unit => destruct V; destruct_unit
      end
  | [ |- ?H -> ?G] => intros _; destruct_unit
  | [ |- _ ] => fail
  end.

(** The first two tactics are adapted from https://gitlab.mpi-sws.org/iris/stdpp/-/blob/df33944852793fd7a93368b6b0251e9f29a3c4dd/stdpp/tactics.v#L45-78 (they are BSD licensed).*)
Create HintDb wff_constr_db.
Create HintDb ref_constr_db.
Create HintDb eq_hint_db.
Create HintDb get_rel_db.
Create HintDb solver_db.
Create HintDb quicksolve_db.
Create HintDb pi_db.

(* stop intuition tactic from spamming deprecation warnings *)
Global Ltac Tauto.intuition_solver ::= auto with *. (*ref_constr_db wff_constr_db fix_notation_hints pi_db f_rel_back f_rel_funct_db lia_unfold lia_rewrites eq_hint_db. *)

Global Ltac split_hyp := 
  match goal with
  | [h: (?p && ?q) = true |- _] =>
    unfold Init.Datatypes.andb in h;
    destruct p eqn:?; [|easy]
  | [h: (?p /\ ?q) |- _ ] =>
    let Hl := fresh "Hl" in
    let Hr := fresh "Hr" in
      destruct h as [Hl Hr]
  end.

Ltac quick_wff_wit :=
  solve [repeat progress first [unshelve eauto with ref_constr_db wff_constr_db | split | split_hyp ]].

(*From coqDeps Require Export Snipe.*)

Ltac fast_done :=
  solve [ 
    quick_wff_wit (* automatically apply the wff lemmas *)
    | unshelve eassumption
    | symmetry; unshelve eassumption
    | destruct_unit
    | lia (* solve integer arithmetic goals *)
    | congruence (* solve goals in theory of equality and uninterpreted functions *)
    | unshelve intuition (* simplify and apply tauto, a decision procedure for constructive propositional logic *)
    | easy  
  ].

Tactic Notation "fast_by" tactic(tac) := tac; fast_done.
(** mimicks Haskell's $ operator in Coq *)
Notation "f $ x" := (f x) (at level 60, right associativity, only parsing).

Ltac f_equal_ind :=
  match goal with
  | [ |- ?G ] =>
    tryif
      (tryif assert (~ G); [ injection |]
       then fail else idtac)
    then
      fail "Not an inductive constructor"
    else
      f_equal
  end.

Local Lemma negb_inj: forall (s t: bool), negb s = negb t <-> s = t.
Proof.
  intros s t. split; intro H; destruct s; destruct t; easy.
Qed.

Tactic Notation "if_not_done" tactic(tac) := tryif simpl then tac else idtac.

Global Lemma neq_eq: forall [A:Type] [s t s' t':A], (s = t) = (s' = t') -> (s <> t) = (s' <> t').
Proof.
  intros A s t s' t' ->. reflexivity.
Qed.

Local Ltac assert_lia_simpl h tp :=
  tryif (let temp := fresh "temp" in
  assert tp as temp by lia;
  clear h; assert _ as h by (exact temp);
  clear temp) then idtac else idtac "Failure to simplify hypothesis " h " to " tp ". ".

Ltac isVar tm :=
  match goal with
  | [h: _ |- _] => eq_fail h tm
  end.

(* very quick single-step tactic that matches on goal and tries to simplifies it, so other tactics can more easily solve it *)
Ltac shape_based := match goal with
  | [h:?g |- ?g] => exact h
  (* the following cases are used for proving the cases for dead branches 
     (translated using exfalso) in the existence lemata *)
  | |- ?f ⌊ False_rec _ ?z -⌋ => exfalso; exact z
  | |- ?f ⌊ False_rect _ ?z -⌋ => exfalso; exact z
  | |- ?c = true \/ ?c = false => destruct c; first [now left | now right]
  | [h: ?c = true |- (?c = true /\ ?d) \/ (?c = false /\ ?e)] => 
    left; split; [apply h|]
  | [h: ?c = false |- (?c = true /\ ?d) \/ (?c = false /\ ?e)] => 
    right; split; [apply h|]

  | [ |- (?x ==? ?y) = (?c ?x ==? ?c ?y)] =>
    eqb_inject_ind  
  | [ h:?p /\ ?q |- (?p /\ ?q')] =>
    destruct h as [? h]
  | [h:?p |- (?p /\ ?q)] => 
    match type of p with
    | Prop => split; [exact h|]
    end
  | [ h: ?p /\ ?q |- (?p' /\ ?q)] => 
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    destruct h as [H1 H2];
    refine (conj _ H2)
  | [ h:?x = (?s ==? ?t) |- ?x = ?H] => 
    revert h;
    apply (eq_eqb_ante s t x); intro h
  | [ h:?x = (?s ==? ?t) |- ?H = ?x] =>
    apply eq_sym; revert h;
    apply (eq_eqb_ante s t x); intro h
  | [ h:?s == ?t |- ?x = ?H] => 
    apply (pr2 (generic_equalb_eq s t)) in h
  | [ h:(is_true (?u ==? ?v)) |- ?K] => 
    apply (pr2 (generic_equalb_eq u v)) in h
  | [ h: negb ?s = negb ?t |- _] =>
    rewrite negb_inj in h
  | [ |- _ -> negb ?s = negb ?t] =>
    let H := fresh "H" in
      intro H; rewrite negb_inj;
      revert H
  | [ h:_ |- negb ?s = negb ?t] =>
    rewrite negb_inj
  | [ h: ?p <-> True |- _ ] => 
    let temp := fresh "temp" in
    assert (p <-> True -> p) as temp by intuition;
    apply temp in h; clear temp
  | [ h: True <-> ?p |- _ ] => 
    let temp := fresh "temp" in
    assert (True <-> p -> p) as temp by intuition;
    apply temp in h; clear temp
  | [ h: ?p = True |- _ ] => 
    let temp := fresh "temp" in
    assert (p = True -> p) as temp by intuition;
    apply temp in h; clear temp
  | [ h: True = ?p |- _ ] => 
    let temp := fresh "temp" in
    assert (True = p -> p) as temp by intuition;
    apply temp in h; clear temp
  (* terms of this shape frequently show up in inductive proofs *)
  | [ h:(?l = (?x ==? ?y)) |- ?l = (?c ?x ==? ?c ?y)] =>
    rewrite h; eqb_inject_ind
  (* we have to show a contradiction, so it might help to split the hypothesis we have *)
  | [ h: ?p /\ ?q |- False] =>
    let H2 := fresh "H1" in
    let H2 := fresh "H2" in
    destruct h as [H1 H2]
  (* we have a precondition expressed via an unref relation, that hopefully yields a contradiction *)
  | [ h: forall (res:bool), ?res_def -> is_true res |- False] =>
    let temp := fresh "temp" in
      specialize (h false); 
      discriminate h
  (* ToDo: Is it really a good idea to have this case? *)
  | [ _:?s = ?t' |- ?s = ?t] =>
    let H := fresh "H" in
      intro H; rewrite H
  | [ |- (?p /\ ?q) -> _] =>
    let Hl := fresh "Hl" in
    let Hr := fresh "Hr" in
      intros [Hr Hr]
  (* | [ h: ?p /\ ?q |- _] =>
    let Hl := fresh "Hl" in
    let Hr := fresh "Hr" in
      destruct h as [Hl Hr] *)
  | [ h: exists v:_, ?p /\ ?q |- _] =>
    let x := fresh "v" in
    let r := fresh "p" in
    let s := fresh "q" in
    destruct h as [v [r s]]
  | [ h: exists v:_, ?p |- _] =>
    let x := fresh "v" in
    let r := fresh "p" in
      destruct h as [v r]
  | [ |- ?ante -> _] =>
      intro
  | [ |- forall (x: ?A), ?G ] =>
      intro x
  | [ |- negb ?s = negb ?t] =>
      rewrite negb_inj
  | [ |- _ /\ _ ] => split
  

  | [ h:(true = (?s ==? ?t)) |- _ ] => apply (pr2  (true_eqb s t)) in h
  | [ h: false = (?s ==? ?t) |- _] => apply (pr2 (false_eqb s t)) in h
  | [ h: (?s ==? ?t) = true |- _] => apply (pr2 (generic_equalb_eq s t)) in h
  | [ h: (?s /=? ?t) = true |- _] => apply (pr1 (istrue_neqb s t)) in h
  | [ h: (?s ==? ?t) = false |- _] => apply (pr2 (eqb_false s t)) in h
  | [ h: is_true ?v |- _ ] => replace v with true in * by (apply h); try clear h v

  | [ |- true = (?s ==? ?t)] => apply (pr1  (true_eqb s t))
  | [ |- false = (?s ==? ?t)] => apply (pr1 (false_eqb s t))
  | [ |- (?s ==? ?t) = true] => apply (pr1 (generic_equalb_eq s t))
  | [ |- (?s ==? ?t) = false] => apply (pr1 (eqb_false s t))
  | [ |- (?s /=? ?t) = true] => apply (pr2 (istrue_neqb s t))
  | [ |- (?s ==? ?t) = (?u ==? ?v)] => first [ eqb_eqb | apply eqb_eqb'; [eauto | eauto] | rewrite (eqb_symm (?s ==? ?t) (?u ==? ?v)); apply eqb_eqb'; [eauto | eauto]]
  | [ |- ?s ==? (?u ==? ?v)] => apply (pr1 (generic_equalb_eq s (?u ==? ?v)))
  | [ |- (?u ==? ?v) ==? ?s] => apply (pr1 (generic_equalb_eq (?u ==? ?v) s))
  | [ |- (is_true (?u ==? ?v))] => unfold is_true
  | [ h: negb ?v = true |- _] => isVar v; apply isTrue_neg in h; try rewrite h in *

  | [h: (?s ?= ?t) = Gt |- _] => 
    let temp := fresh "temp" in 
    let E := fresh "E" in 
    assert (s > t) as temp by (destruct (s ?= t) eqn:E; fast_done);
    clear h; assert _ as h by (exact temp); clear temp
  | [h: (?s ?= ?t) = Lt |- _] => 
    let temp := fresh "temp" in 
    let E := fresh "E" in 
    assert (s < t) as temp by (destruct (s ?= t) eqn:E; fast_done);
    clear h; assert _ as h by (exact temp); clear temp
  | [h: (?s ?= ?t) = Eq |- _] => 
    let temp := fresh "temp" in 
    let E := fresh "E" in 
    assert (s = t) as temp by (destruct (s ?= t) eqn:E; fast_done);
    clear h; assert _ as h by (exact temp); clear temp

  | [h: ?m + ?o = ?n + ?o |- _] => assert_lia_simpl h (m = n)
  | [h: ?o + ?m = ?o + ?n |- _] => assert_lia_simpl h (m = n)
  | [h: ?m - ?o = ?n - ?o |- _] => assert_lia_simpl h (m = n)
  | [h: ?o - ?m = ?o - ?n |- _] => assert_lia_simpl h (m = n)
  | [h: ?m * ?o = ?n * ?o |- _] => assert_lia_simpl h (m = n)
  | [h: ?o * ?m = ?o * ?n |- _] => assert_lia_simpl h (m = n)

  (* the first two check are to prevent the third case getting us into trouble *)
  | [ h: (?s <> ?s') = (?t <> ?t') |- (?s <> ?s') = (?c ?t <> ?c ?t')] => 
    tryif (
      let tp := type of t in
      let inj_lem := fresh "inj_lem"  in
      assert (forall (x y:tp), c x = c y -> x = y) as inj_lem by (let h:= fresh "H" in intros ? ? h; injection h as h; apply h)
    ) then rewrite h else apply neq_eq
  | [ h: (?t <> ?t') = (?s <> ?s') |- (?s <> ?s') = (?c ?t <> ?c ?t')] => 
    tryif (
      let tp := type of t in
      let inj_lem := fresh "inj_lem"  in
      assert (forall (x y:tp), c x = c y -> x = y) as inj_lem by (let h:= fresh "H" in intros ? ? h; injection h as h; apply h)
    ) then rewrite <- h else apply neq_eq
  | [ |- (_ <> _) = (_ <> _)] => apply neq_eq

  | [ h: forall v, ltbZ_rel ?s ?t v -> _ |- _] => 
    specialize (h (s <? t));
    specialize (h (ltac:(constructor)))
  | [ h: forall v, lebZ_rel ?s ?t v -> _ |- _] => 
    specialize (h (s <=? t));
    specialize (h (ltac:(constructor)))
  | [ h: forall v, eqbZ_rel ?s ?t v -> _ |- _] => 
    specialize (h (s =? t));
    specialize (h (ltac:(constructor)))
  | [ h: forall v, gebZ_rel ?s ?t v -> _ |- _] => 
    specialize (h (s >=? t));
    specialize (h (ltac:(constructor)))
  | [ h: forall v, gtbZ_rel ?s ?t v -> _ |- _] => 
    specialize (h (s =? t));
    specialize (h (ltac:(constructor)))

  (*| [h: ?wf ⌊ ?ih ?z1 _ _ _ _ -⌋ |- _] =>
    tryif (isVar z1) then fail else idtac;
    let prf := fresh "z" in
    pose proof z1 as prf;
    progress replace z1 with prf in * by (auto with pi_db)
  | [h: ?wf ⌊ ?ih ?z1 _ _ -⌋ |- _] =>
    tryif (isVar z1) then fail else idtac;
    let prf := fresh "z" in
    pose proof z1 as prf;
    progress replace z1 with prf in * by (auto with pi_db)
  | [h: ?wf ⌊ ?ih ?z -⌋ |- _] =>
    tryif (isVar z) then fail else idtac;
    let prf := fresh "z" in
    pose proof z as prf;
    progress replace z with prf in * by (auto with pi_db)*)

  | [ h: ⌊ ?ih ?p -⌋ < ?t |- _] => 
    let pTp := type of p in
    let pKind := type of pTp in
    eq_fail pKind Prop; (* this condition ensures that ih is an application of an induction hypothesis *)
    let H := fresh "H" in
    pose proof (exist _ (ih p) eq_refl) as H;
    let ih := fresh "IH" in
    let eq := fresh "eqn" in
    destruct H as [ih eq];
    rewrite eq in h;
    clear eq;
    let q := fresh "ih_ref" in
    destruct ih as [ih q];
    autorewrite with fix_notation_hints in h

  (* | [ h: ?rel ⌊ ?ih ?p -⌋ ?t |- _] => isIntComp rel; 
    let pTp := type of p in
    let pKind := type of pTp in
    eq_fail pKind Prop; (* this condition ensures that ih is an application of an induction hypothesis *)
    let H := fresh "H" in
    pose proof (exist _ (ih p) eq_refl) as H;
    let ih := fresh "IH" in
    let eq := fresh "eqn" in
    destruct H as [ih eq];
    rewrite eq in h;
    clear eq;
    let q := fresh "ih_ref" in
    destruct ih as [ih q];
    autorewrite with fix_notation_hints in h *)

  | [h: ?a -> ?c |- _] => match goal with
    | [g: a |- _] => specialize (h g)
  end
  | [h: ?a <-> ?c |- _] => destruct h
  | [h: ?x <> ?y |- ?c ?x <> ?c ?y] =>
    injection; now apply h
  | [h: ?x = ?y |- ?c ?x = ?c ?y] =>
    injection; now apply h
  | [ h: ?c ?s = ?c ?t |- _] => 
      assert (forall v v', c v = c v' -> v = v') as _ by (intros ? ?; injection 1; intros; assumption);
      injection h as ?
  | [ h: ?c ?s <> ?c ?t |- _] => 
    assert (forall v v', c v = c v' -> v = v') as _ by (intros ? ?; injection 1; intros; assumption);
    assert (s <> t) by (intros ->; now apply h); clear h
  | [ h: ?c ?s = ?c ?t -> False |- _] => 
    assert (forall v v', c v = c v' -> v = v') as _ by (intros ? ?; injection 1; intros; assumption);
    assert (s <> t) by (intros ->; now apply h); clear h
  | [h: forall (_:?tp) (_:?p), False |- False] => match goal with
    | [h2: p |- _] => specialize h with (2 := h2)
    end
  | [h: (?s = ?t -> False) -> _ |- _] => match goal with
    | [h2: s <> t |- _] => specialize (h h2)
    end
  | [ |- ?H <-> ?K] => split
  | [h1: ?s <> ?t |- _] => match goal with
    | [h2: s = t |- _] => apply h1 in h2
    end
  (* if we have to synthesize a term of singleton type *)
  | [ |- {x: ?A | x = ?t} ] => exact (exist _ t eq_refl)
  | [ |- {x: ?A | ?t = x} ] => exact (exist _ t eq_refl)
  (* destruct refined variables *)
  | [ x:{x':?a | ?r} |- _ ] => 
    let xp := fresh "xp" in
    destruct x
  | [ |- is_true (negb (?s ==? ?t))] =>
    apply isTrue_neg; apply (pr1 (eqb_false s t))
  | [ |- {_: Unit | _} ] => refine (exist _ unit _)
  | [ |- True -> ?p ] => intros _
  | [h: ?t = ?t /\ _ |- _] => destruct h as [_ h]
  | [h: false = true /\ _ \/ _ |- _] => destruct h as [h | h]; [exfalso; destruct h; now unshelve intuition|]
  | [h: true = false /\ _ \/ _ |- _] => destruct h as [h | h]; [exfalso; destruct h; now unshelve intuition|]
  | [h: _ \/ false = true /\ _ |- _] => destruct h as [h | h]; [|exfalso; destruct h; now unshelve intuition]
  | [h: _ \/ true = false /\ _ |- _] => destruct h as [h | h]; [|exfalso; destruct h; now unshelve intuition]

  | |- (?l && ?r) = true => rewrite andb_true
  | [h: (?l && ?r) = true |- _] => rewrite andb_true in h
  | [h: (?w + ?z == ?x + ?z + ?y) |- _] => replace (x + z + y) with (x + y + z) in h by lia
  | [h: (?x ==? ?y) = true |- _ ] => isVar x; rewrite <- generic_equalb_eq in h; first [subst x | rewrite h in *; rewrite generic_equalb_eq in h]
  | [h: (?x =? ?y) = true |- _ ] => isVar x; rewrite Z.eqb_eq in h; first [subst x | rewrite h in *; rewrite <- Z.eqb_eq in h]
  | [h: (?x ==? ?tm) = true |- _ ] => isVar x; rewrite <- eqb_true in h; first [subst x | rewrite h in *; rewrite generic_equalb_eq in h]
  | [h: (?s ==? ?t) = true |- _ ] => rewrite <- eqb_true in h
  | [h: ?x == ?tm |- _ ] => isVar x; rewrite <- generic_equalb_eq in h; first [subst x | rewrite h in *; rewrite generic_equalb_eq in h]
  | [h: ?tm == ?x |- _ ] => isVar x; rewrite <- generic_equalb_eq in h; first [symmetry in h; subst x | rewrite h in *; rewrite generic_equalb_eq in h]| |- (?s ==? ?t) = true => rewrite <- eqb_true
  | |- (?s == ?t) => rewrite <- generic_equalb_eq
  | [h: ?tm <> ?tm |- False] => apply h; reflexivity
  | [h: ?x = ?tm |- _ ] => isVar x; first [subst x | rewrite h in *]
  | [h: forall (_:?tm <> ?tm), _ |- _] => clear h

  (*
  | [wff_hint : _ ?tm /\ _ |- _] => (* assert_fails (isVar tm); *)
    let wff_c_hint := fresh "wff_cr_" in
    destruct wff_hint as [wff_c_hint wff_hint];
    progress (simpl in wff_c_hint);
    match goal with
    | |- _ /\ _ => split; [timeout 1 apply wff_c_hint|];
      try now inversion wff_hint
    | _ => idtac
    end *)
  | [h: _ /\ True |- _] => first [
    destruct h as [h _] |
    let temp := fresh "temp_triv_" in
    destruct h as [h temp]; 
    try replace temp with I in * by (auto with pi_db); 
    try clear temp]

  | |- (false = true /\ _) \/ (negb false = true /\ _) => 
    right; split; [reflexivity|]
  | |- (false = true /\ _) \/ (true = true /\ _) => 
    right; split; [reflexivity|]
  | |- (true = true /\ _) \/ (true = false /\ _) => 
    left; split; [reflexivity|]
  | |- ((?s ==? ?t) = true /\ _) \/ ((?s /=? ?t) = true /\ _) => 
    let H := fresh "H" in
    tryif (assert ((s ==? t) = true) as H by (repeat shape_based; timeout 1 solve [lia | unshelve intuition]))
      then (
        idtac "Able to prove (" s " ==? " t ") = true using lia or intuition tactic, choosing left disjunct (of goal) and filling in proof for its first conjunct. ";
        left; split; [apply H|]
      ) else (
        assert ((s /=? t) = true) as H by (repeat shape_based; timeout 1 solve [lia | unshelve intuition]);
        idtac "Able to prove (" s " /=? " t " ) = true using lia or intuition tactic, choosing left disjunct (of goal) and filling in proof for its first conjunct. ";
        right; split; [apply H|]
      )
  | |- (?c = true /\ _) \/ (?c = false /\ _) => 
    let H := fresh "H" in
    tryif (assert (c = true) as H by (repeat shape_based; timeout 1 solve [lia | unshelve intuition]))
      then (
        idtac "Able to prove (" c " = true) using lia or intuition tactic, choosing left disjunct (of goal) and filling in proof for its first conjunct. ";
        left; split; [apply H|]
      ) else (
        assert (c = false) as H by (repeat shape_based; timeout 1 solve [lia | unshelve intuition]);
        idtac "Able to prove (" c " = false) using lia or intuition tactic, choosing left disjunct (of goal) and filling in proof for its first conjunct. ";
        right; split; [apply H|]
      )
  | [h: ?c |- ?c \/ ?d] => left; apply h
  | [h: ?d |- ?c \/ ?d] => left; apply h
  | [h: ?c \/ ?d |- ?g] => 
      match g with
      | _ -> False => fail
      | False => fail
      | _ => idtac
      end;
      let temp := fresh "H" in
      first [
        assert (c -> False) as temp by (fast_done); destruct h;
        [exfalso; apply temp in h; now apply h|] |
        assert (d -> False) as temp by (fast_done); destruct h;
        [|exfalso; apply temp in h; now apply h]
      ]
  | |- ?c \/ ?d => 
      let temp := fresh "H" in
      first [
        assert (c -> False) as temp by (intro; repeat shape_based; fast_done); right |
        assert (d -> False) as temp by (intro; repeat shape_based; fast_done); left];
      clear temp
  (*| |- exists v, ?relAp v => solve [unshelve (eexists _; econstructor; assumption)]*)
  | |- exists v, ?relAp v /\ v = ?t => exists t; split; [|reflexivity]
  | |- _ => intro
  end.

Ltac simpl_exists tm := 
  let temp := fresh "temp" in
  pose tm as temp;
  repeat progress (autorewrite with lia_rewrites in temp);
  exists temp;
  subst temp.

Ltac simpl_specialize h tm := 
  let temp := fresh "temp" in
  pose tm as temp;
  repeat progress (autorewrite with lia_rewrites in temp);
  specialize (h temp);
  subst temp.

Ltac instantiate_lia_goal := 
  match goal with
    | |- exists (z:Z), subZ_rel ?s ?t z -> _ => simpl_exists (s - t)
    | |- exists (z:Z), addZ_rel ?s ?t z -> _ => simpl_exists (s + t)
    | |- exists (z:Z), subZ_rel ?s ?t z /\ _ => simpl_exists (s - t);
      try (split; [constructor|])
    | |- exists (z:Z), addZ_rel ?s ?t z /\ _ => simpl_exists (s + t);
      try (split; [constructor|])
    | _ => fail "Goal doesn't contain existentially quantified variables we can instantiate"
  end.

Ltac instantiates_lia_goal := repeat progress instantiate_lia_goal.

Ltac final_shape_based := match goal with
  | |- {_: Unit | _} => unshelve refine (exist _ unit _)
  | [e: ⌊ ?ihAppl -⌋ = ?uterm |- _] => match ihAppl with
    | _ _ => 
      let term := fresh "term" in
      let termWf := fresh "termWf" in
      set ihAppl as term in *;
      pose proof ⌈ ihAppl ⌉ as termWf;
      rewrite e in termWf;
      unfold term in termWf;
      simpl in termWf;
      let termWfTp := type of termWf in
      tryif (match goal with
      | [wf2: ?tp |- _] => eq_fail tp termWfTp; eq_fail wf2 termWfTp
      end) then fail else idtac
    end
  | [h: ?s == ?t |- _] => solve [exfalso; rewrite <- eqb_eq in h; 
    let ineq := fresh "ineq" in
    assert (s <> t) as ineq by fast_done;
    exact (ineq h)]
  (*
  (* here we have to synthesize a refined term, there is no way we can generically manage that (let alone choose the right term), 
  however this should only ever show up in the translation in branches that are anyways impossible, so we might as well use exfalso *)
  | [ |- {_: _ | _} ] => idtac "We need to synthesize a refined term, but it's unclear which term to pick, giving up and trying to prove a contradiction!"; exfalso
  *)
  end.

Create HintDb fix_notation_hints.
Lemma fix_notation [A:Type] [P: A -> Prop] (tm: {v: A | P v}): ⌊ tm _⌋ = ⌊ tm -⌋.
Proof.
  reflexivity.
Qed. 
Global Lemma fix_notation' [A:Type] [P: A -> Prop] (tm: {v: A | P v}): ` tm = ⌊ tm -⌋.
Proof.
  reflexivity.
Qed. 

#[global] Hint Rewrite fix_notation:fix_notation_hints. 
Tactic Notation "simpl_opaque" constr_list(fs) := unfold proj1_sig in *; cbv beta delta -[fs] in *; autorewrite with fix_notation_hints in *; fold proj1_sig in *.

#[global] Hint Rewrite negb_involutive:fix_notation_hints.

(* autorewriting only using this lemma is actually marginally slower than directly using 
  cbv beta delta [proj1_sig] in * and autorewriting by the above lemma. 
  However, we still need this lemma, to make sure terms of shape ⌊ exist _ tm _ -⌋ are simplified, 
  as the cleanup steps rely on this assumption *)
Local Lemma proj_ex [A: Type] (P : A -> Prop) (tm : A) (z:P tm): proj1_sig (exist P tm z) = tm.
Proof.
  reflexivity.
Qed.
Local Lemma proj_ex' [A: Type] [P : A -> Prop] (tm : A) (z:P tm): ⌊ exist P tm z _⌋ = tm.
Proof.
  reflexivity.
Qed.
Lemma proj_ex'' [A: Type] [P : A -> Prop] (tm : A) (z:P tm): ⌊ exist P tm z -⌋ = tm.
Proof.
  reflexivity.
Qed.

Local Lemma ex_proj [A: Type] [P : A -> Prop] (tm : {v:A | P v}): (exist P ⌊ tm -⌋ ⌈ tm ⌉) = tm.
Proof.
  destruct tm as [v wit]. reflexivity.
Qed.
#[global] Hint Rewrite ex_proj:fix_notation_hints. 
#[global] Hint Rewrite proj_ex:fix_notation_hints.
#[global] Hint Rewrite proj_ex':fix_notation_hints.
#[global] Hint Rewrite proj_ex'':fix_notation_hints.
Local Lemma ex_proj' [A: Type] [P : A -> Prop] (tm : {v:A | P v}): (exist P ⌊ tm _⌋ ⌈ tm ⌉) = tm.
Proof.
  destruct tm as [v wit]. reflexivity.
Qed.
#[global] Hint Rewrite ex_proj':fix_notation_hints. 

Lemma proj_subCast [A: Type] [G:A -> Prop] (H: A -> Prop) (tm: {x: A | G x}) (p: G (` tm) -> H (` tm)): ⌊ @subsumptionCast A G H tm p -⌋ = ⌊ tm -⌋.
Proof.
  reflexivity.
Qed.
#[global] Hint Rewrite proj_subCast:fix_notation_hints. 

Lemma proj_subCast' [A: Type] [G:A -> Prop] (H: A -> Prop) (tm: {x: A | G x}) (p: G (` tm) -> H (` tm)): ⌊ @subsumptionCast A G H tm p _⌋ = ⌊ tm -⌋.
Proof.
  reflexivity.
Qed.
#[global] Hint Rewrite proj_subCast':fix_notation_hints. 

Lemma negb_false : negb false = true.
Proof. 
  reflexivity.
Qed.
#[global] Hint Rewrite negb_false:fix_notation_hints. 

Lemma proj_if [A:Type] [P:A->Prop] (c:bool) (s: {v : A | P v}) (t: {v : A | P v}): ⌊ (if c then s else t) -⌋ = (if c then ⌊ s -⌋ else ⌊ t -⌋).
Proof.
  now destruct c.
Qed.
#[global] Hint Rewrite proj_if:fix_notation_hints. 
Lemma proj_dependent_if [A:Type] [P:A->Prop] (c:bool) 
  (s: c = true -> {v : A | P v}) (t: c = false -> {v : A | P v}) z: 
  ⌊ (if c as b return (c = b -> {v : A | P v}) then s else t) z -⌋ = (if c as b return (c = b -> A) then fun e => ⌊ s e -⌋ else fun e => ⌊ t e -⌋) z.
Proof.
  now destruct c.
Qed.
#[global] Hint Rewrite proj_dependent_if:fix_notation_hints. 

(*
Lemma proj_False_rect (A:Type) (P:A->Prop) (f:False): ⌊ False_rect {v : A | P v} f -⌋ = match f return A with end.
Proof.
  easy.
Qed.
#[global] Hint Rewrite proj_False_rect:fix_notation_hints. *)

Create HintDb apply_id_hints.
Lemma apply_if_tt [A:Type] [c:bool] [s t: A]: c = true -> (if c then s else t) = s.
Proof.
  now destruct c.
Qed.
#[global] Hint Resolve apply_if_tt:apply_id_hints. 

Lemma apply_if_ff [A:Type] [c:bool] [s t: A]: c = false -> (if c then s else t) = t.
Proof.
  now destruct c.
Qed.
#[global] Hint Resolve apply_if_ff:apply_id_hints. 

Require Import Logic.ProofIrrelevanceFacts.
#[global] Hint Resolve proof_irrelevance : pi_db.

Lemma apply_dependent_if_tt [A:Type] [c:bool] [s: c = true -> A] [t:c = false -> A] (h: c = true) {z:_}: (if c as b return (c = b -> A) then s else t) z = s h.
Proof.
  destruct c; try easy; try f_equal; auto with pi_db. 
Qed.
#[global] Hint Resolve apply_dependent_if_tt:apply_id_hints. 
Lemma apply_dependent_if_ff [A:Type] [c:bool] [s: c = true -> A] [t:c = false -> A] (h: c = false) {z:_}: (if c as b return (c = b -> A) then s else t) z = t h.
Proof.
  destruct c; try easy; try f_equal; auto with pi_db. 
Qed.
#[global] Hint Resolve apply_dependent_if_ff:apply_id_hints.
Ltac apply_ifs :=
  repeat progress (match goal with
    | [h:?c = true |- _] => rewrite (apply_if_tt h) in *
    | [h:?c = true |- _] => rewrite (apply_dependent_if_tt h) in *
    | [h:?c = false |- _] => rewrite (apply_if_ff h) in *
    | [h:?c = false |- _] => rewrite (apply_dependent_if_ff h) in *
    end
  ).

Ltac fix_notations := repeat progress autorewrite with fix_notation_hints in *.

Ltac simpl_proj := try fix_notations; (* (fix_notations; 
  unfold proj1_sig in *; fold proj1_sig in *; unfold False_rec in *;
  cbv beta delta [proj1_sig] in *; autorewrite with fix_notation_hints in * ); *)
  try (repeat progress autounfold with ref_constr_db in *; progress (autorewrite with fix_notation_hints in * )).

(* Linear arithmetic rewrites *)
Create HintDb lia_rewrites.
Local Lemma plus_lt_z (s t:Z): s + t < 0 <-> s < -t.
Proof. lia. Qed.
#[global] Hint Rewrite plus_lt_z:lia_rewrites.
Local Lemma minus_lt_z (s t:Z): s - t < 0 <-> s < t.
Proof. lia. Qed.
#[global] Hint Rewrite minus_lt_z:lia_rewrites.
Local Lemma z_lt_minus (s t:Z): 0 < s - t <-> t < s.
Proof. lia. Qed.
#[global] Hint Rewrite z_lt_minus:lia_rewrites.
Local Lemma z_lt_plus (s t:Z): 0 < s + t <-> -t < s.
Proof. lia. Qed.
#[global] Hint Rewrite z_lt_plus:lia_rewrites.
Local Lemma plus_le_z (s t:Z): s + t <= 0 <-> s <= -t.
Proof. lia. Qed.
#[global] Hint Rewrite plus_le_z:lia_rewrites.
Local Lemma minus_le_z (s t:Z): s - t <= 0 <-> s <= t.
Proof. lia. Qed.
#[global] Hint Rewrite minus_le_z:lia_rewrites.
Local Lemma z_le_minus (s t:Z): 0 <= s - t <-> t <= s.
Proof. lia. Qed.
#[global] Hint Rewrite z_le_minus:lia_rewrites.
Local Lemma z_le_plus (s t:Z): 0 <= s + t <-> -t <= s.
Proof. lia. Qed.
#[global] Hint Rewrite z_le_plus:lia_rewrites.

Local Lemma ltb_true (s t:Z): s <? t = true <-> s < t.
Proof.
  split; intro H; lia. 
Qed.
#[global] Hint Rewrite ltb_true:lia_rewrites.

Local Lemma leb_true (s t:Z): s <=? t = true <-> s <= t.
Proof.
  split; intro H; lia.
Qed.
#[global] Hint Rewrite leb_true:lia_rewrites.

Local Lemma gtb_true (s t:Z): s >? t = true <-> s > t.
Proof.
  split; intro H; lia. 
Qed.
#[global] Hint Rewrite gtb_true:lia_rewrites.

Local Lemma geb_true (s t:Z): s >=? t = true <-> s >= t.
Proof.
  split; intro H; lia.
Qed.
#[global] Hint Rewrite geb_true:lia_rewrites.


Local Lemma plus_zero (s: Z): s + 0 = s.
Proof. 
  lia.
Qed.
#[global] Hint Rewrite plus_zero:lia_rewrites.
Local Lemma plus_sub (s t: Z): (s + t) - t = s.
Proof. 
  lia.
Qed.
#[global] Hint Rewrite plus_sub:lia_rewrites.
Local Lemma plus_sub' (s t u: Z): (s + (t + u)) - t = s + u.
Proof. 
  lia.
Qed.
#[global] Hint Rewrite plus_sub':lia_rewrites.
Local Lemma plus_sub'' (s t u: Z): (s + (t + u)) - u = s + t.
Proof. 
  lia.
Qed.
#[global] Hint Rewrite plus_sub'':lia_rewrites.
Local Lemma plus_r' (s t u: Z): s + u == t + u -> s = t.
Proof.
  intros H.
  rewrite <- eqb_eq in H.
  assert (s + u - u = t + u - u) by (now rewrite H).
  now autorewrite with lia_rewrites in H0. 
Qed.
#[global] Hint Rewrite plus_r':lia_rewrites.
Local Lemma plus_one_assoc (s t:Z): s + (t + 1) = (s + t) + 1.
Proof.
  lia.
Qed.
#[global] Hint Rewrite plus_one_assoc:lia_rewrites.

Ltac simpl_ref_constr := repeat progress autounfold with ref_constr_db get_rel_db in *.
Ltac lia_simpl_step := first [progress autounfold with lia_unfold get_rel_db in * | progress autorewrite with fix_notation_hints lia_rewrites in *].
Ltac lia_simpl := repeat lia_simpl_step.
Ltac quick_cleanup := simpl_ref_constr; 
  simpl_proj; apply_ifs; 
  try (lia_simpl; simpl_proj).
Ltac quick_simpl := quick_cleanup;  repeat shape_based.

Ltac cleanup_hints := match goal with
  | [hint: {_: Unit | ?r} |- _ ] => destruct hint as [_ hint]
  | [hint: {x: ?A | ?r} |- _ ] => 
    let hint_r := fresh "hint_r" in
    destruct hint as [hint hint_r]
  | [ h: ?s == ?t |- _] => idtac h; rewrite <- generic_equalb_eq in h
  end.

Ltac simpl_hyp := match goal with
  | [hint : _ |- _] => progress (timeout 1 simpl in hint)
  end.

Ltac simpl_loop :=
  repeat first
    [ fast_done
    | f_equal_ind
    | progress unshelve eauto with wff_constr_db
    | solve [progress unshelve intuition; fast_done]
    | solve [trivial]
    | progress shape_based
    | solve [symmetry; fast_done]
    | discriminate
    | contradiction
    | progress unshelve intuition discriminate
    | progress subst
    | progress simpl
    | simpl_hyp
    | progress autorewrite with lia_rewrites fix_notation_hints in *
    | split_hyp
    | progress (timeout 6 simpl in * )
    (*| timeout 1 (unshelve smt)*)
    | split
    | left; simpl_loop
    | right; simpl_loop
    ].

Ltac quicksolve := (* try (progress unshelve intuition; timeout 1 quicksolve); *)
  solve [ 
    quick_wff_wit 
    | quick_simpl; try (final_shape_based; repeat final_shape_based; subst; quick_simpl); subst; simpl_loop
  ].
#[global] Hint Extern 20 () => quicksolve : quicksolve_db. 

(* Finish a unification subgoals with f_equal, reflexivity and proof_irrelevance *)
Ltac solve_pi_unif_subgoal := cbn; simpl_proj; repeat f_equal; auto with pi_db.

Ltac isIntComp rel :=
  let temp := fresh "temp" in
  assert (rel = rel) as temp by reflexivity;
  match type of temp with
  | Z.leb = _=> idtac
  | Z.ltb = _ => idtac
  | Z.gtb = _ => idtac
  | Z.eqb = _ => idtac
  | Z.lt = _ => idtac
  | Z.le = _ => idtac
  | Z.gt = _ => idtac
  | Z.ge = _ => idtac
  | Z.eq = _ => idtac
  | _ => fail
  end.