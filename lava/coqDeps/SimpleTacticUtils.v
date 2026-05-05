Load QuickTacs.
Tactic Notation "do_nonbranching" tactic(t) :=
  let n := numgoals in
  tryif t; let m := numgoals in guard m = n then idtac else fail "Tactic " t " produces additional subgoals".

Ltac protectEqnHyps :=
  repeat (
    match goal with
    | [ h: ?v = ?t |- _ ] => 
      let h' := fresh "temp" in
      assert (True -> v = t) as h' by (intros; exact h);
      first [clear h | rewrite h with (h' I) in * by (auto with pi_db); clear h];
      assert (True -> v = t) as h by (exact h');
      first [clear h' | rewrite (h' I) with (h I) in * by (auto with pi_db); clear h']
    end
  ).
Ltac restoreEqnHyps :=
  repeat (
    match goal with
    | [ h: True -> ?v = ?t |- _ ] => 
      let h' := fresh "temp" in
      assert (v = t) as h' by (exact (h I));
      first [clear h | rewrite (h I) with h' by (auto with pi_db); clear h];
      assert (v = t) as h by (apply h');
      first [clear h' | rewrite h' with h by (auto with pi_db); clear h']
    end
  ).

Ltac propKinded tm :=
  let tmTp := type of tm in
  let tmKind := type of tmTp in
  eq_fail tmKind Prop (*tryif (eq_fail tmKind Prop) then idtac else (idtac "term " tm " isn't Prop-kinded"; fail)*).
Ltac typeKinded tm :=
  let tmTp := type of tm in
  let tmKind := type of tmTp in
  eq_fail tmKind Type (*tryif (eq_fail tmKind Prop) then idtac else (idtac "term " tm " isn't Prop-kinded"; fail)*).


Global Tactic Notation "cleanup_inversion" tactic(invTac) hyp(h) := 
  protectEqnHyps; invTac; 
  repeat (match goal with
  | [eqV: ?tp = ?v |- _] => typeKinded tp; apply eq_sym in eqV; subst
  | [existEq: @existT Type ?P ?X ?p = @existT Type ?P ?X ?q |- _] => fail 
  end); restoreEqnHyps; clear h.

Global Tactic Notation "clean_inversion" tactic(invTac) hyp(h) := 
  match type of h with
  | ?f_rel_ap ?v => protectEqnHyps; invTac; 
    match goal with
    | [eqV: ?tm = v |- _] => apply eq_sym in eqV; subst; clear h
    | _ => (* idtac "Cannot find final generated equality of inversion tactic to switch. "; *) subst; clear h
    end; restoreEqnHyps
  | ?tp => fail "Hypothesis to invert is not of expected shape, but has shape " tp 
  end.

Global Ltac strong_inversion h := first [clean_inversion (inversion h) h | clean_inversion (dependent inversion h) h].
Ltac intro_inv := 
  let h := fresh "H" in
  intros h; strong_inversion h.

Tactic Notation "repeat_or_fail" tactic(tac) := tryif tac then repeat tac else fail. 

Global Tactic Notation "assRefl" constr(x) "as" ident(Res) :=
  assert (x = x) as Res by reflexivity; subst x.

Local Tactic Notation "first_sucessful" tactic(t) tactic(t') := tryif t then idtac else t'.

(* find a subexpression satisfying tactic P in exp and pose in as Res *)
Ltac findSubExpr Res P exp :=
  (* idtac "Calling findSubExpr on term " exp; *)
  tryif P exp then 
      return Res exp
      else 
  (match exp with
    | ?f ?t => first_sucessful (findSubExpr Res P f) (findSubExpr Res P t)
    | ?a -> ?c => first_sucessful (findSubExpr Res P a) (findSubExpr Res P c)
    | forall (v:_), ?b => findSubExpr Res P b
    | forall (v:_), ?rel v -> ?b => first [findSubExpr Res P rel | findSubExpr Res P b]
    | forall (v:?aT), ?b => first_sucessful (findSubExpr Res P aT) (findSubExpr Res P b)
    | fun (_:?aT) => ?b => first_sucessful (findSubExpr Res P aT) (findSubExpr Res P b)
    | ?s = ?t => first_sucessful (findSubExpr Res P s) (findSubExpr Res P t)
    | ?s <-> ?t => first_sucessful (findSubExpr Res P s) (findSubExpr Res P t)
    | ?s /\ ?t => first_sucessful (findSubExpr Res P s) (findSubExpr Res P t)
    | ?s \/ ?t => first_sucessful (findSubExpr Res P s) (findSubExpr Res P t)
    | _ => fail (* "term doesn't have a matching subterm" exp *)
  end)
  (*; idtac "Finished computing findSubExpr " exp Res;
  print_res Res *).