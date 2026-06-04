Load GetRelInterface.
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
    | exists (v:?aT), _ => findSubExpr Res P aT
    | exists (v:_), ?b => findSubExpr Res P b
    | exists (v:_), ?rel v /\ ?b => first [findSubExpr Res P rel | findSubExpr Res P b]
    | forall (v:?aT), _ => findSubExpr Res P aT
    | forall (v:_), ?b => findSubExpr Res P b
    | forall (v:_), ?rel v -> ?b => first [findSubExpr Res P rel | findSubExpr Res P b]
    | fun (_:?aT) => ?b => first_sucessful (findSubExpr Res P aT) (findSubExpr Res P b)
    | ?s = ?t => first_sucessful (findSubExpr Res P s) (findSubExpr Res P t)
    | ?s <-> ?t => first_sucessful (findSubExpr Res P s) (findSubExpr Res P t)
    | ?s /\ ?t => first_sucessful (findSubExpr Res P s) (findSubExpr Res P t)
    | ?s \/ ?t => first_sucessful (findSubExpr Res P s) (findSubExpr Res P t)
    | _ => fail (* "term doesn't have a matching subterm" exp *)
  end)
  (*; idtac "Finished computing findSubExpr " exp Res;
  print_res Res *).

(* destructs a function application exp into a pair of shape (f, (t1, (t2, ... (tn, tt)))) and pose it as Res *)
Ltac destrApp exp Res := 
  match exp with
  | ?f' ?t' => 
    prepend_res Res t'; destrApp f' Res
  | _ => prepend_res Res (exp _::_ _nil)
  end.

Inductive LookupItems : Set :=
  | rel : LookupItems
  | rwLem : LookupItems
  | functionhood : LookupItems.
Class dictionary (item: LookupItems) {A : Type} (a : A) := { 
  ty : Type; 
  lookup' : ty
}.
Definition lookup item {A:Type} a {instance : dictionary item a}: ty := (@lookup' item A a) instance.

Class getFunc {B: Type} (b:B) := {
  f_tp : Type;
  getF' : f_tp
}.
Definition getF {B:Type} (b:B) {instance: getFunc b}: f_tp := (@getF' B b) instance.

Ltac test_term tm := 
  let temp := fresh "temp" in
  pose tm as temp;
  clear temp.

Ltac localLookupRel f Res :=
  match type of f with
  | forall (args:ArgList ?argTps), ?rTp =>
    match goal with
    | [f_frel: forall (args: ArgList argTps) v, ⌊ f args -⌋ = v <-> ?frel _ v |- _] =>
      pose frel as Res
    end
  end.
Ltac localLookupFunct rel Res :=
  match goal with
  | [funct: forall (uargs : UArgList _) (v v' : Z), rel uargs v -> rel uargs v' -> v = v' |- _] =>
    pose rel as Res
  end.

Ltac hasLocalRel f :=
  let res := fresh "res" in
  localLookupRel f res;
  try clear res.

Ltac has_rel f := first [test_term (lookup rel f) | hasLocalRel f].
Ltac has_no_rel f := tryif (has_rel f) then fail else idtac.


Ltac localLookupFunc rel Res :=
  match type of rel with
  | forall (_:UArgList ?uargTps) (_:?T), Prop =>
    match goal with
    | [f_frel: forall (args: ArgList ?argTps) (v: T), ⌊ ?f args -⌋ = v <-> rel _ v |- _] =>
      pose f as Res
    end
  end.
Ltac localIsRel rel :=
  let res := fresh "res" in
  localLookupFunc rel res;
  try clear res.

Ltac is_rel f_rel := first [test_term (getF f_rel) | localIsRel f_rel].
Ltac is_no_rel f_rel := tryif (test_term (getF f_rel)) then fail else idtac.

Ltac isRelAppl fApplV :=
  let fAppl := fresh "fAppl" in
  pose fApplV as fAppl; try unfold fApplV in fAppl;
  let fApplRefl := fresh "fApplRefl" in
  assRefl fAppl as fApplRefl;
  match type of fApplRefl with
  | ?fApp = _ => clear fApplRefl; 
    let fAppD := fresh "fAppD" in
    destrApp fApp fAppD;
    let fAppRefl := fresh "fAppRefl" in
    assRefl fAppD as fAppRefl;
    match type of fAppRefl with
    | ((?f_rel _::_ _nil) _::_ _) = _ => clear fAppRefl; is_rel f_rel
    end
  end.