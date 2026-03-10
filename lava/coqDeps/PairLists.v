Require Import Init.Datatypes (tt).
Tactic Notation "print_res" hyp(Res) := 
  let resTp := type of Res in
  let temp := fresh "temp" in
  assert (Res = Res) as temp by reflexivity; unfold Res in temp; 
  match type of temp with
  | ?res = _ => idtac Res ":=" res ": " resTp
  end; clear temp.

Tactic Notation "return" ident(Res) constr(res) :=
    pose res as Res.

Definition _nil := tt. 
Notation "res _::_ tl" := (res, (tl)) (right associativity, at level 51 ).

Tactic Notation "prepend_res" ident(Res) constr(res) :=
  let temp := fresh "temp" in
  tryif (
    match type of Res with
     | _ => idtac
    end) then pose (res _::_ Res) as temp; subst Res; pose temp as Res; subst temp else pose (res _::_ _nil) as Res. 

Tactic Notation "initialize_res" ident(Res) constr(res) :=
  let temp := fresh "temp" in
  tryif (
    match type of Res with
     | _ => idtac
    end) then idtac else pose res as Res.
  

Tactic Notation "head_res" hyp(Res) ident(Res2) :=
  let temp := fresh "temp" in
  assert (Res = Res) as temp by reflexivity; unfold Res in temp; 
  match type of temp with
  | (?hd _::_ ?tl) = _ => return Res2 hd
  | _ => fail
  end; try clear temp.

Tactic Notation "tail_res" hyp(Res) ident(Res2) :=
  let temp := fresh "temp" in
  assert (Res = Res) as temp by reflexivity; unfold Res in temp; 
  match type of temp with
  | (?hd _::_ ?tl) = _ => return Res2 tl
  | _ => fail
  end; clear temp.

Ltac _map f plist Res2 :=
  return Res2 _nil;
  match plist with
  | ?hd _::_ ?tl => _map f tl Res2; prepend_res Res2 (f hd)
  | _nil => idtac
  end.

Tactic Notation "map_res" constr(f) hyp(Res) :=
  let temp := fresh "temp" in
  assert (Res = Res) as temp by reflexivity; subst Res; 
  match type of temp with
  | ?plist = _ => _map f plist Res
  | _ => fail
  end; clear temp.

Ltac pinit plist Res2 :=
    match plist with
    | _nil => fail "init of empty list"
    | ?tm _::_ _nil => _nil
    | ?hd _::_ ?tl => pinit tl Res2; prepend_res Res2 hd
    end.

Tactic Notation "init_res" hyp(Res) ident(Res2) :=
  let temp := fresh "temp" in
  assert (Res = Res) as temp by reflexivity; unfold Res in temp; 
  match type of temp with
  | ?tm = _ => pinit tm Res2
  end; clear temp.


Ltac plast plist Res2 :=
    match plist with
    | _nil => fail "last of empty list"
    | ?tm _::_ _nil => return Res2 tm
    | ?hd _::_ ?tl => plast tl Res2
    end.

Tactic Notation "last_res" hyp(Res) ident(Res2) :=
  let temp := fresh "temp" in
  assert (Res = Res) as temp by reflexivity; unfold Res in temp; 
  match type of temp with
  | ?tm = _ => plast tm Res2
  end; clear temp.

Ltac eq_fail s t :=
  tryif (assert (s = t) as _ by reflexivity) then idtac else fail.

Ltac neq_fail s t :=
  tryif (assert (s = t) as _ by reflexivity) then fail else idtac.

Ltac _any P plist :=
  match plist with
  | _nil => fail
  | ?hd _::_ ?tl => tryif P hd then idtac else _any P tl
  end.

Ltac _all P plist :=
  match plist with
  | _nil => fail
  | ?hd _::_ ?tl => P hd; _any P tl
  end.

Ltac _find P plist Res :=
  match plist with
  | _nil => fail
  | ?hd _::_ ?tl => tryif P hd then return Res hd else _find P tl Res
  end.

Ltac _foreach tac plist :=
  match plist with
  | _nil => idtac
  | ?hd _::_ ?tl => tac hd; _foreach tac tl
  end.

(* runs tactic tac on each value in the list posed as Res, consumes Res *)
Ltac foreach_r tac Res :=
    let tempEq := fresh "tempEq" in
    assert (Res = Res) as tempEq by reflexivity;
    subst Res; 
    match type of tempEq with
    | ?plist = _ => clear tempEq; _foreach tac plist
    end.

Tactic Notation "foreach_t" tactic(tac) hyp(Res) := foreach_r tac Res.

Ltac _contains tm plist := 
  match plist with
  | _nil => fail
  | ?hd _::_ ?tl => tryif eq_fail tm hd then idtac else _contains tm tl
  end.

Ltac _reverse plist Res :=
  match plist with
  | _nil => try (return Res _nil)
  | ?hd _::_ ?tl => prepend_res Res hd; _reverse tl Res
  end.

Ltac reverse_res Res :=
  let H := fresh "H" in
  assert (Res = Res) as H by reflexivity; subst Res; 
  match type of H with
  | ?tm = _ => _reverse tm Res
  end; clear H.
  

Tactic Notation "contains_res" constr(tm) hyp(Res) :=
  let temp := fresh "temp" in
  assert (Res = Res) as temp by reflexivity; unfold Res in temp; 
  match type of temp with
  | ?plist = _ => _contains tm plist
  end; clear temp.

Ltac compose_tacs_res t1 t2 Res := t2 Res; t1 Res.

(* find all hypothesis satisfying tactic P and pose them as Res (in reverse order) *)
Tactic Notation "findHyps_res" tactic(P) ident(Res) :=
  repeat (
    match goal with
    | [h : _ |- _] => tryif P h then prepend_res Res h else fail
    end
  ).