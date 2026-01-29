Load QuickTacs.

Ltac in_all_hyps tac :=
    repeat match goal with
           | [ H : _ |- _ ] => progress tac H
           end.

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

Global Tactic Notation "assRefl" constr(x) "as" ident(Res) :=
  assert (x = x) as Res by reflexivity; subst x.

Ltac generalize_dependents genVars :=
  match genVars with
  | _nil => idtac
  | ?x _::_ ?tl => 
    tryif (isVar x) then (idtac "running generalize dependent " x; generalize dependent x) else idtac; 
    generalize_dependents tl
  end.

Ltac nested_induction indVars :=
  match indVars with
  | _nil => idtac
  | ?x _::_ ?tl => induction x; 
    match tl with
    | ?y _::_ _ => intro y
    | _ => try intro; 
      repeat (match goal with
      | [ih: forall (_:?pTp), _ |- _] => 
        let wit := fresh "wit" in
        let pKnd := type of pTp in
        eq_fail pKnd Prop;
        do_nonbranching (unshelve refine (let wit := (_ : pTp) in _); 
        [try clear ih; first [quick_wff_wit | quicksolve] |]);
        let witEq := fresh "witEq" in
        assert (wit = wit) as witEq by reflexivity; unfold wit in witEq; 
        match type of witEq with
        | ?witDef = _ => clear witEq; 
          tryif specialize (ih witDef) then idtac else (specialize (ih wit)); 
          idtac "Specializing " ih " with (simple) proof term in nested induction " (* witDef *)
        end
      end)
    end; nested_induction tl
  end.

Ltac destruct_conds conds :=
  let remConds := fresh "remConds" in
  let remCondsRefl := fresh "remCondsRefl" in
  pose conds as remConds;
  
  repeat (
    assRefl remConds as remCondsRefl;
    match type of remCondsRefl with
    | ?cond _::_ ?rConds = _ => clear remCondsRefl; 
      idtac "destructing the condition " cond;
      tryif (
        first [ destruct cond as [|] eqn:? |
          let temp := fresh "temp" in
          assert (cond = true \/ cond = false) as temp by quicksolve;
          destruct temp
        | destruct cond eqn:?
        ]
      ) then idtac else idtac "failed to destruct condition " cond; 
      pose rConds as remConds
    | _nil = _ => clear remCondsRefl; fail
    end
  ); try clear remConds;
  repeat progress (simpl_proj; apply_ifs).

(* we assume that the lemmaVars are already introed into the context *)
Ltac multivariable_induction indVars conds lemmaVars := 
  (* compute the variables genVars that aren't inductive or lemmaVars *)
  let genVars := fresh "genVars" in
  match indVars with
  | _nil => idtac
  | ?x _::_ ?tl => 
    
    let nonGenVars := fresh "nonGenVars" in
    let nonGenVarsRefl := fresh "nonGenVarsRefl" in
    pose tl as nonGenVars;
    pose _nil as genVars;
    repeat (
      match goal with
      | [h:_ |- _ ] => 
        tryif (eq_fail x h) then (idtac (* "no point doing generalize dependent on first inductive variable " x *); fail)
        else (
        tryif (eq_fail nonGenVars h) then (idtac (* "not an original hypothesis " h *); fail) else (
        tryif (eq_fail genVars h) then (idtac (* "not an original hypothesis " h *); fail) else (
        tryif (_contains h lemmaVars) then (idtac (* "not generalizing on lemmaVar " h *); fail) else (
          assRefl nonGenVars as nonGenVarsRefl;
          match type of nonGenVarsRefl with
          | ?vars = _ => clear nonGenVarsRefl; 
            tryif (_contains h vars) then fail else 
            (* idtac "adding hypothesis " h " to the hypothesis to generalize dependent"; *)
            prepend_res genVars h;
            pose (h _::_ vars) as nonGenVars
          end
      ))))
      end
    ); try clear nonGenVars; 
    (* revert the lemmaVars again (in opposite order) *)
    let remLemVars := fresh "remLemVars" in
    let remLemVarsRefl := fresh "remLemVarsRefl" in
    pose lemmaVars as remLemVars;
    reverse_res remLemVars;
    repeat (
      assRefl remLemVars as remLemVarsRefl;
      match type of remLemVarsRefl with
      | ?v _::_ ?rLemVars = _ => clear remLemVarsRefl; 
        (* idtac "reverting back lemmaVar " v; *) try revert v; 
        pose rLemVars as remLemVars
      | _nil = _ => clear remLemVarsRefl; fail
      end
    ); try clear remLemVars;
    reverse_res genVars;
    let genVarsRefl := fresh "genVarsRefl" in
    assRefl genVars as genVarsRefl;
    match type of genVarsRefl with
    | ?gVars = _ => clear genVarsRefl; 
      generalize_dependents gVars
    end;
    generalize_dependents tl; 
    induction x; 
    match tl with
    | ?y _::_ _ => intro y
    | _ => try intro
    end; nested_induction tl
  end;
  
  intros;
  destruct_conds conds.

(* destructs a function application exp into a pair of shape (f, (t1, (t2, ... (tn, tt)))) and pose it as Res *)
Ltac destrApp exp Res := 
  match exp with
  | ?f' ?t' => 
    prepend_res Res t'; destrApp f' Res
  | _ => prepend_res Res (exp _::_ _nil)
  end.

Ltac specializes recCalls :=
  match recCalls with
  | _nil => idtac
  | ?recCall _::_ _nil => intros; specialize (recCall)
  | ?recCall _::_ ?tl => intros; try pose proof (recCall); specializes tl
  end.

Tactic Notation "repeat_or_fail" tactic(tac) := tryif tac then repeat tac else fail. 
Local Tactic Notation "first_sucessful" tactic(t) tactic(t') := tryif t then idtac else t'. 

Ltac split_hyps := repeat_or_fail split_hyp.

Global Tactic Notation "transparent" "assert" constr(type) "as" ident(name) "by" tactic(tac) :=
  (* idtac "transparent assert " type " as " name " by " "...";
  tryif (assert type as name by (now tac); clear name) then idtac else (idtac "assert is impossible!"; fail);
  first [
    do_nonbranching (unshelve refine (let name := (_ : type) in _); [now tac|]) |
    idtac "transparent assert failed, falling back to plain assert"; 
    do_nonbranching (unshelve eassert type as name by (now tac))
  ]; 
    let tp := type of name in
    idtac "transparent assert sucessful: " name ": " tp.
  (* do_no_subgoals (unshelve assert type as name by (now tac)). *)
  *)
  do_nonbranching (unshelve refine (let name := (_ : type) in _); [now tac|]).

Tactic Notation "autospecialize'" hyp(h) "by" tactic(tac) :=
  let temp := fresh "temp_autospecialize_" in
  pose (fun x => h x) as temp;
  match type of temp with
  | ?p -> _ => clear temp; match type of p with
    | Prop => assert p as temp by tac; specialize (h temp); try clear temp
    end
  | _ => fail h " is not a function, so it cannot be specialized. "
  end.

Global Tactic Notation "autospecialize" hyp(h) "by" tactic(tac) := try (autospecialize' h by tac).

Global Tactic Notation "make_opaque" hyp(h) :=
  let temp := fresh "temp" in
  pose proof (exist _ h eq_refl) as temp;
  destruct temp as [temp ->];
  pose proof (exist _ temp eq_refl) as h; 
  destruct h as [h ->]; clear temp.

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

Ltac isApplOf t f :=
  let Res := fresh "Res" in
  let ResRefl := fresh "ResRefl" in
  destrApp t Res;
  assRefl Res as ResRefl;
  match type of ResRefl with
  | ((?f' _::_ _nil) _::_ _) = _ => clear ResRefl; eq_fail f' f
  end.

(* destructs a function application posed as Res into a pair of shape (f, (t1, (t2, ... (tn, tt)))) and pose it as Res *)
Tactic Notation "destrAppRes" ident(Res) :=
  let temp := fresh "temp" in
  assRefl Res as temp;
  match type of temp with
  | ?exp = _ => destrApp exp Res
  end; clear temp.

Ltac get_dom_ref f Res :=
  let temp := fresh "temp" in
  pose (fun x => f x) as temp;
  match type of temp with
  | {x:?b | ?p } -> _ => pose (fun x:b => p) as Res
  end; clear temp.

Ltac get_ret_tp tp Res :=
  match tp with
  | exists (_:_), ?p => get_ret_tp p Res
  | exists (_:_) (_:_), ?p => get_ret_tp p Res
  | ?g => pose g as Res
  end.

Ltac get_goal_ret Res :=
  match goal with
  | [ |- ?g ] => get_ret_tp g Res
  end.

Ltac rewriteAll h :=
  match type of h with
  | ?v = ?t => tryif (isVar v) then 
    first [subst v | 
      first [progress rewrite h in *; clear h | revert h; intros ->]; 
    clear v] else first [rewrite h in *; clear h | revert h; intros ->]
  end.

Global Tactic Notation "rewriteRLAll" hyp(h) := 
  match type of h with
  | ?t = ?v => tryif (isVar v) then 
    (first [progress rewrite <- h in *; clear h | revert h; intros <-];
    clear v) 
  else first [progress rewrite <- h in *; clear h | revert h; intros <-]
  end.

(* rewrite in <- direction by antecedent *)
Ltac introsRwRL :=
  let H := fresh "temp" in
  match goal with
  |- _ = _ -> _ => tryif intros <- then idtac else
    intros H; try rewrite <- H in *; clear H
  | |- ?g => fail "goal " g " has no equality as antecedent we can rewrite with"
  end.

Ltac lookupFuncTp tm := 
  let tp := type of tm in
  exact tp.

Inductive LookupItems : Set :=
  | rel : LookupItems
  | rwLem : LookupItems.
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

Ltac localLookupRel1 f Res :=
  match type of f with
  | forall (x:?A'), ?B' x =>
    match goal with
    | [rel: ?A -> ?B -> Prop |- _] =>
      match goal with
      | [projA: A' ⤖ A |- _] => 
        match goal with
        | [projB: forall (a:A'), (B' a) ⤖ B |- _] => 
          pose rel as Res
        end
      end
    end
  end.

Ltac localLookupRel2 f Res :=
  match type of f with
  | forall (x1:?X1') (x2:?X2' x1), ?T' x1 x2 =>
    match goal with
    | [rel: ?X1 -> ?X2 -> ?T -> Prop |- _] =>
      match goal with
      | [proj1: X1' ⤖ X1 |- _] => 
        match goal with
        | [proj2: forall (x1:X1'), (X2' x1) ⤖ X2 |- _] => 
          match goal with
          | [projT: forall (x1:X1') (x2:X2' x1), (T' x1 x2) ⤖ T |- _] => 
            pose rel as Res
          end
        end
      end
    end
  end.

Ltac localLookupRel3 f Res :=
  match type of f with
  | forall (x1:?X1') (x2:?X2' x1) (x3:?X3' x1 x2), ?T' x1 x2 x3 =>
    match goal with
    | [rel: ?X1 -> ?X2 -> ?X3 -> ?T -> Prop |- _] =>
      match goal with
      | [proj1: X1' ⤖ X1 |- _] => 
        match goal with
        | [proj2: forall (x1:X1'), (X2' x1) ⤖ X2 |- _] => 
          match goal with
          | [proj3: forall (x1:X1') (x2:X2' x1), (X3' x1 x2) ⤖ X3 |- _] => 
            match goal with
            | [projT: forall (x1:X1') (x2:X2' x1) (x3:X3' x1 x2), (T' x1 x2 x3) ⤖ T |- _] => 
              pose rel as Res
            end
          end
        end
      end
    end
  end.

Ltac localLookupRel f Res :=
  first [localLookupRel1 f Res | localLookupRel2 f Res | localLookupRel3 f Res].

Ltac hasLocalRel f :=
  let res := fresh "res" in
  localLookupRel f res;
  try clear res.

Ltac has_rel f := first [test_term (lookup rel f) | hasLocalRel f].
Ltac has_no_rel f := tryif (has_rel f) then fail else idtac.


Ltac localLookupFunc1 rel Res :=
  match type of rel with
  | ?A -> ?B -> Prop =>
    match goal with
    | [f: forall (x:?A'), ?B' x |- _] =>
      match goal with
      | [projA: A' ⤖ A |- _] => 
        match goal with
        | [projB: forall (a:A'), (B' a) ⤖ B |- _] => 
          pose f as Res
        end
      end
    end
  end.

Ltac localLookupFunc2 rel Res :=
  match type of rel with
  | ?X1 -> ?X2 -> ?T -> Prop =>
    match goal with
    | [f: forall (x1:?X1') (x2:?X2' x1), ?T' x1 x2 |- _] =>
      match goal with
      | [proj1: X1' ⤖ X1 |- _] => 
        match goal with
        | [proj2: forall (x1:X1'), (X2' x1) ⤖ X2 |- _] => 
          match goal with
          | [projT: forall (x1:X1') (x2:X2' x1), (T' x1 x2) ⤖ T |- _] => 
            pose f as Res
          end
        end
      end
    end
  end.

Ltac localLookupFunc3 rel Res :=
  match type of rel with
  | ?X1 -> ?X2 -> ?X3 -> ?T -> Prop =>
    match goal with
    | [f: forall (x1:?X1') (x2:?X2' x1) (x3:?X3' x1 x2), ?T' x1 x2 x3 |- _] =>
      match goal with
      | [proj1: X1' ⤖ X1 |- _] => 
        match goal with
        | [proj2: forall (x1:X1'), (X2' x1) ⤖ X2 |- _] => 
          match goal with
          | [proj3: forall (x1:X1') (x2:X2' x1), (X3' x1 x2) ⤖ X3 |- _] => 
            match goal with
            | [projT: forall (x1:X1') (x2:X2' x1) (x3:X3' x1 x2), (T' x1 x2 x3) ⤖ T |- _] => 
              pose f as Res
            end
          end
        end
      end
    end
  end.
Ltac localLookupFunc rel Res :=
  first [localLookupFunc1 rel Res | localLookupFunc2 rel Res | localLookupFunc3 rel Res].
Ltac localIsRel rel :=
  let res := fresh "res" in
  localLookupFunc rel res;
  try clear res.

Ltac is_rel f_rel := first [test_term (getF f_rel) | localIsRel f_rel].
Ltac is_no_rel f_rel := tryif (test_term (getF f_rel)) then fail else idtac.

Ltac localLookupRwLem1 f Res :=
  match type of f with
  | forall (x:?A'), ?B' x =>
    match goal with
    | [rel: ?A -> ?B -> Prop |- _] =>
      match goal with
      | [projA: A' ⤖ A |- _] => 
        match goal with
        | [projB: forall (a:A'), (B' a) ⤖ B |- _] => 
          match goal with
          | [rwLem: forall (x:A') (v:B), (projB x).(proj) (f x) = v <-> rel (projA.(proj) x) v |- _] =>
            pose rwLem as Res
          end
        end
      end
    end
  end.

Ltac localLookupRwLem2 f Res :=
  match type of f with
  | forall (x1:?X1') (x2:?X2' x1), ?T' x1 x2 =>
    match goal with
    | [rel: ?X1 -> ?X2 -> ?T -> Prop |- _] =>
      match goal with
      | [pr1: X1' ⤖ X1 |- _] => 
        match goal with
        | [pr2: forall (x1:X1'), (X2' x1) ⤖ X2 |- _] => 
          match goal with
          | [prT: forall (x1:X1') (x2:X2' x1), (T' x1 x2) ⤖ T |- _] => 
            match goal with
              | [rwLem: forall (x1:X1') (x2:X2' x1) (v:T), (prT x1 x2).(proj) (f x1 x2) = v <-> rel (pr1.(proj) x1) ((pr2 x1).(proj) x2) v |- _] =>
                pose rwLem as Res
              end
          end
        end
      end
    end
  end.

Ltac localLookupRwLem3 f Res :=
  match type of f with
  | forall (x1:?X1') (x2:?X2' x1) (x3:?X3' x1 x2), ?T' x1 x2 x3 =>
    match goal with
    | [rel: ?X1 -> ?X2 -> ?X3 -> ?T -> Prop |- _] =>
      match goal with
      | [proj1: X1' ⤖ X1 |- _] => 
        match goal with
        | [pr2: forall (x1:X1'), (X2' x1) ⤖ X2 |- _] => 
          match goal with
          | [pr3: forall (x1:X1') (x2:X2' x1), (X3' x1 x2) ⤖ X3 |- _] => 
            match goal with
            | [prT: forall (x1:X1') (x2:X2' x1) (x3:X3' x1 x2), (T' x1 x2 x3) ⤖ T |- _] => 
              match goal with
              | [rwLem: forall (x1:X1') (x2:X2' x1) (x3:X3' x1 x2) (v:T), (prT x1 x2 x3).(proj) (f x1 x2 x3) = v <-> rel (pr1.(proj) x1) ((pr2 x1).(proj) x2) ((pr3 x1 x2).(proj) x3) v |- _] =>
                pose rwLem as Res
              end
            end
          end
        end
      end
    end
  end.

Ltac localLookupRwLem f Res :=
  first [localLookupRwLem1 f Res | localLookupRwLem2 f Res | localLookupRwLem3 f Res].
Ltac localHasRwLem f :=
  let res := fresh "res" in
  localLookupRwLem f res;
  try clear res.
Ltac hasRwLem f := first [test_term (lookup rwLem f) | localHasRwLem f].
Ltac lookupRwLem f Res := first [pose (lookup rwLem f) as Res | localLookupRwLem f Res].
Ltac getRwLemRefl f ReflRes :=
  let res := fresh "res" in
  lookupRwLem f res;
  assRefl res as ReflRes;
  simpl in ReflRes.

Ltac isConstrAppl t :=
  tryif (isVar t) then fail else 
  let temp := fresh "temp" in
  match t with
  | ?cApp _ => assert (forall x y, x <> y -> cApp x <> cApp y) as temp by (intros; injection; assumption)
  end; clear temp.

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

Ltac isFApplTm fApp :=
  let fAppD := fresh "fAppD" in
  destrApp fApp fAppD;
  let fAppRefl := fresh "fAppRefl" in
  assRefl fAppD as fAppRefl;
  match type of fAppRefl with
  | ((?f _::_ _nil) _::_ _) = _ => clear fAppRefl; has_rel f
  end.

Ltac isFAppl fApplV :=
  let fAppl := fresh "fAppl" in
  pose fApplV as fAppl; try unfold fApplV in fAppl;
  let fApplRefl := fresh "fApplRefl" in
  assRefl fAppl as fApplRefl;
  match type of fApplRefl with
  | ?fApp = _ => clear fApplRefl; 
    isFApplTm fApp
  end.

Ltac is_no_rel_appl tm := tryif (isRelAppl tm) then fail else idtac.
Ltac is_no_f_appl tm := tryif (isFAppl tm) then fail else idtac.

(* quick heuristic to ensure we don't waste time trying to invert hypothesis that aren't applications of relations parameters that aren't all variables *)
Ltac inversion_precheck h :=
  match type of h with
  | ?f_rel_ap ?v => isVar v; tryif (match f_rel_ap with
    | ?rel ?x1 ?x2 ?x3 => is_no_rel_appl rel
    | ?rel ?x1 ?x2 => is_no_rel_appl rel
    | ?rel ?x => is_no_rel_appl rel
    end) then fail else isRelAppl f_rel_ap
  end.
Global Tactic Notation "non_branching_inversion" hyp(h) := first 
  [ do_nonbranching strong_inversion h 
  | inversion_precheck h; do_nonbranching (strong_inversion h; try (exfalso; timeout 1 quicksolve))].

Tactic Notation "is_rel_appl_h" hyp(h) :=
  let tp := type of h in
  tryif (progress (cbv beta delta in h)) then fail tp " is reducible and thus not an application of an inductively-defined relation" else idtac;
  isRelAppl tp. 

Local Ltac eqSnd rel tuple :=
  match tuple with
  | (_, ?frel) => eq_fail rel frel
  | _ => fail
  end.

Local Ltac eqFst f tuple :=
  match tuple with
  | (?f', _) => eq_fail f f'
  | _ => fail
  end.

Local Ltac getFst tuple Res :=
  match tuple with
  | (?f, _) => return Res f
  | _ => fail "getFst " tuple Res " failed!"
  end.

Local Ltac getSnd tuple Res :=
  match tuple with
  | (_, ?frel) => return Res frel
  | _ => fail
  end.

Ltac isRel map rel := 
  match map with
  | _nil => fail "The relation " rel " is not amongst the relations in the map."
  | ?hd _::_ ?tl => tryif eqSnd rel hd then idtac else isRel tl rel
  end.

Ltac getRel map f Res := 
  match map with
  | _nil => fail
  | ?hd _::_ ?tl => tryif eqFst f hd then getSnd hd Res else getRel tl f
  end.

Ltac headApp exp Res :=
  let temp := fresh "temp" in
  (* idtac "calling destrApp " exp temp; *)
  destrApp exp temp;
  (* idtac "destrApp " exp temp; *)
  head_res temp Res;
  (* idtac "head_res " temp Res; *)
  clear temp.

Ltac mkAppl f ts Res :=
  match ts with
  | _nil => return Res f
  | ?t _::_ ?tl => mkAppl (f t) tl Res
  end.

Ltac applyFunc f ts :=
  let Res := fresh "temp" in
  let tempEq := fresh "H" in
  mkAppl f ts Res;
  assert (Res = Res) as tempEq by reflexivity;
  subst Res; 
  match type of tempEq with
  | ?fappl = _ => refine fappl; clear tempEq
  end.

Ltac applyFuncRel rel ts :=
  first [applyFunc (getF rel) |
    let fres := fresh "f" in
    let fresRefl := fresh "fRefl" in
    localLookupFunc rel fres;
    assRefl fres as fresRefl;
    match type of fresRefl with
    | ?f = _ => clear fresRefl;
      applyFunc f
    end].

Ltac clear_all :=
  repeat (match goal with
  | [h:_ |- _] => clear h
  end
  ).

Ltac print_proof_state :=
  let alreadyPrinted := fresh "alreadyPrinted" in
  let alreadyPrintedRefl := fresh "alreadyPrintedRefl" in
  pose _nil as alreadyPrinted;
  repeat (
    assRefl alreadyPrinted as alreadyPrintedRefl;
    match type of alreadyPrintedRefl with
    | ?already = _ => clear alreadyPrintedRefl;
      match goal with
      | [ h: ?tp |- _ ] => 
        tryif (_contains h already) then
          fail
        else (
          pose (h _::_ already) as alreadyPrinted;
          idtac h ": " tp
        )
      end
    end
  );
  match goal with
  | |- ?g => idtac "----------------------------------"; idtac g; idtac " "
  end; try clear alreadyPrinted.

Tactic Notation "rename_hyp" hyp(h) ident(name) :=
  pose h as name;
  replace h with name in * by (subst name; reflexivity);
  make_opaque name;
  clear h.

Ltac reconstruct_ref map :=
  match goal with
  | [h: ?frelApp ?v |- {v | ?r} ] => isRelAppl h map; 
    let Res := fresh "temp" in
    let ResArgs := fresh "tempArgs" in
    let temp := fresh "temp_" in
    destrApp frelApp temp;
    head_res temp Res;
    tail_res temp ResArgs;
    map_res (fun v => (exist _ v _)) ResArgs;
    clear temp;
    let tempEq := fresh "H" in
    assRefl Res as tempEq; 
    let fRes := fresh "Res" in
    match type of tempEq with
    | ?frel = _ => (* applyFunc (getF frel); *)
      let tempEq' := fresh "H'" in
      assRefl ResArgs as tempEq';
      match type of tempEq with
      | ?ts = _ => applyFuncRel frel ts
      end;
      clear tempEq'; clear tempEq
    end
  end. 

(* destructs a function type tp into a pair of shape (((x:xTp) _::_ ((y:yTp) _::_ ...(z:zTp) _::_ _nil) and poses it as Res *)
Ltac getAntes tp Res :=
  match tp with
  | forall (x:?xTp), ?ret => 
    getAntes ret Res;
    prepend_res Res (x,xTp)
  | _ => return Res _nil
  end.

Local Ltac isAxOf v map arg :=
  match arg with
  | (?vdef, ?frelAp ?v') => eq_fail v v'; isRelAppl vdef map
  end.

Local Ltac findAxOf v map plist Res :=
  match plist with
  | _nil => fail
  | ?hd _::_ ?tl => tryif isAxOf v map hd then return Res hd else findAxOf v map tl Res
  end.

Local Ltac checkAxs antes Res2 map :=
  let resAx := fresh "resAx" in
  match antes with
  | (?v, ?vTp) _::_ ?tl => 
    tryif (findAxOf v map tl resAx) 
      then (prepend_res Res2 (v, resAx); subst resAx; checkAxs tl Res2 map)
      else checkAxs tl Res2 map
  | _ _::_ _nil => fail "The result " antes " findAxs is called on is ill-formed. "
  end.

Ltac findAxs Res Res2 map :=
    let tempEq := fresh "tempEq" in
    assRefl Res as tempEq;
    match type of tempEq with
    | ?antes = _ => checkAxs antes Res2 map
    end; clear tempEq.

Ltac specializeAx ih ax :=
  match ax with
  | (?v, (?vdef, ?frelAp ?v')) => eq_fail v v';
    match goal with
    | [h:frelAp ?v' |- _] => 
      let htp := type of h in
      let T := type of v in
      let temp := fresh "H" in
      tryif (assert (forall (w:T), (frelAp w) -> w = v') as temp by (intros; eauto with f_rel_funct_db); clear temp)
      then 
        idtac "Axiomatization " h ": " htp " of variable " v " is used to specialize " ih ". "; 
        specialize ih with (v:=v'); specialize ih with (vdef:=h) 
      else fail "Cannot prove function-hood, so not going to specialize " ih " by possibly not unique value " v ". "
    | _ => fail
    end
  | _ => fail "Ill-formed axiom in specializeAx " ih ax
  end.

Tactic Notation "specializeAx_res" hyp(ih) ident(axRes) := 
    let tempEq := fresh "tempEq" in
    assRefl axRes as tempEq; 
    match type of tempEq with
    | ?ax = _ => specializeAx ih ax
    end; clear tempEq.


(* destructs a function type tp into a pair of shape ((xTp _::_ yTp _::_ ...zTp _::_ _nil) and poses it as Res *)
Ltac getAnteTps tp Res :=
  match tp with
  | ?ante -> ?ret => idtac "prepending " ante " to " Res;
    getAnteTps ret Res;
    prepend_res Res ante
  | forall (_:?xTp), ?ret => idtac "prepending " xTp " to " Res;
    getAnteTps ret Res;
    prepend_res Res xTp
  | _ => return Res _nil
  end.

(* destructs a function type tp into a pair of shape (((x:xTp),((y:yTp),...(z:zTp)...unit), ret) and poses it as Res
   this tactic also supports implications *)
Ltac destrFunc tp Res :=
  match tp with
  | forall (x:?xTp), ?ret => 
    let temp := fresh "temp" in
    destrFunc ret temp;
    pose (((x,xTp), fst temp), snd temp) as Res;
    subst temp
  | ?xTp -> ?ret => 
    let x := fresh "x_" in
    let temp := fresh "temp" in
    pose True as x;
    destrFunc ret temp;
    clear x;
    pose (((x,xTp), fst temp), snd temp) as Res;
    subst temp
  | _ => pose (unit, tp) as Res
  end.

(*
Ltac 
  recreate_refined v relApp map Res := idtac v ", " relApp;
    let f_ts := fresh "Res" in
    idtac "recreate_var" v relApp; 
    destrApp relApp f_ts;
    idtac "after destrApp" relApp f_ts;
    let temp := fresh "temp" in
    head_res f_ts temp;
    let tail_res := fresh "tail_res" in
    tail_res f_ts tail_res;
    idtac "after head_res" f_ts;
    let temp2 := fresh "temp2" in
    let f_res := fresh "f_res" in
    try (assert (temp = temp) as temp2 by reflexivity; subst temp;
    match type of temp2 with
    | ?frel _::_ _nil = _ => getF map frel f_res; clear temp2
    end);
    
    let temp3 := fresh "temp3" in
    let fAppl_res := fresh "fAppl_res" in
    assRefl f_res as temp3;
    match type of temp3 with
    | ?f = _ => idtac "f:=" f; clear temp3; 
      let temp5 := fresh "temp5" in
      assert (tail_res = tail_res) as temp5; subst tail_res;
      match type of temp5 with
      | ?tl = _ => clear temp5; idtac "calling mkRelAppl" f tl fAppl_res; mkRelAppl f tl Res map
      end
    end
*)

(*
Calling mkRefAppl add (IH_m_n _::_ (mult_res_2 _::_ _nil)) fAppl_res
IH_m_n ,  (add_rel m n)
recreate_var IH_m_n (add_rel m n)
after destrApp (add_rel m n) Res0
after head_res Res0
f:= add
mult_res_2 ,  (mult_rel n o)
recreate_var mult_res_2 (mult_rel n o)
after destrApp (mult_rel n o) Res0
after head_res Res0
f:= mult
*)
