Load TacticUtils.

Ltac injectivity_in H := injection H; clear H; intros H.

(* execute the two tactics one after the other and suceed iff at least one of them is sucessful *)
Tactic Notation "concat_either" tactic(first) tactic(second) :=
  tryif first then try second else second.

Definition qmark [A:Type] [P: A -> Prop] [B:Type] [Q: Prop] (p:{x:A | P x}) (q:{_:B|Q}): {x:A | P x /\ Q}.
Proof. 
  destruct p as [u p].
  destruct q as [_ q].
  exact (exist _ u (conj p q)).
Defined. 
Global Notation "p ? q" := (qmark p q) (at level 99).

Ltac is_trivial tp :=
  match tp with
  | True => idtac
  | ?tm = ?tm => idtac
  | ?tm == ?tm => idtac
  | _ => fail
  end.

Ltac cleanup_witness z :=
  let zTp := type of z in
  let zKnd := type of zTp in
  eq_fail zKnd Prop;
  
  let temp_wit_rw := fresh "temp_wit_rw" in
  tryif (is_trivial zTp) then fail else idtac;
  match goal with
  | [wit: zTp |- _] => 
    assert (forall z', z' = wit) as temp_wit_rw by (intros; auto with pi_db);
    try rewrite -> (temp_wit_rw z) in *;
    repeat progress rewrite -> temp_wit_rw in *
  | |- _ =>
    let wit := fresh "wit_" in
    set (z) as wit in *;
    assert (forall z', z' = wit) as temp_wit_rw by (intros; auto with pi_db);
    repeat progress rewrite -> temp_wit_rw in *;
    try clearbody wit;
    simpl in wit;
    let witTp := type of wit in
    tryif (eq_fail zTp witTp) then idtac "Created new witness " wit " for " witTp else 
      match goal with
      | [wit': witTp |- _] => neq_fail wit wit';
        clear temp_wit_rw;
        assert (forall z', z' = wit') as temp_wit_rw by (intros; auto with pi_db);
        rewrite -> (temp_wit_rw wit) in *;
        repeat progress rewrite -> temp_wit_rw in *;
        clear wit;
        idtac "Unified proof term with existing witness " wit' " for " witTp
      | |- _ => idtac "Created new witness " wit " for " witTp
      end
  end; clear temp_wit_rw.

#[global] Hint Unfold refinement_proj:get_rel_db.
#[global] Hint Unfold packPr:get_rel_db.
#[global] Hint Unfold f:get_rel_db.
#[global] Hint Unfold frel:get_rel_db.
#[global] Hint Unfold f_frel:get_rel_db.
#[global] Hint Unfold funct:get_rel_db.
#[global] Hint Unfold rel_u:get_rel_db.
#[global] Hint Unfold funct_u:get_rel_db.
#[global] Hint Unfold proj:get_rel_db.

Ltac unpack :=
  let E := fresh "E" in
  repeat autounfold with get_rel_db in *;
  match goal with
  | [f: Pack ?argTps ?T ?p |- _] => destruct f as [? ? ? ?] eqn:E
  | [f: uPack ?uargTps ?T |- _] => destruct f as [? ?] eqn:E
  end; 
  repeat autounfold with get_rel_db in *;
  repeat autorewrite with get_rel_db in *;
  repeat autounfold with get_rel_db in *;
  match type of E with
  | ?f = _ => try (revert E; intros ->; clear f)
  end;
  unfold packPr_proj in *.

Ltac unpack_all :=
  repeat autounfold with get_rel_db in *;
  let unpacked := fresh "unpacked" in
  pose _nil as unpacked;
  progress repeat (
  let E := fresh "E" in
  match goal with
  | [f: Pack ?argTps ?T ?p |- _] => tryif (contains_res f unpacked) then fail else 
    destruct f as [? ? ? ?] eqn:E
  | [f: uPack ?uargTps ?T |- _] => tryif (contains_res f unpacked) then fail else 
    destruct f as [? ?] eqn:E
  end; 
  repeat autounfold with get_rel_db in *;
  repeat progress autorewrite with get_rel_db in *;
  repeat autounfold with get_rel_db in *;
  match type of E with
  | ?f = _ => first [
    first [
    clear E; clear f |
    destruct E as [->]; clear f] |
    prepend_res unpacked f]
  end; 
  repeat autounfold with get_rel_db in *;
  repeat progress autorewrite with get_rel_db in * );
  clear unpacked.

Ltac fApplPack fAppl := idtac.

Ltac f_def_appl f := 
  let x := fresh "x" in
  intros x; fApplPack (f x).

Ltac isVarPairApp exp :=
  match exp with
  | ?h => isVar h
  | ?h _ _ => isVarPairApp h
  end.

Ltac isEqnResAppProj exp :=
  match exp with
  | ⌊ ?h -⌋ => isVar h
  | ⌊ ?h _ _ -⌋ => isVar h
  | ⌊ ?h _ _ _ _ -⌋ => isVar h
  | ⌊ ?h _ _ _ _ _ _ -⌋ => isVar h
  | ⌊ ?h _ _ _ _ _ _ _ _ -⌋ => isVar h
  | ⌊ ?h _ _ _ _ _ _ _ _ _ _ -⌋ => isVarPairApp h
  | _ => fail
  end.

Ltac findNextEqnResAppProj Res := 
  let res := fresh "res" in
  match goal with
  (* in case the hypothesis is from a previous axiomatization *)
  | [_: ⌊ _ -⌋ = _ |- ?g] => findSubExpr res isEqnResAppProj g
  | [h:?T |- ?g] => 
    first [findSubExpr res isEqnResAppProj T | findSubExpr res isEqnResAppProj g]
  end;
  let resRefl := fresh "resRefl" in
  assRefl res as resRefl;
  match type of resRefl with
  | ⌊ ?tm -⌋ = _ => clear resRefl; 
    set tm as Res in *
  end.

Ltac destructEqnResAppProj :=
  let Res := fresh "Res" in
  let temp := fresh "temp" in
  let resU := fresh "res_u" in
  let resP := fresh "res_p" in
  findNextEqnResAppProj Res;
  destruct Res as [resU resP].

Ltac isExistProj exp :=
  match exp with
  | ⌊ exist _ _ _ -⌋ => idtac
  | _ => (* idtac "subterm not matching " exp; *) fail
  end.

Ltac isSubCastProj exp :=
  match exp with
  | ⌊ subsumptionCast _ _ _ _ -⌋ => idtac
  | _ => (* idtac "subterm not matching " exp; *) fail
  end.

Ltac isAppProj exp :=
  match exp with
  | ⌊ ?fApp _ -⌋ => tryif (match fApp with
    | subsumptionCast _ _ _ => idtac
    | exist _ _ => idtac
    end) then fail else idtac (* "found matching subterm " exp *)
  | ⌊ ?const -⌋ => has_rel const; idtac
  | _ => (* idtac "subterm not matching " exp; *) fail
  end.

Local Ltac isEqRes Res exp :=
  let test := fresh "test" in
  assert (Res = exp) as test by (unfold Res; reflexivity); clear test. 

(* takes a projection ` tm posed as Res and sets tm as Res *)
Tactic Notation "undoProj" ident(Res) :=
  let temp := fresh "temp" in
  assRefl Res as temp;
  match type of temp with
  | ` ?tm = _ => clear temp; set tm as Res in *
  | ⌊ ?tm -⌋ = _ => clear temp; 
    (* idtac "found projection of " tm; *)
    tryif (set tm as Res in *) then idtac else (idtac "failed to pose that projection"; fail)
  end.

Ltac findProj exp Res :=
  findSubExpr Res isAppProj exp;
  undoProj Res.

(* simplify subterms of the shape ⌊ exist _ _ _ -⌋ in exp throughout the proof state *)
Ltac cleanupExistProj exp :=
  let Res := fresh "Res" in
  findSubExpr Res isExistProj exp;
  let temp := fresh "temp" in
  assRefl Res as temp;
  match type of temp with
  | ⌊ ?tm -⌋ = _ => clear temp; 
    pose proof ⌈ tm ⌉;
    set ⌊ tm -⌋ as Res in *
  end;
  first [rewrite proj_ex'' in Res | timeout 1 simpl in Res];
  subst Res.

(* simplify subterms of the shape ⌊ subsumptionCast _ _ _ _ -⌋ in exp throughout the proof state *)
Ltac cleanupSubCastProj exp :=
  let Res := fresh "Res" in 
  findSubExpr Res isSubCastProj exp;
  let temp := fresh "temp" in
  assRefl Res as temp;
  match type of temp with
  | ⌊ ?tm -⌋ = _ => clear temp; 
    pose proof ⌈ tm ⌉;
    set ⌊ tm -⌋ as Res in *
  end;
  first [rewrite proj_subCast in Res | timeout 1 simpl in Res];
  subst Res.

(* suceeds iff fApp is a hypothesis or an application of a hypothesis *)
Ltac isHypApp fApp :=
  match fApp with
  | ?f _ _ _ _ _ _ _ _ => isVar f
  | ?f _ _ _ _ _ _ _ => isVar f
  | ?f _ _ _ _ _ _ => isVar f
  | ?f _ _ _ _ _ => isVar f
  | ?f _ _ _ _ => isVar f
  | ?f _ _ _ => isVar f
  | ?f _ _ => isVar f
  | ?f _ => isVar f
  | ?f => isVar f
  | _ =>
    let fAppD := fresh "fAppD" in
    destrApp fApp fAppD;
    let fAppRefl := fresh "fAppRefl" in
    assRefl fAppD as fAppRefl;
    match type of fAppRefl with
    | ((?h _::_ _nil) _::_ _) = _ => clear fAppRefl; 
      tryif (isVar h) then idtac else (*idtac "Not an application of a hypothesis, exiting from isHypApp. "; *) fail
    | _ => fail
    end
  end.

Ltac ihAppProj exp :=
  match exp with
  | ⌊ ?fApp ?p -⌋ => propKinded p; isHypApp fApp
  | _ => fail
  end.

Ltac findAppProj exp Res :=
  findSubExpr Res ihAppProj exp;
  undoProj Res.

Ltac applyRwLem h :=
  tryif (progress autorewrite with f_rel_funct_db in h) then idtac else (
  let hTp := type of h in
  match hTp with
  | ⌊ ?fAppl -⌋ = ?v => isVar v;
    let fAppD := fresh "fAppD" in
    destrApp fAppl fAppD;
    let fAppRefl := fresh "fAppRefl" in
    assRefl fAppD as fAppRefl;
    match type of fAppRefl with
    | ((?f _::_ _nil) _::_ ?ts) = _ => clear fAppRefl; 

      tryif (hasRwLem f) then idtac else ((* idtac "No rwRelation known for function " f ". "; *) fail); 

      (* idtac h " : " hTp; *)
      
      let rwLemResRefl := fresh "rwLemResRefl" in
      getRwLemRefl f rwLemResRefl;

      match type of rwLemResRefl with
      | ?rwLemSimpl = _ => clear rwLemResRefl;
        let rwLemTp := type of rwLemSimpl in
        idtac "The rewrite lemma " rwLemSimpl ": " rwLemTp " that needs to be used to change axiomatization of a variable from the refined to the unrefined world. ";
        match ts with
        | _nil => 
          rewrite (rwLemSimpl v) in h
        | ((exist _ ?x1 ?x1p) _::_ _nil) => 
          rewrite (rwLemSimpl x1 x1p v) in h
        | ((exist _ ?x1 ?x1p) _::_ (exist _ ?x2 ?x2p) _::_ _nil) => 
          rewrite (rwLemSimpl x1 x2 x1p x2p v) in h
        | ((exist _ ?x1 ?x1p) _::_ (exist _ ?x2 ?x2p) _::_ (exist _ ?x3 ?x3p) _::_ _nil) => 
          rewrite (rwLemSimpl x1 x2 x3 x1p x2p x3p v) in h
        | ((exist _ ?x1 ?x1p) _::_ (exist _ ?x2 ?x2p) _::_ (exist _ ?x3 ?x3p) _::_ (exist _ ?x4 ?x4p) _::_ _nil) => 
          rewrite (rwLemSimpl x1 x2 x3 x4 x1p x2p x3p x4p v) in h
        | ((exist _ ?x1 ?x1p) _::_ (exist _ ?x2 ?x2p) _::_ (exist _ ?x3 ?x3p) _::_ (exist _ ?x4 ?x4p) _::_ (exist _ ?x5 ?x5p) _::_ _nil) => 
          rewrite (rwLemSimpl x1 x2 x3 x4 x5 x1p x2p x3p x4p x5p v) in h
        | _ => 
          tryif (isVar h) then idtac else idtac "Global function " f " has arity >5 and arguments " ts ". ";
          let remTs := fresh "remTs" in
          let remTsRefl := fresh "remTsRefl" in
          let resArgs := fresh "resArgs" in
          let resArgsRefl := fresh "resArgsRefl" in
          pose ts as remTs;
          pose _nil as resArgs;
          let rwAppl := fresh "rwAppl" in
          let rwApplRefl := fresh "rwApplRefl" in
          
          repeat (
            assRefl remTs as remTsRefl;
            match type of remTsRefl with
            | _nil = _ => clear remTsRefl;
              prepend_res resArgs v;
              reverse_res resArgs;
              fail
            | ((exist _ ?x1 ?x1p) _::_ ?tl) = _ => clear remTsRefl; pose tl as remTs;
              prepend_res resArgs x1;
              prepend_res resArgs x1p
            end
          ); 
          assRefl resArgs as resArgsRefl;
          match type of resArgsRefl with
          | ?resFargs = _ => clear resArgsRefl; 
            mkAppl rwLemSimpl resFargs rwAppl;
            assRefl rwAppl as rwApplRefl;
            match type of rwApplRefl with
            | ?rwLemAppl = _ => clear rwApplRefl; 
              rewrite rwLemAppl in h
            end
          end
        end
      end
    end
  end).

Tactic Notation "axiomatize_term" constr(tm) "as " ident(name) ident(def) :=
  let v := fresh "v" in
  let v_def := fresh "res_def" in
  let v_wit := fresh "res_wit" in
  let temp := fresh "res_ref" in
  
  let tm' := fresh "tm'" in
  pose (exist _ tm (eq_refl tm)) as tm';
  
  pose (⌊ tm -⌋) as v; assert (⌊ tm -⌋ = v) as v_def by reflexivity;
  pose proof (exist _ v v_def) as [name def]; 

  clear v v_def;
  let def_rw := fresh "def_rw" in
  pose proof def as def_rw; try unfold tm in def;
  try clearbody tm;
  try autounfold with lia_unfold in tm;
  try (applyRwLem def; simpl in def); 
  
  tryif (destruct tm' as [[v v_wit] v_def];
  pose proof def_rw as temp; rewrite v_def in temp; simpl in temp;
  revert temp; intros <-; clear v_def) then 
    idtac "Sucessfully axiomatized refined term and created refinement witness for it."
  else (idtac "Failed to create refinement witness for newly axiomatized refined term."; clear tm');
  try (
      match type of def_rw with
      | ⌊ ?Res -⌋ = v => let tmp := fresh "v_p" in
        pose proof (⌈ Res ⌉) as tmp;
        rewrite def_rw in tmp
      end
    ).

Ltac pose_cleanup_refined_tm var_name tm := 
  let temp := fresh "temp_r" in
  let v_def := fresh "v_def" in 
  pose tm as temp;
  pose proof ( ⌈ temp ⌉ );
  assert ({v | ⌊ temp -⌋ = v}) as v by (now refine (exist _ ( ⌊ temp -⌋ ) eq_refl));
  destruct v as [var_name v_def]; unfold temp in *;
  rewrite v_def in *;
  clear temp;
  applyRwLem v_def.

Create HintDb f_rel_constr_db.
Create HintDb f_rel_funct_db.

Ltac cleanup_subterms tm :=
  match tm with
  | exist ?pred ?res ?z => cleanup_witness z
  | ⌊ exist ?pred ?res ?z -⌋ => cleanup_witness z
  | ?fApp ?t => concat_either (cleanup_subterms t) (cleanup_subterms fApp)
  end.

Ltac isHOAppProj exp :=
  match exp with
  | ⌊ ?f ?argList -⌋ => match goal with
    | [f_frel : (forall (args : ArgList ?argTps) (v : ?resTp), ⌊ ?f args -⌋ = v <->
      ?frel (prArgList args ?uargTps _) v) |- _] =>
    idtac
    end
  | ` (?f ?argList) => match goal with
    | [f_frel : (forall (args : ArgList ?argTps) (v : ?resTp), ⌊ ?f args -⌋ = v <->
      ?frel (prArgList args ?uargTps _) v) |- _] =>
    idtac
    end
  | _ => (* idtac "subterm not matching " exp; *) fail
  end.

(* takes a projection ` tm posed as Res and poses tm as Res *)
Tactic Notation "undoHOAppProj" ident(ProjRes) ident(Res) :=
  let temp := fresh "temp" in
  assRefl Res as temp;
  match type of temp with
  | ?projRes = _ => 
    match type of temp with
    | ⌊ ?tm -⌋ = _ => clear temp; 
      set projRes as ProjRes in *;
      (* idtac "found projection of " tm; *)
      tryif (set tm as Res in *) then idtac else (idtac "failed to pose that projection"; fail)
    end
  end.

Ltac findHOAppProj exp ProjRes Res :=
  findSubExpr Res isHOAppProj exp;
  undoHOAppProj ProjRes Res.

Ltac axHOAppProjTm exp :=
  let ProjRes := fresh "v" in
  let Res := fresh "Res" in
  let tmv := fresh "u" in
  let tmp := fresh "up" in
  let temp := fresh "H" in
  simpl_proj;
  findHOAppProj exp ProjRes Res;

  let Res' := fresh "Res'" in
  let ResRefl := fresh "ResRefl" in
  pose ProjRes as Res'; 
  try unfold ProjRes in Res'; try unfold Res in Res';
  assRefl Res' as ResRefl;
  match type of ResRefl with
  (* We have a projection of a pack application *)
  | ⌊ ?f ?argList -⌋ = _ => clear ResRefl; match goal with
    | [f_frel : (forall (args : ArgList ?argTps) (v : ?resTp), ⌊ f args -⌋ = v <->
      ?frel (prArgList args ?uargTps _) v) |- _] =>
      let w := fresh "w" in
      let tm := fresh "tm" in
      let v_def := fresh "res_def" in
      let v_df := fresh "res_def1" in
      let v_wit := fresh "res_wit" in
      let temp := fresh "res_ref" in
      assert (⌊ Res -⌋ = ProjRes) as v_def by reflexivity;
      let witTp := type of (⌈ Res ⌉) in
      match goal with
      | [h: ?htp |- _] => eq_fail witTp htp; idtac "A witness for the refined term " tm " is already present as hypothesis " h " not asserting another. "
      | _ => pose proof (⌈ Res ⌉) as v_wit
      end;
      pose (exist _ ProjRes v_def) as temp;
      destruct temp as [w v_df];
      rewrite v_def in v_df; revert v_df; intros <-;
      let def_rw := fresh "def_rw" in
      pose proof v_def as def_rw; try unfold tm in v_def;
      try match goal with
      | [h: ?htp |- _] => eq_fail witTp htp; idtac h; rewrite def_rw in h
      end; try rewrite def_rw in v_wit;
      (* try rewriteAll def_rw;*)
      let rw_lem := fresh "rw_lem" in
      pose proof (f_frel argList ProjRes) as rw_lem;
      replace (f argList) with Res in rw_lem by reflexivity;
      apply pr1 in rw_lem;
      apply rw_lem in def_rw; clear rw_lem;
      simpl in def_rw;
      try first [rewrite def_rw | pose proof def_rw as ->];
        clear v_def;
        first [clear Res | subst Res];
        first [
          clearbody ProjRes |
          pose proof (exist _ ProjRes eq_refl) as [? ->] |
          let tmp := fresh "v" in
          set ProjRes as tmp in *;
          clearbody tmp;
          clear dependent ProjRes
        ]
    end
  end.

Ltac axProjTm exp :=
  let Res := fresh "Res" in
  let tmv := fresh "u" in
  let tmp := fresh "up" in
  let temp := fresh "H" in
  simpl_proj;
  findProj exp Res;

  let Res' := fresh "Res'" in
  let ResRefl := fresh "ResRefl" in
  pose Res as Res'; try unfold Res in Res';
  assRefl Res' as ResRefl;
  match type of ResRefl with
  (* Some obvious simplifications *)
  | exist ?pred ?res ?z = _ => clear ResRefl; 
    let tempExist := fresh "tempExist" in
    set (⌊ exist pred res z -⌋) as tempExist in *;
    cbn in tempExist;
    subst tempExist
  | @subsumptionCast ?A ?G ?H ?res ?p = _ => clear ResRefl; 
    let tempPr := fresh "tempProjSubCast" in
    set (⌊ @subsumptionCast A G H res p -⌋) as tempPr in *;
    simpl in tempPr;
    subst tempPr
  (* We have a projection of a function application with the function being a ho argument *)
  | ⌊ ?f ?argList -⌋ = _ => match goal with
    | [f_frel : (forall (args : ArgList ?argTps) (v : ?resTp), ⌊ f args -⌋ = v <->
      ?frel (prArgList args ?uargTps _) v) |- _] =>
      idtac "call axHOAPPProjTm to fix things up!"
    end
  (* this is an optimization that detects if the found refined term is an application of a reflected function and otherwise aborts immediately *)
  | ?res = _ => clear ResRefl; 
    tryif (isFAppl res) then idtac else ((*idtac "Projection " res " is not an application of a previously defined reflected function (or local one), so not going to try to get rid of it here";*) fail);
    match goal with
    (* this optimization detects if we already have a hypothesis we can use to rewrite away the projection *)
    | [rwH: ⌊ res -⌋ = ?v |- _] => isVar v; idtac "A variable axiomatizing the terms already exists. ";
      progress autorewrite with rwH in *
    | _ => 
      (* idtac "Calling axiomatize_term Res as " tmv tmp " on "; print_res Res; *)
      tryif (axiomatize_term Res as tmv tmp) then idtac else idtac "axiomatize_term failed on subexpression " res " of expression " exp;
      try cleanup_subterms res;
      match type of tmp with
      | ?f_rel_ap ?w => revert tmp; match goal with
        | [_:f_rel_ap ?v |- _] => intro tmp; assert (w = v) as temp by (eauto with f_rel_funct_db); rewriteAll temp
        | _ => intro tmp; isRelAppl f_rel_ap
          (*; idtac "axProjTm produced a new axiomatized variable " w *)
        | _ => 
          (* idtac "axProjTm cannot axiomatize term (like " tmpTp1 " that isn't an application of a reflected definition, but " f_rel_ap "isn't the corresponding relation application. "; *)
          fail
        end
      | ?t => (*idtac "axProjTm produced an ill-formed result" t; *) fail
      end; 
      match goal with
      | [eq: ⌊ ?Res -⌋ = ?v |- _] => repeat rewrite eq in *;
        try (let tmp := fresh "temp" in
        pose proof eq as tmp;
        simpl in tmp;
        revert tmp; intros <-)
      end
    end
  end.

Ltac createIhAppRw ih p :=
  match goal with
  | [h: ih ?q = ?v |- _ ] => propKinded q; (*idtac "Specialization of " ih " already exists in context as " v;*)
    tryif (neq_fail p q) then replace p with q in * by (auto with pi_db) else idtac
  | |- _ => 
    let H := fresh "temp" in
    assert (forall p', ih p' = ih p) as H by (intros; f_equal; now auto with pi_db); 
    (* let Htp := type of H in
    idtac H ": " Htp; *)
    try (rewrite H in *; idtac "Rewrote other applications of " ih " to " ih p " using proof irrelevance. "); 
    clear H;
    
    let v := fresh "v" in
    let v_def := fresh "v_def" in
    pose proof (exist (fun v => ih p = v) (ih p) eq_refl) as v;
    destruct v as [v v_def]; 
    try cleanup_witness p
  end.

(* takes a hypothesis with prop-kinded antecedent and a proof term for the antecedent,
    and creates a variable for the application and tries to 
    specialize all occurences of the hypothesis with that variable *)
Ltac assIhAppl ih p Res :=
  propKinded p;
  idtac "assIhAppl " ih p Res; 
  createIhAppRw ih p;
  match goal with
  | [h: ih ?q = ?v |- _ ] => propKinded q; (*idtac "Specialization of " ih " already exists in context as " v;*)
    replace p with q in * by (auto with pi_db);
    pose v as Res;
    try (rewriteAll h)
  | |- _ => fail "Missing hypothesis rewriting ih application into a variable. "
  end.

(* Unify and opaqueify ih application subterms in exp throughout the proof state *)
Ltac axProjIhAppl exp :=
  let Res := fresh "Res" in
  let ih := fresh "ih" in
  let ihApplRefl := fresh "ihApplRefl" in
  findAppProj exp Res;
  (*axiomatize_term Res as ih ihApplRefl;*)
  pose proof (eq_refl ⌊ Res -⌋) as ihApplRefl; unfold Res in ihApplRefl;
  match type of ihApplRefl with
  | ⌊ ?ihApp -⌋ = _ => clear ihApplRefl;
    let ihAppD := fresh "ihAppD" in
    destrApp ihApp ihAppD;
    let ihAppRefl := fresh "ihAppRefl" in
    assRefl ihAppD as ihAppRefl;
    match type of ihAppRefl with
    | ((?ih0 _::_ _nil) _::_ ?p0 _::_ ?tl0) = _ => clear ihAppRefl; 
      idtac "Creating partial applications for " ih0 (* tl0 *);
      let ihAppl := fresh "ihAppl" in
      assIhAppl ih0 p0 ihAppl; (* this may create variables of type ih0 _ = ihAppl *)
      (* idtac "Created partial applications for " ih0; *)
      
      let tail := fresh "tail" in
      pose tl0 as tail;
      let tailRefl := fresh "tailRefl" in
      
      repeat (
        (* idtac "main ih application loop"; *)
        assRefl tail as tailRefl; 
        let tailReflTp := type of tailRefl in
        match type of tailRefl with
        | _nil = _ => (* idtac "done asserting partial applications of " ihAppl; *) clear tailRefl; fail
        | ?t _::_ ?t_p _::_ ?tl = _ => clear tailRefl; propKinded t_p; 
          (* idtac "Going to specialize the ih with term " t " and corresponding witness " t_p; *)
          assRefl ihAppl as ihAppRefl; 
          match type of ihAppRefl with
          | ?ih = _ => clear ihAppRefl; 
            assIhAppl (ih t) t_p ihAppl
          end;
          pose tl as tail
        | ?p _::_ ?tl = _ => clear tailRefl; propKinded p; idtac "Unexpectedly found single prop argument for ih to apply "; fail
        | ?t _::_ ?tl = _ => clear tailRefl; 
          assRefl ihAppl as ihAppRefl; 
          match type of ihAppRefl with
          | ?ih = _ => clear ihAppRefl; idtac "Specializing " ih " with term " t; pose (ih t) as ihAppl
          end;
          pose tl as tail
        end
      ); try clear tail; 
      assRefl ihAppl as ihAppRefl; 
      match type of ihAppRefl with
      | ?ih = _ => clear ihAppRefl; 
        let IH := fresh "IH" in
        let IH_p := fresh "IH_p" in
        destruct ih as [IH IH_p]
      end; try clear ih0
    | ?tp = _ => idtac "Destructed ihApp of unexpected shape: " tp; fail
    end
  end.

Ltac create_ih_specializations :=
  match goal with
  (* in case the hypothesis is from a previous axiomatization *)
  | [_: ⌊ _ -⌋ = _ |- ?g] => axProjIhAppl g
  | [h:?T |- ?g] => 
    first [axProjIhAppl T (*; idtac "sucessfully called axProjIhAppl on " h ": " T*) |  axProjIhAppl g]
  end; simpl_proj.

Ltac axiomatize_ih_specializations :=
  tryif (repeat_or_fail create_ih_specializations) then idtac else fail "No ih applications to axiomatize".

Ltac axiomatize_next_term :=
  repeat rewrite fix_notation' in *; 
  match goal with
  | |- ?g => first [cleanupSubCastProj g | cleanupExistProj g | axProjTm g | axHOAppProjTm g]
  | [h:?T |- ?g] => tryif (match T with
    (* in case the hypothesis is from a previous axiomatization *)
    | ⌊ _ -⌋ = _ => idtac
    | _ => fail
    end) then fail else first [cleanupSubCastProj T | cleanupExistProj g | axProjTm T | axHOAppProjTm T]
  end; simpl_proj.

Ltac axiomatize_ho_term :=
  repeat rewrite fix_notation' in *; 
  match goal with
  | |- ?g => first [axHOAppProjTm g]
  | [h:?T |- ?g] => tryif (match T with
    (* in case the hypothesis is from a previous axiomatization *)
    | ⌊ _ -⌋ = _ => idtac
    | _ => fail
    end) then fail else first [axHOAppProjTm T]
  end; simpl_proj.

(* replace projections of refined terms in hypothesis or goal by unrefined variables axiomatized using the graph relations *)
Ltac axiomatize_terms := tryif (repeat_or_fail axiomatize_next_term) then idtac else fail "No terms to axiomatize".

(* "unify" context variables axiomatized to correspond to the same unrefined values via graph relations,
  also do various other simpler unification steps to unify/remove redundant hypothesis *)
Ltac simplify_hyp :=
  match goal with
    | [h: ?v = ?w |- _] => isVar v; isVar w;
      (*progress*) first [rewriteRLAll h | rewriteAll h (*| try rewrite <- h in *; clear w h | try rewrite h in *; clear v h *) (*| try rewrite <- h in *; clear w; try clear h*)]
    | [h: ?v = ?t |- _] => isVar v;
      first [subst h | rewriteAll h]
    | [h: ?t = ?v |- _] => isVar v;
      apply eq_sym in h;
      first [subst h | rewriteAll h]
    | [h: ?wff ?tm /\ ?P |- _] => isConstrAppl tm;
      let wff_c_hint := fresh "wff_cr_" in
      destruct h as [wff_c_hint h];
      progress (simpl in wff_c_hint);
      match goal with
      | |- wff _ /\ _ => split; [apply wff_c_hint|]; 
        idtac "Simplified and applied first part of well-formedness assumption " h ", trying to invert second part to attempt to solve the remaining goal. ";
        try (inversion_precheck h; non_branching_inversion h; try assumption)
      | |- wff _ => try (inversion_precheck h; non_branching_inversion h; try assumption)
      | _ => idtac
      end
    | [h: True |- _ ] => first [clear h | replace h with I in * by (auto with pi_db); clear h]
    | [h: ?tm = ?tm |- _ ] => clear h; idtac "Removed trivial hypothesis" h
    | [h1: ?f_rel_ap ?w |- _] => match goal with
      | [h2:f_rel_ap ?v |- _] => first [isVar v | isVar w]; neq_fail h1 h2;
        let temp := fresh "H" in
        assert (v = w) as temp by (unshelve eauto with f_rel_funct_db); 
        (* rewrite variable to term, or keep both around *)
        first [
          isVar v; rewriteAll temp; replace h2 with h1 in * by (auto with pi_db); clear h2
        | isVar w; rewriteRLAll temp; replace h1 with h2 in * by (auto with pi_db); clear h1
        | rewriteAll temp; try clear h2
        ]; idtac "Unified axiomatized variables" v "and" w ". "
      | [h2:f_rel_ap w |- _] => neq_fail h1 h2;
        first [
          replace h2 with h1 in * by (auto with pi_db f_rel_funct_db); clear h2; idtac "Removed redundant hypothesis" h2
          | replace h1 with h2 in * by (auto with pi_db f_rel_funct_db); clear h1; idtac "Removed redundant hypothesis" h1
        ]
      | [h2:f_rel_ap ?v |- _] => neq_fail h1 h2;
        first [isConstrAppl v; isConstrAppl w | 
          let temp := fresh "temp" in
          assert (v <> w) as temp by (intros; discriminate);
          clear temp
        ]; 
        tryif (match goal with
        | [k: v = w |- _] => idtac
        end) then fail else idtac;
        neq_fail v w;
        let H := fresh "eq" in
        assert (v = w) as H by (unshelve eauto with f_rel_funct_db);
        try solve [discriminate H]; try solve [now injection H]
    end
    | [g: ?rel ?s ?t ?u |- _] => isRelAppl rel; match goal with
      | [h: ?rel ?s' ?t' ?v |- u = ?v] => tryif eq_fail u v then reflexivity else 
        concat_either (non_branching_inversion g) (non_branching_inversion h); 
        repeat_or_fail simplify_hyp;
        idtac "Trying to unify variables axiomatized in hypotheses " g h " to solve goal asserting their equality. "; reflexivity
      end
    | [h1: ?frel ?uargs ?v |- _] => isVar v;
      match goal with
        | [h2: frel uargs ?w |- _] => neq_fail v w;
          match goal with
          | [funct: forall (uargs_ : UArgList ?uargTps) (u u' : ?resTp),
            frel uargs_ u -> frel uargs_ u' -> u = u' |- _] =>
            let uargsTp := type of uargs in
            eq_fail uargTps uargsTp;
            let vTp := type of v in
            eq_fail vTp resTp;
            pose proof (funct uargs v w h1 h2) as ->
          end
        end
    | _ => fail "no axiomatized variables to unify"
  end.

Ltac unify_vars := simplify_hyp; repeat simplify_hyp.

Ltac strong_specialize h tm :=
  let temp := fresh "h_specialized" in
  let h' := fresh "h'" in
  first [specialize (h tm) |
    pose proof (h tm) as temp; 
    tryif (
    let resTp := type of temp in
    match goal with
    | [g: ?tp |- _] => eq_fail resTp tp
    end) then fail else (
    try unfold tm in temp; 
    rename_hyp h h';
    rename_hyp temp h)].

Ltac specialize_wit h wit :=
  first [ specialize (h wit) |
    let hTp := type of h in
    let hKnd := type of hTp in
    eq_fail hKnd Prop;
    let H := fresh "temp" in
    assert (forall p', h p' = h wit) as H by (intros; f_equal; now auto with pi_db);
    rewriteAll H; idtac "Rewrote other applications of " h " to " h wit " using proof irrelevance. ";
    try specialize (h wit)].

Tactic Notation "specialize_hyp_ax_wit" hyp(h) constr(v) constr(g) tactic(suc) tactic(fl) :=
  let hApplTp := type of (h v g) in
  tryif (match goal with
    | [hApp':?hAppTp' |- _] => eq_fail hApplTp hAppTp'
    end) then fail else (
    tryif (specialize (h v)) then (
      tryif (specialize_wit h g) then (
        suc
      ) else pose proof (h g)
    ) else (
      tryif (is_trivial hApplTp) then try clear h else
      fl; progress cleanup_witness (h v g)
    )).

Ltac specialize_hyp h :=
  let temp := fresh "H" in
  progress (
    match type of h with
    | forall (w:?T), w = ?tm -> _ => (* idtac "found hypothesis to potentially specialize " ih " with variable " w " of type " T; *)
      specialize (h tm)
    | forall (w:bool), ltbZ_rel ?s ?t w -> _ => 
      specialize (h (s <? t));
      specialize (h (ltac:(constructor)))
    | forall (w:bool), lebZ_rel ?s ?t w -> _ => 
      specialize (h (s <=? t));
      specialize (h (ltac:(constructor)))
    | forall (w:bool), eqbZ_rel ?s ?t w -> _ => 
      specialize (h (s =? t));
      specialize (h (ltac:(constructor)))
    | forall (w:bool), gebZ_rel ?s ?t w -> _ => 
      specialize (h (s >=? t));
      specialize (h (ltac:(constructor)))
    | forall (w:bool), gtbZ_rel ?s ?t w -> _ => 
      specialize (h (s >? t));
      specialize (h (ltac:(constructor)))
    | forall (w:Z), addZ_rel ?s ?t w -> _  => 
      specialize (h (s + t));
      specialize (h (ltac:(constructor)))
    | forall (w:Z), subZ_rel ?s ?t w -> _ => 
      specialize (h (s - t));
      specialize (h (ltac:(constructor)))
    | forall (w:Z), multZ_rel ?s ?t w -> _ => 
      specialize (h (s * t));
      specialize (h (ltac:(constructor)))
    | forall (w:Z), divZ_rel ?s ?t w -> _ => 
      specialize (h (s / t));
      specialize (h (ltac:(constructor)))
    | _ /\ ?T => destruct h as [? h]; try specialize_hyp h
    | exists (w:?T), (?f_rel_ap w) /\ _ => 
      neq_fail T Prop; isRelAppl f_rel_ap;
      let v := fresh "v_" in
      let vdef := fresh "v_def_" in
      destruct h as [v [vdef ?]]
    | exists (w:?T), (?f_rel_ap w) => 
      neq_fail T Prop; isRelAppl f_rel_ap;
      let v := fresh "v_" in
      let vdef := fresh "v_def_" in
      destruct h as [v vdef]
    | forall (w:?T), (?f_rel_ap w) -> _ => 
      neq_fail T Prop;
      (* idtac "found hypothesis to potentially specialize " h " with variable " w " of type " T; *)
      tryif (isRelAppl f_rel_ap) then (
        match goal with
        | [g:f_rel_ap ?v |- _] => 
          (* idtac "Variable " w " in the context has matching axiomatization " g " to specialize " h ". "; *)
          (*tryif (specialize (h v); specialize_wit h g) then (
            let gtp := type of g in
            idtac "Axiomatization " g ": " gtp " of variable " v " is used to specialize " h ". "
          ) else (
            idtac "unable to specialize" h "with" v "!"; fail
          )*)
          specialize_hyp_ax_wit h v g 
            (let gtp := type of g in
            idtac "Axiomatization " g ": " gtp " of variable " v " is used to specialize " h ". ")
            (let hApplTp := type of (h v g) in
            idtac "Unable to specialize" h "with" v "and" g ":" hApplTp "!")
        | _ => 
          let u := fresh "u" in
          let uRefl := fresh "uRefl" in
          do_nonbranching (unshelve refine (let u := (_ : {u:T | f_rel_ap u}) in _); 
          [unshelve (refine (exist _ _ _); econstructor; 
            first [now unshelve eassumption | quick_simpl]; reflexivity); quicksolve|]);
          assert (u = u) as uRefl by reflexivity; subst u;
          match type of uRefl with
          | exist _ ?tm ?z = _ => clear uRefl; 
            specialize_hyp_ax_wit h tm z
              (idtac "Directly specialized " h " with easily synthesizable term. ")
              (idtac "Unable to directly specialize " h "!")
          end
        | _ => fail
        end
      ) else (
        idtac "Not a registered graph relation, so not going to specialize " h " by possibly not unique value. "; fail
      )
    (* specialize with local relation for 1-ary local function *)
    | forall (w:?T), (?f_rel ?x w) -> _ => match goal with
      | [f_funct: forall (y:_) (v1:?T) (v2:?T), f_rel y v1 -> f_rel y v2 -> v1 = v2 |- _] =>
        match goal with
        | [g:f_rel x ?v |- _] => 
          specialize_hyp_ax_wit h v g
            (let gtp := type of g in
            idtac "Axiomatization " g ": " gtp " of variable " v " is used to specialize " h ". ")
            (idtac "Unable to specialize relation for 1-ary function " h "!"; fail)
        end
      end
    (* specialize with local relation for 2-ary local function *)
    | forall (w:?T), (?f_rel ?x1 ?x2 w) -> _ => match goal with
      | [f_funct: forall (y1:_) (y2:_) (v1:?T) (v2:?T), f_rel y1 y2 v1 -> f_rel y1 y2 v2 -> v1 = v2 |- _] =>
        match goal with
        | [g:f_rel x1 x2 ?v |- _] => 
          specialize_hyp_ax_wit h v g
            (let gtp := type of g in
            idtac "Axiomatization " g ": " gtp " of variable " v " is used to specialize " h ". ")
            (idtac "Unable to specialize relation for 2-ary function " h "!"; fail)
        end
      end
    (* specialize with local relation for 3-ary local function *)
    | forall (w:?T), (?f_rel ?x1 ?x2 ?x3 w) -> _ => match goal with
      | [f_funct: forall (y1:_) (y2:_) (y3:_) (v1:?T) (v2:?T), f_rel y1 y2 y3 v1 -> f_rel y1 y2 y3 v2 -> v1 = v2 |- _] =>
        match goal with
        | [g:f_rel x1 x2 x3 ?v |- _] => 
          specialize_hyp_ax_wit h v g
            (let gtp := type of g in
            idtac "Axiomatization " g ": " gtp " of variable " v " is used to specialize " h ". ")
            (idtac "Unable to specialize relation for 3-ary function " h "!"; fail)
        end
      end
    | forall (wit:?r), ?f => match type of r with
      | Prop => 
        let wit := fresh "ref_wit" in
        (* for some reason (potentially a Coq bug) this leads to an infinite loop:
        transparent assert r as wit by (eauto with ref_constr_db); 
        so instead we inline the definition of the Tactic Notation transparent assert *)
        do_nonbranching (unshelve refine (let wit := (_ : r) in _); 
        [try clear h; quick_wff_wit|]);
        let witEq := fresh "witEq" in
        assert (wit = wit) as witEq by reflexivity; unfold wit in witEq; 
        match type of witEq with
        | ?witDef = _ => clear witEq; 
          tryif specialize (h witDef) then idtac else (specialize (h wit)); 
          idtac "Specializing " h " with simple proof term " (* witDef *)
        end
        (* tryif (transparent assert r as wit by (eauto with ref_constr_db); specialize (h wit)) then idtac else (idtac "unable to synthesize proof " r " to specialize " h ". "; fail) *)
      | _ => fail "The Antecedent " r " of hypothesis " h " is not Prop-kinded, so we won't try to specialize it to a proof. "
      end
    | forall (wit:?r), ?f => match type of r with
      | Prop => (* idtac "trying to specialize Prop-kinded antecedent of hypothesis " h; *)

        (* check whether we already have an appropriate hypothesis in the context *)
        match goal with
        | [w:r |- _] => specialize (h w)
        | _ => 
          let wit := fresh "ante" in
          do_nonbranching (unshelve refine (let wit := (_ : r) in _); [try clear h; quicksolve|]);
          let witEq := fresh "witEq" in
          assert (wit = wit) as witEq by reflexivity; unfold wit in witEq; 
          match type of witEq with
          | ?witDef = _ => clear witEq; 

            progress first [
              tryif specialize (h witDef) then idtac else (specialize (h wit)) |
              let temp := fresh "temp_wit" in
              let temp_ih := fresh "temp_ih" in
              assert r as temp by (try clear h; quicksolve); 
              first [specialize (h temp); try clear temp | pose proof (h temp) as temp_ih; clear h; pose proof temp_ih as h; clear temp_ih; try clear temp | clear temp]]; 
            idtac "Specializing " h " with proof term" (* witDef *)
          end; subst wit
        (* in case creating a transparent witness failed, create an opaque one *)
        | _ => let wit := fresh "ante" in
          assert r as wit by quicksolve; specialize (h wit); clear wit
        end
      | _ => fail "The Antecedent " r " of hypothesis " h " is not Prop-kinded, so we won't try to specialize it to a proof. "
      end
    (* | [h: forall v:_, ?relAp v -> _ |- _] => isRelApp relAp; 
      let temp := fresh "temp" in
      unshelve assert (relAp _) as temp by quicksolve;
      specialize (h _ temp); clear temp *)
    | _ /\ _ => destruct h as [? h]; specialize_hyp h; intros
    | _ => fail "No hypothesis with fully axiomatized variables to specialize"
    end
  ).

(* specialize hypothesis/instantiate existentials to fully axiomatized variables *)
Ltac specialize_hyps := 
  repeat_or_fail progress ( 
    match goal with
    | [h: _ |- _] => timeout 10 specialize_hyp h
    end
  ).

Tactic Notation "if_successful" tactic(t) :=
  let temp := fresh "H" in
  tryif (assert True as temp by (t; exact I); clear temp) then idtac else fail.

Ltac nonbranching_invert_axiomatization :=
  let temp := fresh "H" in
  match goal with
    | [h:?f_rel_ap ?v |- _] => isRelAppl f_rel_ap;
      let htp := type of h in
      tryif (non_branching_inversion h) then 
        (idtac "Inverted the axiomatization " h ": " htp;
        repeat axiomatize_next_term)
       else 
        fail 
    | _ => fail "No hypothesis to invert"
    end.

Ltac invert_axiomatization :=
  tryif nonbranching_invert_axiomatization then idtac else
  let temp := fresh "H" in
    match goal with
      | [h:?f_rel_ap ?v |- _] => isRelAppl f_rel_ap;
        let htp := type of h in
        let fAppD := fresh "fAppD" in
        destrApp f_rel_ap fAppD;
        let fAppRefl := fresh "fAppRefl" in
        assRefl fAppD as fAppRefl;
        match type of fAppRefl with
        | ((?f_rel _::_ _nil) _::_ ?ts) = _ => clear fAppRefl; is_rel f_rel;
          tryif (non_branching_inversion h) then 
            idtac "Inverted the axiomatization " h ": " htp else 
            (
            tryif (_any isConstrAppl ts) then 
              (idtac "running strong_inversion on hypothesis " h " : " htp; 
              tryif (strong_inversion h; intros) then repeat axiomatize_next_term else (idtac "Failure to run strong_inversion on " h; fail)) else 
            (fail "Failed to invert " h " : " htp ". ")
            );
          try timeout 1 assumption
        end
      | _ => fail "No hypothesis to invert"
      end.

Tactic Notation "nonbranching_invert_axiomatizations" :=
  repeat_or_fail ( progress nonbranching_invert_axiomatization).

Tactic Notation "invert_axiomatizations" :=
  repeat_or_fail ( progress invert_axiomatization ).

Tactic Notation "get_f_ts" constr(relApp) ident(Res) :=
  let f_ts := fresh "Res" in
  (* idtac "get_f_ts" relApp Res; *)
  destrApp relApp f_ts;
  (* idtac "after destrApp" relApp f_ts; *)
  let temp := fresh "temp" in
  head_res f_ts temp;
  let tail_res := fresh "tail_res" in
  tail_res f_ts tail_res;

  let temp2 := fresh "temp2" in
  let f_res := fresh "f_res" in
  assRefl temp as temp2;
  match type of temp2 with
  | ?frel _::_ _nil = _ => clear temp2; 
    let temp5 := fresh "temp5" in
    assRefl tail_res as temp5; 
    match type of temp5 with
    | ?tl = _ => clear temp5; 
      first [
        pose (getF frel, tl) as Res;
        simpl in Res
      |
        let fres := fresh "f" in
        let fresRefl := fresh "fRefl" in
        localLookupFunc frel fres;
        assRefl fres as fresRefl;
        match type of fresRefl with
        | ?f = _ => clear fresRefl;
          pose (f, tl) as Res
        end
      ]
    end
  end; 
  try clear f_ts.

Ltac assert_wit v pred wit_name := (* idtac "assert_wit" v pred wit_name; *)
  tryif (
  match v with
  | ⌊ ?tm -⌋ => pose ⌈ tm ⌉ as wit_name
  end) then idtac else (
  tryif 
    (match goal with
    | [h:_ |- _] => assert (pred v) as wit_name by (subst pred; exact h); clear wit_name; pose h as wit_name
    end) then idtac else (
  idtac "assert_wit " v pred wit_name; 
  match goal with
  | [h: ?f_rel_ap v |- _] => 
    isRelAppl f_rel_ap; (* idtac "case in assert_wit for unrefined variable axiomatized using the following application of a graph relation: " f_rel_ap; *)

    (* fetch f and the values ts to which f_rel is applied in f_rel_ap *)
    let f_ts := fresh "f_ts" in
    get_f_ts f_rel_ap f_ts; 
    
    let tempEq := fresh "tempEq" in
    assRefl f_ts as tempEq;
    match type of tempEq with
    | (?f, ?ts) = _ => clear tempEq;
      let fApp := fresh "fApp" in
      let fApp' := fresh "fApp'" in
      let tl := fresh "tsTail" in
      let tlEq := fresh "tsTailEq" in
      pose f as fApp;
      pose ts as tl;
      (* recursively assert the refinements of the ts and apply f to them *)
      repeat (
        assRefl tl as tlEq; 
        match type of tlEq with
        | _nil = _ => fail
        | ?t _::_ ?tail = _ => idtac "running main loop in assert_wit with tail " t " _::_ " tail; 
          pose fApp as fApp'; subst fApp;
          
          let dom_ref := fresh "t_dom_ref" in
          get_dom_ref fApp' dom_ref;
          let arg_wit_name := fresh "arg_wit_name_" in

          first [
            assert_wit t dom_ref arg_wit_name
          | let claim := fresh "claim" in
            let claimRefl := fresh "claimRefl" in
            pose (dom_ref t) as claim;
            assRefl claim as claimRefl; 
            unfold dom_ref in claimRefl; simpl in claimRefl; 
            match type of claimRefl with
            | ?tp = _ => clear claimRefl; idtac tp;
              match tp with
              | (?wf ?x /\ ?p) /\ ?q => 
                first [
                  assert_wit x (fun x => wf x /\ p /\ q) arg_wit_name
                | match goal with
                  | [h: ?relAp x |- _] => 
                    isRelAppl relAp; (* idtac "case in assert_wit for unrefined variable axiomatized using the following application of a graph relation: " f_rel_ap; *)

                    (* fetch f and the values ts to which f_rel is applied in f_rel_ap *)
                    let g_ts := fresh "g_ts" in
                    get_f_ts relAp g_ts; 
                    let tempEq := fresh "tempEq" in
                    assRefl g_ts as tempEq;
                    let g := fresh "g" in
                    match type of tempEq with
                    | (?g, ?ts) = _ => clear tempEq;
                      let gdomRef := fresh "gdomRef" in
                      let x_wit := fresh "x_wit_" in
                      get_dom_ref g gdomRef;
                      assert_wit x gdomRef x_wit;
                      assert tp as arg_wit_name by (try split_hyps; try unify_vars; quicksolve)
                    end
                  end
                ]
              end
            end
          ];
          let arg_wit_tp := type of arg_wit_name in
          idtac "recursive call created witness " arg_wit_name " : " arg_wit_tp ". "; 
          pose (fApp' (exist _ t arg_wit_name)) as fApp;
          try subst arg_wit_name; subst fApp'; simpl_proj;
          pose tail as tl
        end; clear tlEq
      ); idtac "finish main loop"; clear tl;
      (* we now have a fully applied version of f in fApp, we destruct it to get the refinement witness for it *)
      let appl_wit := fresh "appl_wit_" in
      pose proof (⌈ fApp ⌉) as appl_wit; subst fApp; simpl_proj; 
      
      let fApplTp := type of appl_wit in
      idtac fApplTp;
      (* try axProjTm fApplTp;*)
      (* tryif destruct fApp as [_ appl_wit] then idtac else idtac "failed to extract the refinement witness from " fApp; *)
      assert (pred v) as wit_name by (unfold pred; simpl; try 
        first [clear pred | subst pred]; first [exact appl_wit; clear appl_wit | quick_wff_wit | quick_simpl; split_hyps; unify_vars; try (specialize_hyps; try unify_vars); try quicksolve; (*print_proof_state;*) timeout 10 (unshelve eauto 50 with solver_db)])
    end

  | _ => (* idtac "fallback case in assert_wit for complicated unrefined values that aren't variables axiomatized using a graph relation"; *)
         assert (pred v) as wit_name by 
          (unfold pred; simpl; try first [clear pred | subst pred]; first [quick_wff_wit | quick_simpl; unify_vars; try (specialize_hyps; try unify_vars); try quicksolve; (*print_proof_state;*) timeout 10 unshelve eauto 50 with solver_db])
  end)); subst pred; simpl in wit_name.

Tactic Notation "assert_ho_relAp" constr(frel) constr(uargs) :=
  match goal with
  | [f_frel : (forall (args : ArgList ?argTps) (v: ?T), ⌊ ?f args -⌋ = v <->
  frel (prArgList args ?uargTps _) v) |- _] => 
    let z := fresh "z" in
    refine (let z: projectsArgListT argTps uargTps := ltac:(quicksolve) in _);
    try simpl in z;
    let temp := fresh "temp" in
    unshelve refine (let temp : {args:ArgList argTps | prArgList args uargTps z = uargs} := 
      ltac:(subst z; synthesize_args) in _); simpl in temp; try subst z;
    let args := fresh "args" in
    let args_def := fresh "args_def" in
    destruct temp as [args args_def];
    let vRes := fresh "w_" in
    let res_def := fresh "w_def_" in
    pose (exist _ (⌊ f args -⌋) eq_refl) as vRes;
    destruct vRes as [vRes res_def];
    rewrite (f_frel args) in res_def;
    match type of res_def with
    | frel ?tm vRes => 
      match type of args_def with
      | ?tm2 = _ => 
        replace tm with tm2 in res_def by solve_pi_unif_subgoal
      end
    end;
    try rewrite args_def in res_def; try clear args_def args;
    idtac "Proven new relation about local function " f " and asserted it. "
  end.

(* takes a function f and an unrefined value v, 
   constructs an appropriate refinement t (with witness (if any) wit_name) of v
   and poses f t as Res *)
Tactic Notation "mk_ref_arg" constr(f) constr(v) ident(wit_name) ident(Res) := 
  (* idtac "mk_ref_arg" f v wit_name Res; *)
  match v with
  | packPr_proj ?pack => (* idtac "pack argument case in mk_ref_arg: " pack; *)
    pose (f pack) as Res
  | _ ::U nilU => fail "higher order case in mk_ref_arg"
  | _ => 
    let dom_ref := fresh "dom_ref" in
    get_dom_ref f dom_ref;
    (* idtac "get_dom_ref" f dom_ref "returned"; *)

    assert_wit v dom_ref wit_name;
    (* idtac "assert_wit" v dom_ref wit_name "returned"; *)
    pose (Res := (f (exist _ v wit_name))); try subst wit_name (*; simpl_proj*)
  end.

Ltac refTmToRef f rtm utm resWit :=
  pose proof ⌈ rtm ⌉ as resWit;
  let rw := fresh "rw" in
  assert (⌊ rtm -⌋ = utm) as rw by ( 
    let temp := fresh "temp" in
    lookupRwLem f temp;
    simpl in temp;
    apply temp; assumption);
  rewrite rw in resWit.

Ltac mkRefAppl f ts Res := (* idtac "mkRefAppl" f ts Res; *)
  match ts with
  | _nil => return Res f
  | ?uargs _::_ _nil => match uargs with
    | _ ::U _ => idtac
    end;
    match goal with
    | [f_frel: forall (args: ArgList ?argTps) (v: ?T), ⌊ f args -⌋ = v <-> ?frel _ v |- _] =>
      assert_ho_relAp frel uargs;
      match goal with
      | [vRes_def: frel uargs ?vRes |- _] => return Res vRes
      end
    end
  | ?t _::_ ?tl => 
    let f_t__res_ := fresh "f_t__res_" in
    let wff_lem := fresh "wit_" in

    match t with
    | ⌊ ?tm -⌋ => pose (f tm) as f_t__res_
    | packPr_proj ?pack => (* idtac "pack argument case in mkRefAppl: " pack; *)
      pose (f pack) as f_t__res_
    | _ => 
      let t_wit := fresh "t_wit" in 
      (* prevent nameclashes with witnesses from recursive calls that use fresh to figure out a name *)
      pose I as t_wit;
      let dom_ref := fresh "dom_ref" in
      get_dom_ref f dom_ref;
      let claim := fresh "claim" in
      let claimRefl := fresh "claimRefl" in
      pose (dom_ref t) as claim;
      assRefl claim as claimRefl; 
      unfold dom_ref in claimRefl; simpl in claimRefl; 
      match type of claimRefl with
      | ?tp = _ => clear claimRefl; 
        (*idtac "claim we need to prove in order to synthesize refined version of argument: " tp;*)
        match tp with
        | _ => clear t_wit; assert tp as t_wit by (assumption)
        | _ => 
          match goal with
          | [h: ?relAp t |- _] => isVar t;
            isRelAppl relAp; 
            (* fetch f and the values ts to which f_rel is applied in f_rel_ap *)
            let g_ts := fresh "g_ts" in
            get_f_ts relAp g_ts; 
            let tempEq := fresh "tempEq" in
            assRefl g_ts as tempEq;
            match type of tempEq with
            | (?g, ?ts) = _ => clear tempEq;
              tryif (_contains t ts) then fail else idtac;
              let gAppl := fresh "gAppl" in
              mkRefAppl g ts gAppl;
              (* idtac "Generated refined term " gAppl " for argument " t ".";*)
              let gAppl_wit := fresh "gAppl_wit" in
              pose proof ⌈ gAppl ⌉ as gAppl_wit;
              let rw := fresh "rw" in
              assert (⌊ gAppl -⌋ = t) as rw by ( 
                let temp := fresh "temp" in
                lookupRwLem g temp;
                simpl in temp;
                apply temp; assumption);
              rewrite rw in gAppl_wit;
              (* let witTp := type of gAppl_wit in
              idtac "witTp: " witTp ", tp: " tp; *)
              clear t_wit;
              assert tp as t_wit by (try apply gAppl_wit; 
                quick_simpl; try split_hyps; try unify_vars; quicksolve)
            end
          end
        | (?wf ?x /\ ?p) /\ ?q =>
          first [
            match goal with
            | [h: ?relAp x |- _] => 
              isRelAppl relAp; 
              (* fetch f and the values ts to which f_rel is applied in f_rel_ap *)
              let g_ts := fresh "g_ts" in
              get_f_ts relAp g_ts; 
              let tempEq := fresh "tempEq" in
              assRefl g_ts as tempEq;
              match type of tempEq with
              | (?g, ?ts) = _ => clear tempEq;
                tryif (_contains x ts) then fail else idtac;
                let gAppl := fresh "gAppl" in
                mkRefAppl g ts gAppl;
                (*idtac "Generated refined term " gAppl " for axiomatized subterm " x " of argument " t ".";*)
                let gAppl_wit := fresh "gAppl_wit" in
                pose proof ⌈ gAppl ⌉ as gAppl_wit;
                let rw := fresh "rw" in
                assert (⌊ gAppl -⌋ = x) as rw by ( 
                  let temp := fresh "temp" in
                  lookupRwLem g temp;
                  simpl in temp;
                  apply temp; assumption);
                rewrite rw in gAppl_wit
              end;
              clear t_wit;
              assert tp as t_wit by (quick_simpl; try split_hyps; try unify_vars; quicksolve)
            end
          ]
        | _ => 
          clear t_wit;
          tryif (assert tp as t_wit by (
            quick_simpl; try split_hyps; try unify_vars; 
            first [quicksolve | 
            
            match goal with
            | |- exists (w:_), ?relAp w /\ _ => isRelAppl relAp;
              let v := fresh "v_" in 
              let f_ts := fresh "Res" in
              get_f_ts relAp f_ts; 

              (* idtac "calling mkRefAppl_res" f_res tail_res fAppl_res; try mkRefAppl_res f_res tail_res fAppl_res; *)
              let temp3 := fresh "temp3" in
              assRefl f_ts as temp3;
              match type of temp3 with
              | (?f, ?ts) = _ => (* idtac "f:=" f;*) clear temp3; mkRefAppl f ts v
              end; try clear f_ts;
              exists v; split; [assumption|]
            end; 
            quick_simpl; try first [ lia | timeout 5 quicksolve];
            repeat match goal with
            | |- ?f ?s ?t => isVar s; idtac s; try subst s
            | |- ?f ?s ?t => isVar t; idtac t; try subst t
            end;
            simpl in *;
            try timeout 10 quicksolve;
            repeat nonbranching_invert_axiomatizations;
            autorewrite with lia_rewrites;
            (let res := fresh "res" in
            match goal with
            | [h: ?relAp ?v |- ?f ?s ?t] => eq_fail v s isRelAppl relAp;
              let f_ts := fresh "Res" in
              get_f_ts relAp f_ts; 

              (* idtac "calling mkRefAppl_res" f_res tail_res fAppl_res; try mkRefAppl_res f_res tail_res fAppl_res; *)
              let temp3 := fresh "temp3" in
              assRefl f_ts as temp3;
              match type of temp3 with
              | (?f, ?ts) = _ => (* idtac "f:=" f;*) clear temp3; mkRefAppl f ts res
              end; try clear f_ts;
              let res_wit := fresh "res_wit" in
              pose proof ⌈ res ⌉ as res_wit;
              let rw := fresh "rw" in
              assert (⌊ res -⌋ = v) as rw by (try subst res; now autorewrite with f_rel_funct_db);
              rewrite rw in res_wit
            | [h: ?relAp ?v |- ?f ?s ?t] => eq_fail v t; isRelAppl relAp; idtac v;
              let f_ts := fresh "Res" in
              get_f_ts relAp f_ts; 

              (* idtac "calling mkRefAppl_res" f_res tail_res fAppl_res; try mkRefAppl_res f_res tail_res fAppl_res; *)
              let temp3 := fresh "temp3" in
              assRefl f_ts as temp3;
              match type of temp3 with
              | (?f, ?ts) = _ => idtac "f:=" f "ts:=" ts; clear temp3; mkRefAppl f ts res
              end; try clear f_ts;
              let res_wit := fresh "res_wit" in
              pose proof ⌈ res ⌉ as res_wit;
              let rw := fresh "rw" in
              assert (⌊ res -⌋ = v) as rw by (try subst res; now autorewrite with f_rel_funct_db);
              try rewrite rw in res_wit
            end
            );
            repeat nonbranching_invert_axiomatizations;
            autorewrite with lia_rewrites;
            quicksolve

            ])) then
            idtac else fail "No known way to prove the refinement of " tp
        end
      end;
      idtac "Created witness " t_wit " for argument " t " of graph relation for " f;
      pose (f (exist dom_ref t t_wit)) as f_t__res_
    end;

    (* idtac "mk_ref_arg returned"; *)
    let temp_2 := fresh "temp_2" in
    assRefl f_t__res_ as temp_2;
    match type of temp_2 with
    | ?fapp = _ => clear temp_2;
      (* idtac "Recursing in mkRefAppl with function " fapp " and arguments " tl;*)
      mkRefAppl fapp tl Res
    end
  end.

Tactic Notation "recreate_refined_term" constr(relApp) ident(fAppl_res) := 
  let f_ts := fresh "Res" in
  get_f_ts relApp f_ts; 

  (* idtac "calling mkRefAppl_res" f_res tail_res fAppl_res; try mkRefAppl_res f_res tail_res fAppl_res; *)
  let temp3 := fresh "temp3" in
  assRefl f_ts as temp3;
  match type of temp3 with
  | (?f, ?ts) = _ => (* idtac "f:=" f;*) clear temp3; mkRefAppl f ts fAppl_res
  end; 
  try clear f_ts.

Ltac nonbranching_destruct :=
  match goal with
  | [v: ?Tp |- _] => replace v with v by reflexivity;
    tryif (match Tp with
      | _ == _ => idtac
      | _ = _ => idtac 
      end) then fail else idtac;
    do_nonbranching (destruct v(*; idtac "Destructed the variable " v " of an inductive data type with only one constructor." *) )
  end.

Tactic Notation "recreate_var" constr(relApp) ident(vRes) := 
  match relApp with
  (*| _ => isRelAppl relApp;
    let temp := fresh "temp" in
    let v := fresh "v_" in 
    let v_def := fresh "v_def_" in
    assert (exists v, relApp v) as temp by (time (timeout 60 solve [
      now unshelve (eexists _; rconstructor)
    | timeout 12 repeat nonbranching_destruct; 
      now unshelve (eexists _; rconstructor)
    ]));
    destruct temp as [vRes v_def]*)
  | _ ?v => isVar v; match goal with
    | [def: ⌊ ?tm -⌋ = v |- _] => pose (exist _ v ⌈ tm ⌉) as vRes
    end
  | ?frel ?uargs =>
    match type of frel with
    | forall (_:UArgList ?uargTps) (_:?T), Prop =>
      let fAppl_res := fresh "fAppl_res" in
      let res_def := fresh "res_def" in
      assert_ho_relAp frel uargs
    end
  | _ =>
    let fAppl_res := fresh "fAppl_res" in
    recreate_refined_term relApp fAppl_res;
    (* simpl_proj; *) simpl in fAppl_res;
    (* idtac "Sucessfully generated refined result term in recreate_var"; *)
    
    let Res := fresh "fAppl_Res" in
    let v := fresh "fAppl_v" in
    let v_p := fresh "fAppl_p" in
    pose (⌊ fAppl_res -⌋) as Res; 
    axiomatize_term fAppl_res as v v_p; subst Res; 
    (*try (
      match goal with
      | [h: ⌊ fAppl_res -⌋ = v |- _] => let tmp := fresh "v_p" in
        pose proof (⌈ fAppl_res ⌉) as tmp;
        rewrite h in tmp
      end
    );*)
    (*try cleanup_witness ⌈ fAppl_res ⌉;*)
    (* idtac "Sucessfully axiomatized projection of refined result term in recreate_var";*)
    try rewrite v_p in *; 
    let pTp := type of v_p in
    match pTp with
    | ?relAp v => isRelAppl relAp
    | _ => tryif (applyRwLem v_p) then idtac else 
      (fail (* "Failed to rewrite " v_p ": " pTp " from an equality into the application of the graph relation. "*))
    end;
    match type of v_p with
    | ?relAp ?w => simpl_proj; 
      pose w as vRes; 
      idtac "Sucessfully recreated axiomatized unrefined variable by recreating and axiomatizing refined term ";
      try clear fAppl_res
    end
  end.

Ltac simplInstExistGoal :=
  match goal with
  | [vdef: ?relAp ?V |- exists (w:_), ?relAp w /\ _] => isRelAppl relAp;
    exists V; split; [apply vdef|]
  | [vdef: ?relAp ?v |- exists (w:_), ?relAp w] => isRelAppl relAp;
    exists v; apply vdef
  | [vdef: ?relAp ?v |- exists (w:_), ?relAp w /\ _] => isRelAppl relAp;
    exists v; split; [apply vdef|]
  | [h: exists v, ?relAp v |- exists (w:_), ?relAp w] => isRelAppl relAp;
    let v := fresh "v_" in 
    let v_def := fresh "v_def_" in 
    destruct h as [v v_def];
    exists v; apply v_def
  | [h: exists v, ?relAp v /\ _ |- exists (w:_), ?relAp w] => isRelAppl relAp;
    let v := fresh "v_" in 
    let v_def := fresh "v_def_" in 
    destruct h as [v [v_def ?]];
    exists v; apply v_def
  | |- exists (w:_), ?relAp w /\ _ => isRelAppl relAp;
    tryif (match goal with
    | [h: exists (w:_), relAp w |- _] => idtac
    | [h: relAp _ |- _] => idtac
    end) then fail else
    let temp := fresh "temp" in
    let v := fresh "v_" in 
    let v_def := fresh "v_def_" in
    assert (exists (w:_), relAp w) as temp; 
    [|destruct temp as [v v_def]; exists v; split; [apply v_def|]]
  | |- exists v, ?relAp v => isRelAppl relAp;
  	timeout 1 solve [
      now unshelve (eexists _; rconstructor)
    ]
  | |- exists (w:_), ?relAp w => isRelAppl relAp;
    let v := fresh "v_" in 
    recreate_var relAp v;
    exists v; try first [
      assumption
    | idtac "Couldn't discharge defining constraint of formerly existentially quantified variable " v "!";
      try easy ]
  | |- exists (w:_), ?relAp w => isRelAppl relAp;
    (* inversion_precheck_tm relAp;*)
    now unshelve (eexists _;
    econstructor; 
    try match goal with
    | [h: ?relAp ?v |- ?relAp _] => isRelAppl relAp; exact h
    end;
    cleanup_pack_stuff; simpl;
    match goal with
    | |- ?frelAp _ => isRelAppl frelAp;
      let v_ := fresh "v_" in
      recreate_var frelAp v_;
      solve [unshelve eassumption]
    end)
  | |- exists v, ?frel ?uargs v => localIsRel frel;
    let fAppl_res := fresh "fAppl_res" in
      let res_def := fresh "res_def" in
    assert_ho_relAp frel uargs;
    match goal with
    | [vRes_def: frel uargs ?vRes |- _] =>
      exists vRes; apply vRes_def
    end
  | |- ?frel ?uargs _ => localIsRel frel;
    let fAppl_res := fresh "fAppl_res" in
      let res_def := fresh "res_def" in
    assert_ho_relAp frel uargs;
    solve [unshelve eassumption]
  | |- exists v, ?relAp v /\ ?tm == v => exists tm
  | |- exists v, ?relAp v /\ v == ?tm => exists tm
  end.

Ltac instExistGoal :=
  match goal with
  | |- _ => simplInstExistGoal
  (* in case we need to destruct an argument in order to instantiate this *)
  | [t: ?Tp |- exists v, ?relAp v] => isRelAppl relAp;
    tryif (match Tp with
    | _ => let knd := type of Tp in
      eq_fail knd Prop
    end) then fail else idtac;
    now unshelve (
      match relAp with
      | ?rel ?t v => idtac "Destructing " t " to simplify producing result term for " v;
        destruct t; timeout 3 simplInstExistGoal
      | ?rel ?t _ v => idtac "Destructing " t " to simplify producing result term for " v;
        destruct t; timeout 3 simplInstExistGoal
      | ?rel ?t _ _ v => idtac "Destructing " t " to simplify producing result term for " v;
        destruct t; timeout 3 simplInstExistGoal
      | ?rel ?t _ _ _ v => idtac "Destructing " t " to simplify producing result term for " v;
        destruct t; timeout 3 simplInstExistGoal
      | ?rel ?t _ _ _ _ v => idtac "Destructing " t " to simplify producing result term for " v;
        destruct t; timeout 3 simplInstExistGoal
      end)
  end.

(* create variables to instantiate hypothesis *)
Ltac instantiate_hyp :=
  (* assert_fails (specialize_hyps); *)
  match goal with
  | [ih: forall (z: Z), addZ_rel ?s ?t z -> _ |- _] => simpl_specialize ih (s + t)
  | [ih: forall (z: Z), subZ_rel ?s ?t z -> _ |- _] => simpl_specialize ih (s - t)
  | [h: forall (w:?T), ?frel ?uargs w -> ?rtp |- _] => 
    assert_ho_relAp frel uargs
  | [ih: forall (w:?T), ?f_rel_ap w -> ?rtp |- _] => 
    isRelAppl f_rel_ap; 
    tryif (match goal with
    | [h: rtp |- _] => 
      idtac "No point specializing " ih " a hypothesis " h " of the type of the specialization (without the defining axiom) already exists in the context, instead removing " ih ". "
    end) then clear ih
    else (

      (* idtac "Trying to create the variable " w " of hypothesis " ih (* " axiomatized as " f_rel_ap w *); *)
      let vRes := fresh "vRes" in
      
      first [
        recreate_refined_term f_rel_ap vRes;
        let witTp := type of (⌈ vRes ⌉) in
        let v_wit := fresh "v_wit" in
        match goal with
        | [h: ?htp |- _] => eq_fail witTp htp (*; idtac "A witness for the refined term " tm " is already present as hypothesis " h " not asserting another. " *)
        | _ => assert _ as v_wit by (let temp := fresh "temp" in pose ⌈ vRes ⌉ as temp; unfold vRes in temp; exact temp; clear temp)
        end;
        simpl in vRes;
        pose (exist _ (⌊ vRes -⌋) eq_refl) as vRef;
        subst vRes;
        let v := fresh "v" in
        let v_p := fresh "v_p" in
        destruct vRef as [v v_p];
        applyRwLem v_p; simpl in v_p;
        specialize (ih v); specialize_wit ih v_p;
        let wit_tp := type of v_wit in
        try (axProjTm wit_tp)
      |
        recreate_var f_rel_ap vRes; 
        idtac "Re-created a refined term for the axiomatized variable " w " and posed it as " vRes; (* print_res vRes; *)
        let ihApplTp := type of (ih vRes) in
        tryif (match goal with
        | [h: ihApplTp |- _] => clear vRes; 
          idtac "No point specializing " ih " a hypothesis " h " of the type of the specialization already exists in the context, instead removing " ih ". "
        end) then clear ih else
        (
          tryif (first [specialize (ih vRes) | pose proof (ih vRes); try clear ih]) then idtac else (idtac "unable to instantiate the hypothesis " ih " with the freshly created variable " vRes " of expected type " T; fail);
          tryif (first [subst vRes | unfold vRes in ih; try clear vRes]) then idtac else (idtac "unable to unfold the freshly created variable " vRes " in the hypothesis " ih; fail)
        )
      |
        recreate_refined_term f_rel_ap vRes;
        let witTp := type of (⌈ vRes ⌉) in
        let v_wit := fresh "v_wit" in
        match goal with
        | [h: ?htp |- _] => eq_fail witTp htp (*; idtac "A witness for the refined term " tm " is already present as hypothesis " h " not asserting another. " *)
        | _ => assert _ as v_wit by (let temp := fresh "temp" in pose ⌈ vRes ⌉ as temp; unfold vRes in temp; exact temp; clear temp)
        end;
        simpl in vRes;
        pose (exist _ (⌊ vRes -⌋) eq_refl) as vRef;
        subst vRes;
        let v := fresh "v" in
        let v_p := fresh "v_p" in
        destruct vRef as [v v_p];
        applyRwLem v_p; simpl in v_p;
        idtac "Unable to specialize " ih " with newly created axiomatized variable " v;
        strong_specialize (ih v)
      ]
    )
  | _ => fail (* "No hypothesis with fully axiomatized variables to specialize" *)
  end.

Ltac instantiate_hyps := repeat_or_fail instantiate_hyp.

Ltac instantiate_goal := 
  match goal with
    | |- exists (z:Z), _ => instantiate_lia_goal
    | [h: ?f_rel_ap ?v |- exists (w:?tp), (?f_rel_ap w) /\ ?p ] => 
      isRelAppl f_rel_ap; 
      idtac "instanciating the existential in the goal with " v;
      exists v; 
      split; [assumption|]
    | [h: ?f_rel_ap ?v |- exists (w:?tp) (_:_), ?f_rel_ap w ] => 
      isRelAppl f_rel_ap;
      exists v; 
      idtac "instanciating the existential variable at the end of the goal with " v
    | [h: ?f_rel_ap ?v |- exists (w:?tp), ?p ] => 
      let temp := fresh "temp" in
      assert (forall (w:tp), p -> f_rel_ap w) as temp by intuition;
      exists v; clear temp
    | |- exists (v:?tp), ?res = ?ConstrApp ?res /\ ?q =>
      tryif (isVar res) then try subst res else idtac
    | |- exists (v:?tp), ?ConstrApp ?res = ?ConstrApp v /\ ?q =>
      exists (res); split; [reflexivity|]
    | [f_frel : (forall (args : ArgList ?argTps) (v : ?tp), ⌊ ?f args -⌋ = v <->
      ?frel (prArgList args ?uargTps _) v) |- exists (w:?tp), ?frel ?uargs w /\ ?p] => 
       refine (instantiate_frel_res (fun w => p) f_frel _ _);
       [try synthesize_args|intros ? ?]
    | _ => fail "Goal doesn't contain existentially quantified variables we can instantiate"
  end.

Ltac instantiate_goals := repeat_or_fail instantiate_goal.

Create HintDb f_rel_db.
Create HintDb f_rel_back.
Create HintDb f_rel_funct_db.

Ltac saturate_axiom relApp w :=
  let v_ref := fresh "v_ref" in
  let v := fresh "v" in
  let v_def := fresh "v_def" in
  let temp := fresh "temp_rw" in
  let v_wit := fresh "v_wit" in
  
  (* Todo: destruct relApp using destrApp, fetch f using getF, fetch its return type using destrFunc and check if the refinement is trivial or already in the context *)
  idtac "Creating a refined term for variable " w;
  recreate_refined_term relApp v_ref;

  pose proof ⌈ v_ref ⌉ as v_wit;
  cbv beta in v_wit;
  axiomatize_term v_ref as v v_def;
  
  applyRwLem v_def;
  simpl_proj;
  assert (v = w) as temp by (unshelve eauto with f_rel_funct_db; quicksolve);
  rewriteAll temp;
  clear v_def; 

  let witTp := type of v_wit in
  idtac "Created witness " v_wit " of the fact " witTp;
  tryif (
    match goal with
    | [k: ?tp |- _] => 
      eq_fail tp witTp; neq_fail v_wit k;
      idtac "A witness for variable " w " of type " witTp " is already present in the context: " k;
      clear v_wit;
      idtac
    | _ => fail
    end
  ) then (idtac "Not creating superfluous witness. "; fail) 
    else idtac "Sucessfully created witness " v_wit.
  
Ltac saturate_given_hyps hyps :=
  match hyps with
  | _nil => idtac
  | ?h _::_ ?tl => match type of h with
    | ?relApp ?w => idtac "Saturating hypothesis " h;
      tryif (saturate_axiom relApp w) then (try saturate_given_hyps tl) else saturate_given_hyps tl
    end
  end.

Ltac hyps_to_saturate Res :=
  return Res _nil;
  repeat progress (match goal with
    | [h: _ |- _] => tryif (contains_res h Res) then fail else (
        match type of h with
        | addZ_rel _ _ ?z => (* idtac "No meaningful postcondition to create the variable " z; *) fail
        | subZ_rel _ _ ?z => (* idtac "No meaningful postcondition to create the variable " z; *) fail
        (* optimization to avoid uselessly saturating hypothesis, when the appropriate hypothesis already exists *)
        | ?rel _ _ ?w => isVar w; is_rel rel; 
          match type of (getF rel) with
          | forall _ _, {_: ?cod | ?ref} => 
            let refTp := fresh "refTp" in
            pose proof ref as refTp;
            simpl in refTp;
            tryif (match goal with
            | [g: ?gtp |- _] => eq_fail gtp refTp
            end) then idtac else prepend_res Res h
          end
        | ?rel _ ?w => isVar w; is_rel rel; 
          match type of (getF rel) with
          | forall _, {_: ?cod | ?ref} => 
            let refTp := fresh "refTp" in
            pose proof ref as refTp;
            simpl in refTp;
            tryif (match goal with
            | [g: ?gtp |- _] => eq_fail gtp refTp
            end) then idtac else prepend_res Res h
          end
        | ?relApp ?w => isVar w; isRelAppl relApp; prepend_res Res h
        end
      )
    end).

Ltac saturate_context := 
  let hypsToSat := fresh "hypsToSat" in
  let hypsToSatRefl := fresh "hypsToSatRefl" in
  idtac "Saturating context. ";
  hyps_to_saturate hypsToSat;
  assRefl hypsToSat as hypsToSatRefl;
  match type of hypsToSatRefl with
  | ?hyps = _ => clear hypsToSatRefl; saturate_given_hyps hyps
  end.

(* remove refined terms from the proof state *)
Ltac remove_refined :=
  concat_either 
    (axiomatize_ih_specializations; quick_simpl)
    (concat_either (axiomatize_terms; quick_simpl) (progress autorewrite with f_rel_funct_db in *)).

Ltac quick_simple_cleanup_steps :=
  repeat unfold rel_u in *;
  simpl_proj; (* repeat progress autounfold with lia_unfold in *; repeat progress autorewrite with lia_rewrites in *; *)
  concat_either (unify_vars) (
    concat_either (instExistGoal; repeat instExistGoal)
    (specialize_hyps; try unify_vars));
  try timeout 1 simpl_loop.

Ltac initial_simple_cleanup_steps :=
  quick_simpl; 
  repeat progress autounfold with lia_unfold in *;
  simpl_proj;
  concat_either 
    (concat_either (cleanup_pack_stuff) (unpack_all); cleanup_pack_stuff)
    (concat_either (remove_refined) (quick_simple_cleanup_steps)).

Ltac simple_cleanup_steps :=
  quick_simpl; 
  repeat progress autounfold with lia_unfold get_rel_db in *;
  quick_simple_cleanup_steps.

Ltac nonbranching_inversion_specialization :=
  concat_either 
    (nonbranching_invert_axiomatizations; try quick_simple_cleanup_steps) 
    (instantiate_hyps; try specialize_hyps).

Ltac inversion_specialization :=
  concat_either 
    (invert_axiomatizations; try quick_simple_cleanup_steps) 
    (instantiate_hyps; try specialize_hyps).

Ltac inversion_cleanup := 
  concat_either 
    (* forward reasoning *)
    try cleanup_pack_stuff;
    (concat_either (quick_simple_cleanup_steps)
      (repeat_or_fail (reconstruct_ref)))
    (* backwards reasoning *)
    (concat_either 
      (* backwards reasoning in hypotheses *)
      (nonbranching_inversion_specialization)
      (* backwards reasoning in goal *)
      (concat_either (unshelve constructor; timeout 3 quicksolve) 
        (concat_either (progress (autorewrite with f_rel_back; autorewrite with int_rel_back)) 
          (* forwards reasoning in goal *)
          (concat_either (instExistGoal) (instantiate_goals)));
       try quick_simple_cleanup_steps
      )); try simple_cleanup_steps.

Ltac initial_cleanup_recurse := 
  quick_simpl;
  concat_either 
    (initial_simple_cleanup_steps)
    (repeat instExistGoal; unshelve inversion_cleanup). (* TODO: move the unshelve into whatever tactic actually populates the shelf *)

Ltac cleanup_recurse := 
  quick_simpl;
  concat_either 
    (simple_cleanup_steps)
    (unshelve inversion_cleanup). (* TODO: move the unshelve into whatever tactic actually populates the shelf *)

Ltac cleanup_ saturate :=
  (* we need to call the saturate_context tactic potentially before AND after inverting hypothesis *)
  match saturate with
  | True => 
    quick_simpl; 
    concat_either
      (concat_either (saturate_context)
        (progress initial_cleanup_recurse))
      (concat_either 
        (saturate_context)
        (repeat_or_fail (progress cleanup_recurse)))
  | _ => progress initial_cleanup_recurse; repeat (progress cleanup_recurse)
  end.

Ltac cleanup := cleanup_ False.

Ltac cleanup_after_hints_ saturate := 
  (* simpl in *; *)
  match saturate with
  | True => repeat unshelve cleanup_hints; 
    cleanup_ True
  | _ => repeat unshelve cleanup_hints; 
    cleanup
  end.

Ltac cleanup_after_hints := cleanup_after_hints_ False.

(* This ugly hack is to prevent exported notations/definitions in SMTCoq or Sniper to clash with other notations/definitions
Considering we cannot selectively import tactic notations (e.g. snipe) or qualify the recursive imports this seems to be the only semi-robust way
Without this SMTCoq.SMT_terms.Atoms.eqb will clash with Bool.eqb (amongst many other issues).
 *)

(* From coqDeps Require Export Snipe. *)

Ltac snipe := 
  idtac "Running sniper in proof state: ";
  print_proof_state;
  trivial (*smt*).

(* to ensure the default names are the ones in the Bool module *)
Require Import Bool.

(* Arguments exist [A]%type_scope P%function_scope x _. *)

Ltac finish := idtac "Calling finish"; solve [ 
  repeat progress first [unshelve eauto with ref_constr_db wff_constr_db | split | split_hyps ] 
  | quicksolve | quick_simpl; timeout 5 snipe ].

Ltac oracle_ := first [ 
  quick_wff_wit
  | quicksolve 
  | try cleanup_after_hints; try quicksolve; split_hyps; try progress (cleanup_after_hints; split_hyps); try cleanup; finish ].

Ltac strong_oracle := timeout 600 first [ 
  quick_wff_wit
  | quicksolve 
  | try cleanup_after_hints_ True; try quicksolve; split_hyps; try progress (cleanup_after_hints_ True; split_hyps); try cleanup; finish ].

Ltac oracle := timeout 150 oracle_.

Ltac deadBranch := intros; exfalso; oracle.

Ltac default_tactic := try program_simpl; oracle.

(** Advanced tactics for the more structural parts of the translation **)

Tactic Notation "assertHint" open_constr(tm) :=
  let H := fresh "hint" in
  match type of tm with
  | {_ : Unit | ?p} => unshelve epose proof (⌈ tm ⌉) as H
  | _ => match goal with
    | [h:_ |- _] => eq_fail h tm; idtac "The term " tm " to assert as a hint is already a hypothesis, so we won't assert it again."
    | [ |- _ ] => unshelve epose proof tm as H
    end
  end; try quicksolve
  (*first [
    unshelve epose proof tm as H; try quicksolve |
    unshelve (assert _ as H by (unshelve refine tm; oracle)); try quicksolve
  ] *).

Tactic Notation "retCast'" open_constr(tm) :=
  let H := fresh "hint" in
  let tmTp := type of tm in
  let tmKind := type of tmTp in 
  unshelve (match goal with
  | [ |- ?g ] =>
    let gKind := type of g in
    match g with
    (* tm has the same type as g *)
    | _ => eq_fail g tmTp; unshelve refine tm
    (* tm is a Prop, so we assert it *)
    | _ => eq_fail tmKind Prop; 
      match goal with
      | [ h:_ |- _] => eq_fail h tm; idtac "The term to retCast is already a hypothesis, so we won't assert it again and do nothing."
      | [ |- _] => idtac "found a Prop-kinded term to retCast, so running: "; idtac "unshelve epose proof " tm " as " H
      end
    (* the hint is a refinement of unit, typically a theorem call *)
    | _ => neq_fail tmKind Prop; match tmTp with
      | {_:Unit | _} => unshelve epose proof tm as H; simpl_proj; try (timeout 20 oracle); destruct H as [_ H]
      end
    | {v:?a | ?p} => neq_fail tmKind Prop; match tmTp with
      (* we need to add an injection cast *)
      | a => unshelve refine (exist _ tm _)
      (* we need to add an subsumption cast *)
      | {v:a | ?q} => unshelve refine (subsumptionCast _ _ tm _)
      end
    | forall (x:?rt), ?cod => neq_fail tmKind Prop; match tmTp with
      | forall (y:?rt'), ?cod' => 
        let subWitDom := fresh "subWitDom" in
        let subWitCod := fresh "subWitCod" in
        let subWitFunc := fresh "subWitFunc" in
        unshelve assert (sub rt rt') as subWitDom by (oracle);
        unshelve assert (sub cod' cod) as subWitCod by (oracle);
        unshelve assert (sub tmTp g) as subWitFunc by (unshelve eapply sub_fun; oracle);
        unshelve refine (subCast _ _ tm subWitFunc)
      end
    | ?a => neq_fail tmKind Prop; match tmTp with
      (* we need to project *)
      | {v:a | ?p} => unshelve refine (⌊ tm -⌋)
      end
    (* fallback case, we cannot cast tm to the type of the goal *)
    | _ => neq_fail tmKind Prop; match goal with
      (* we already have tm as a hypothesis, so we ignore this retCast completely *)
      | [ h:_ |- _] => eq_fail h tm; idtac "The term to retCast is already a hypothesis, so we won't assert it again."
      (* we don't have tm as hypothesis yet, so we assert it *)
      | [ |- _] => unshelve epose proof tm as H; try (timeout 20 oracle)
      end
    end
  end).

Ltac retCast tm := unshelve retCast' tm; try (oracle).

(** Custom tactics **)

Ltac rel_functionhood_body := 
  quick_simpl; 
  try unpack;
  (* invert hypotheses H and K *)
  match goal with
  | [H: ?relApp ?x |- _] => isVar x; (* found hypothesis H *)
    match goal with
    | [K: ?relApp' ?x' |- _] => isVar x'; neq_fail H K; (* found hypothesis K *)
      strong_inversion H; strong_inversion K; try quicksolve
    end
  end; 
  first [
    solve [ now unify_vars ]
  | progress unfold rel_u in *; try unpack_all; 
    solve [ now unify_vars ]
  ].
  (* try inversion_specialization; try cleanup; try oracle*)

(* Tactic to prove the functionhood lemma for the graph relations *)
Ltac rel_functionhood indVars :=
  intros x x' H K; 
  multivariable_induction indVars _nil (x _::_ x' _::_ H _::_ K _::_ _nil); 
  rel_functionhood_body.

Global Tactic Notation "rconstructor" "by" tactic(tac) := first [
    unshelve econstructor; try (quick_simpl; reflexivity); tac |
    unshelve econstructor 1; try (quick_simpl; reflexivity); tac |
    unshelve econstructor 2; try (quick_simpl; reflexivity); tac |
    unshelve econstructor 3; try (quick_simpl; reflexivity); tac |
    unshelve econstructor 4; try (quick_simpl; reflexivity); tac |
    unshelve econstructor 5; try (quick_simpl; reflexivity); tac |
    unshelve econstructor 6; try (quick_simpl; reflexivity); tac
  ].

Ltac contradicts_brel_hyp p :=
  match goal with
  | [h:?relApp true |- _] => isRelAppl relApp;
    match p with
    | relApp false => idtac
    | relApp false /\ _ => idtac
    | _ /\ relApp false => idtac
    end
  | [h:?relApp false |- _] => isRelAppl relApp;
    match p with
    | relApp true => idtac
    | relApp true /\ _ => idtac
    | _ /\ relApp true => idtac
    end
  | |- _ => 
    match p with
    | ?q \/ ?r => contradicts_brel_hyp q; contradicts_brel_hyp r
    | ?q /\ ?r => first [contradicts_brel_hyp q | contradicts_brel_hyp r]
    | exists _, ?q => contradicts_brel_hyp q
    | exists (v:?vTp), ?p /\ ?q => first [contradicts_brel_hyp p | contradicts_brel_hyp q]
    | exists (v:?vTp), (?p /\ ?q) /\ ?r => first [contradicts_brel_hyp p | contradicts_brel_hyp q | contradicts_brel_hyp r]
    end
  end.

Ltac destruct_disjs_pre := repeat (match goal with
  | [h:_ \/ _ |- _] => destruct h
  | [ h: negb ?v = true |- _] => isVar v; apply isTrue_neg in h; try rewrite h in *
  | [h: (?s <? ?t) = ?b |- _] => apply eq_sym in h; apply ltbZ_rel_rw in h
  | [h: (?s >? ?t) = ?b |- _] => apply eq_sym in h; apply gtbZ_rel_rw in h
  | [h: (?s <=? ?t) = ?b |- _] => apply eq_sym in h; apply lebZ_rel_rw in h
  | [h: (?s >=? ?t) = ?b |- _] => apply eq_sym in h; apply gebZ_rel_rw in h
  end).

Ltac destruct_disjs := first [destruct_disjs_pre; match goal with
  | |- ?p \/ ?q => contradicts_brel_hyp p; 
    idtac "Picking right branch as the left one is contradictory"; right
  | |- ?p \/ ?q => contradicts_brel_hyp q; 
    idtac "Picking left branch as the right one is contradictory"; left
  end | progress destruct_disjs_pre].

Ltac destruct_hyp :=
  match goal with
  | [h: (?p && ?q) = true |- _] =>
    unfold Init.Datatypes.andb in h;
    destruct p eqn:?; [|easy]
  | [h: (?p /\ ?q) |- _ ] =>
    let Hl := fresh "Hl" in
    let Hr := fresh "Hr" in
      destruct h as [Hl Hr]
  | [h: exists v, _ |- _] => destruct h as [v h]
  | [h: ?res = (?s <? ?t) |- _] => rewrite <- ltbZ_lem in h
  | [h: ?res = (?s <=? ?t) |- _] => rewrite <- lebZ_lem in h
  | [h: ?res = (?s >? ?t) |- _] => rewrite <- gtbZ_lem in h
  | [h: ?res = (?s >=? ?t) |- _] => rewrite <- gebZ_lem in h
  | [h:_ \/ _ |- _] => destruct h
  end.

Ltac destruct_hyps := repeat destruct_hyp.

(* tactic to prove the goal backwords reasoning lemmata for the constructors of the graph relations *)
Ltac rel_back' conds := intros; split; 
  [intro_inv; try now unify_vars; repeat shape_based; destruct_conds conds; try unify_vars; repeat shape_based; 
   repeat destruct_disjs; repeat split|]; repeat destruct_disjs;
   try solve [repeat progress (quick_simpl; instantiates_lia_goal); try fast_done; 
   repeat eexists; 
   solve [repeat first [ unshelve eassumption | easy | unify_vars | left; quicksolve | right; quicksolve | quicksolve]]]; 
   intros; destruct_conds conds; destruct_hyps; repeat shape_based; try unify_vars; quick_simpl; subst; 
   repeat progress (quick_simpl; instantiates_lia_goal); 
   try quicksolve; repeat (destruct_disjs; try split_hyps; repeat shape_based); 
   try split_hyps; repeat shape_based; destruct_hyps; 
   try rconstructor; try quicksolve.

(* tactic to prove the goal backwords reasoning lemmata for the constructors of the graph relations *)
Ltac rel_back rel_constr := split; 
  [intro_inv; repeat eexists; quicksolve | quick_simpl; subst; eapply rel_constr; eassumption].

Create HintDb rel_ax_db.

(* Preprocessor steps utilizing the oracle tactic internally *)
Ltac lia_preprocessor_step := match goal with 
  | |- proj _ = ?v => isVar v; unfold proj
  | |- _ => progress split_hyps
  | |- (?c = true /\ _) \/ (?c = false /\ _) => 
    let H := fresh "H" in
    tryif (assert (c = true) as H by (repeat shape_based; timeout 10 oracle))
      then (
        idtac "Able to prove (" c " = true) using oracle tactic, choosing left disjunct (of goal) and filling in proof for its first conjunct. ";
        left; split; [apply H|]
      ) else (
        assert (c = false) as H by (repeat shape_based; timeout 10 oracle);
        idtac "Able to prove (" c " = false) using oracle tactic, choosing right disjunct (of goal) and filling in proof for its first conjunct. ";
        right; split; [apply H|]
      )
  | |- (?c /\ _) \/ ?d => 
    let H := fresh "H" in
    tryif (assert (c) as H by (timeout 10 oracle))
      then (
        idtac "Able to prove (" c ") using oracle tactic, choosing left disjunct (of goal) and filling in proof for its first conjunct. ";
        left; split; [apply H|]
      ) else (
        assert (not c) as H by (timeout 10 oracle);
        idtac "Able to prove ( not " c ") using oracle tactic, choosing right disjunct (of goal). ";
        right; split; try quicksolve
      )
  
  | [h: ?s = ?t |- ?t = _] => solve [unshelve etransitivity; [|apply eq_sym in h; apply h|]; timeout 3 oracle]
  | [h: ?s = ?t |- ?s = _] => solve [unshelve etransitivity; [|apply h|]; timeout 3 oracle]
  | [h: ?s = ?t |- _ = ?t] => solve [symmetry; unshelve etransitivity; [|apply eq_sym in h; apply h|]; timeout 3 oracle]
  | [h: ?s = ?t |- _ = ?s] => solve [symmetry; unshelve etransitivity; [|apply h|]; timeout 3 oracle]

  | [ h: ltbZ_rel ?s ?t ?u |- _] => apply ltbZ_rel_rw in h; 
    try (isVar u; subst u)
  | [ h: lebZ_rel ?s ?t ?u |- _] => apply lebZ_rel_rw in h; 
    try (isVar u; subst u)
  | [ h: subZ_rel ?s ?t ?u |- _] => apply subZ_rel_rw in h; 
    try (isVar u; subst u)
  | [h: forall (wit:?r), ?f |- False] => 
    let anteTp := type of r in
    eq_fail anteTp Prop;
    let wit := fresh "ref_wit" in
    do_nonbranching (unshelve refine (let wit := (_ : not r) in _); 
    [try clear h; first [quick_wff_wit| timeout 1 quicksolve | timeout 2 oracle]|]);
    clear h; idtac "Removed hypothesis with False antecedent: " h
  | [h: forall (wit:?r), ?f |- False] => 
    let anteTp := type of r in
    eq_fail anteTp Prop;
    let wit := fresh "ref_wit" in
    do_nonbranching (unshelve refine (let wit := (_ : r) in _); 
    [try clear h; first [quick_wff_wit| timeout 3 quicksolve | timeout 5 oracle]|]);
    let witEq := fresh "witEq" in
    assert (wit = wit) as witEq by reflexivity; unfold wit in witEq; 
    match type of witEq with
    | ?witDef = _ => clear witEq; idtac "Specializing " h " with complicated proof term " (* witDef *); 
      tryif specialize (h witDef) then idtac else (specialize (h wit))
    end
  | [g: ?rel ?s ?t ?u |- _] => isRelAppl rel; match goal with
    | [h: ?rel ?s' ?t' ?v |- _] => neq_fail u v;
      repeat simplify_hyp;
      first [
        assert (rel s' t' u) by (strong_inversion g; now rconstructor); clear g |
        assert (rel s t v) by (strong_inversion h; now rconstructor); clear h ]; 
        match goal with
        | [h1: ?f_rel_ap u |- _] => match goal with
          | [h2:f_rel_ap v |- _] => isVar u; isVar v;
            let temp := fresh "H" in
            assert (u = v) as temp by (unshelve eauto with f_rel_funct_db); 
            revert temp; first [intros -> | intros <-];
            repeat simplify_hyp
          end
        end;
        idtac "Unified variables " u " and " v " using inversion to prove their equality."
    end
    | |- exists v, ?relAp v => isRelAppl relAp; isVar v;
      idtac "Final desperate attempt to solve existential using eexists and oracle to solve subgoals";
      first [
        instExistGoal
      | solve [unshelve (eexists _;
        econstructor; try match goal with
        | [h: ?tp _ |- ?tp _] => apply h
        end; unshelve strong_oracle)]]
  end.

Ltac eager_oracle :=
  first [ 
  quick_wff_wit
  | timeout 3 quicksolve 
  | try cleanup_after_hints; try timeout 4 quicksolve; split_hyps; try progress (cleanup_after_hints; split_hyps); try cleanup; timeout 10 finish ].

Ltac strong_specialize_hyp h :=
  match type of h with
  | forall (wit:?r), ?f => match type of r with
    | Prop => (* check whether we already have an appropriate hypothesis in the context *)
      match goal with
      | [w:r |- _] => specialize (h w)
      | _ => 
        let wit := fresh "ante" in
        do_nonbranching (unshelve refine (let wit := (_ : r) in _); [try clear h; eager_oracle|]);
        let witEq := fresh "witEq" in
        assert (wit = wit) as witEq by reflexivity; unfold wit in witEq; 
        match type of witEq with
        | ?witDef = _ => clear witEq; 

          progress first [
            tryif specialize (h witDef) then idtac else (specialize (h wit)) |
            let temp := fresh "temp_wit" in
            let temp_ih := fresh "temp_ih" in
            assert r as temp by (try clear h; quicksolve); 
            first [specialize (h temp); try clear temp | pose proof (h temp) as temp_ih; clear h; pose proof temp_ih as h; clear temp_ih; try clear temp | clear temp]]; 
          idtac "Specializing " h " with very complicated proof term" (* witDef *)
        end; subst wit
      (* in case creating a transparent witness failed, create an opaque one *)
      | _ => let wit := fresh "ante" in
        assert r as wit by eager_oracle; specialize (h wit); clear wit
      end
    | _ => fail "The Antecedent " r " of hypothesis " h " is not Prop-kinded, so we won't try to specialize it to a proof. "
      end
  (* | [h: forall v:_, ?relAp v -> _ |- _] => isRelApp relAp; 
    let temp := fresh "temp" in
    unshelve assert (relAp _) as temp by quicksolve;
    specialize (h _ temp); clear temp *)
  | _ /\ _ => destruct h as [? h]; strong_specialize_hyp h; intros
  | _ => fail "No hypothesis with fully axiomatized variables to specialize"
  end.

Ltac strong_specialize_hyps :=
  repeat (match goal with
  | [h:_ |- _] => strong_specialize_hyp h
  end).

(* unify the goal with the appropriate IH and apply the IH to finish the goal *)
Ltac f__f_rel_ih := 
  match goal with
    | [h: forall (q: ?qTp), ?relApp ?u |- ?relApp ?u'] => isRelAppl relApp; idtac "unifying goal with hypothesis with single antecedant " h;
      let H := fresh "H" in
      let uTm := fresh "uTm" in
      let vTm := fresh "vTm" in
      enough qTp as H; 
      [specialize (h H);
      match type of h with
      | ?relApp ?u => idtac u;
        first [set u as uTm in * | pose u as uTm];
        first [set u' as vTm in * | pose u' as vTm];
        replace vTm with uTm;
        subst uTm vTm
      end;
      [apply h|] |]
    | [h: ?relApp ?u |- ?relApp ?u'] => isRelAppl relApp; idtac "unifying goal with hypothesis " h;
      let uTm := fresh "uTm" in
      let vTm := fresh "vTm" in
      set u as uTm in *;
      set u' as vTm in *;
      replace uTm with vTm in h;
      subst uTm vTm;
      try apply h
    | [h: ?relApp ?u |- ?relApp' ?u] => isRelAppl relApp;
      (* fetch the terms the rel is applied to in relApp and relApp' *)
      let relAppD := fresh "relAppD" in
      let relAppD' := fresh "relAppD'" in
      destrApp relApp relAppD;
      destrApp relApp' relAppD';
      let relAppRefl := fresh "relAppDRefl" in
      let relAppRefl' := fresh "relAppDRefl'" in
      assRefl relAppD as relAppRefl;
      assRefl relAppD' as relAppRefl';
      match type of relAppRefl with
      | (?rel _::_ ?ts) = _ => clear relAppRefl; match type of relAppRefl' with
        | (rel _::_ ?ts') = _ => clear relAppRefl'; (* idtac "unifying goal with " relApp u " by unifying " ts " with " ts'; *)
          (* go over the terms the rel is applied to in relApp and relApp' and replace all pairs of terms that aren't identical *)
          let tl := fresh "tailApplicantList" in
          let tl' := fresh "tailApplicantList'" in
          let tsRefl := fresh "tsRefl" in
          let tsRefl' := fresh "tsRefl'" in
          
          let test := fresh "testGoal" in
          pose ts as tl; pose ts' as tl';
          repeat (
            assRefl tl as tsRefl; assRefl tl' as tsRefl'; 
            let tsReflT := type of tsRefl in
            let tsReflT' := type of tsRefl' in
            (* idtac "main unification loop with remaining arguments list " tsReflT " and " tsReflT'; *)
            match type of tsRefl with
            | _nil = _ => idtac "finished unifying"; fail
            | ?t _::_ ?tlL = _ => clear tsRefl; match type of tsRefl' with
              | ?t' _::_ ?tlR = _ => clear tsRefl'; 
                pose tlL as tl; pose tlR as tl';
                tryif (assert (t = t') as test by reflexivity; clear test) 
                  then (idtac (*"the terms " t " and " t' "are already identical and need no unification. "*) )
                  else (idtac "try unifying " "..." " with " t' " in " h; replace t with t' in h)
              end; idtac "sucessfully unified terms"
            end
          ); clear tl tl'
        end
      end;
      try apply h
      | _ => idtac "failure to solve goal: "; print_proof_state
    end; try solve [solve_pi_unif_subgoal].

Ltac existence_lemma_pre f :=
  idtac "Starting proof of existence lemma for the reflected function " f ". ";
  repeat cleanup_hints.

Ltac existence_lemma_quicksolve f := 
  intros; try unpack_all;
  try timeout 3 quicksolve; (* try quicksolve; *)

  (* unfold definition in goal *)
  (* cbn; *) first [ timeout 4 cbn | unfold f; (*unfold subsumptionCast in *;*) repeat progress autorewrite with fix_notation_hints];
  repeat axiomatize_ho_term;
  repeat progress (simpl_proj; apply_ifs); try timeout 4 quicksolve.
  

Ltac existence_lemma_induction f indVars conds :=
  existence_lemma_pre f; 
  multivariable_induction indVars conds _nil; 
  existence_lemma_quicksolve f.

Ltac eager_instantiate_goal :=
  match goal with
  | [h: forall (v:_) (v_p:_), ?rel v ?resV |- exists res : ?tp, ?rel ?y res /\ _ ] => 
    specialize (h y); specialize_hyp h; 
    match type of h with
    | ?relApp ?resV => exists resV; split; [apply h|]
    end
  | [h: forall (v:_) (q:_) (v_p:_), ?rel v ?resV |- exists res : ?tp, ?rel ?y res /\ _ ] => 
    specialize (h y); specialize_hyp h; specialize_hyp h; 
    match type of h with
    | ?relApp ?resV => exists resV; split; [apply h|]
    end
  | [h: forall (v:_) (v_p:_) (q:_), ?rel v ?t ?resV |- exists res : ?tp, ?rel ?y ?t res /\ _ ] =>
    specialize (h y); repeat (specialize_hyp h);
    match type of h with
    | ?relApp ?resV => exists resV; split; [apply h|]
    end
  | [h: forall (v:_) (v_p:_), ?rel v ?t ?resV |- exists res : ?tp, ?rel ?y ?t res /\ _ ] =>
    specialize (h y); specialize_hyp h;
    match type of h with
    | ?relApp ?resV => exists resV; split; [apply h|]
    end
  (* | [h: forall (v:_) (q:_) (v_p:_), ?rel v ?resV |- exists res : ?tp, ?rel ?y res /\ _ ] =>
    specialize (h y); repeat_or_fail (specialize_hyp h);
    match type of h with
    | ?relApp ?resV => exists resV; split; [apply h|]
    end *)
  | [h: forall (v:_) (v_p:_), ?rel v ?resV |- exists res : ?tp, ?rel ?y res /\ _ ] =>
    specialize (h y); specialize_hyp h;
    match type of h with
    | ?relApp ?resV => exists resV; split; [apply h|]
    end
  end.

Ltac invert_all_axiomatizations :=
  concat_either (nonbranching_invert_axiomatizations) (repeat_or_fail (
  match goal with
  | [h: ?relApp _ |- _] => isRelAppl relApp; progress 
    first [
      let hTp := type of h in
      progress (do_nonbranching (inversion_clear h; subst); try clear h);
      
      let test := fresh "test" in
      assert (hTp) as test by (constructor; assumption);
      clear test; idtac "Sucessfully inversion_cleared " h
      | do_nonbranching (inversion h; subst); idtac "Sucessfully inverted " h ]
  end
  )).


Ltac specialize_p h :=
  first [
    specialize_wit h (ltac:(split_hyps; try unify_vars; try invert_all_axiomatizations; oracle))
    | match type of h with
    | forall (_:?hTp), _ => 
      let hKnd := type of hTp in
      eq_fail hKnd Prop;
      let wit := fresh "wit" in
      assert (hTp) as wit by (split_hyps; try unify_vars; try invert_all_axiomatizations; oracle);
      first [
        let H := fresh "temp" in
        assert (forall (p':hTp), h p' = h wit) as H by (intros; f_equal; now auto with pi_db);
        try (rewrite H in *(*; idtac "Rewrote other applications of " h " to " h " wit using proof irrelevance. "*));
        specialize (h wit); 
        clear H |
        pose proof (h wit)]
    end].

Ltac fill_ih_holes := 
  match goal with
  | [ih: forall (x1:_) (x1_p:_) (x2:_) (x2_p:_), ?rel x1 x2 ?u |- ?rel ?x1V ?x2V ?v] => idtac "The hypothesis that matches the goal " ih;
    specialize (ih x1V (ltac:(clear ih; oracle)));
    specialize (ih x2V (ltac:(clear ih; oracle)))
  | [ih: forall (x1:_) (x1_p:_), ?rel x1 ?u |- ?rel ?x1V ?v] => idtac "The hypothesis that matches the goal " ih;
    specialize (ih x1V);
    specialize_p ih
  | [ih: forall (x1:_) (x1_p:_), ?rel x1 ?t ?u |- ?rel ?x1V ?t ?v] => idtac "The hypothesis that matches the goal " ih;
    specialize (ih x1V (ltac:(clear ih; oracle)))
  | [ih: forall (x2:_) (x2_p:_), ?rel ?u x2 _ |- ?rel ?v ?x2V _] => idtac "The hypothesis that matches the goal " ih;
    specialize (ih x2V (ltac:(clear ih; oracle)))
  | [ih: forall (x2:_) (x2_p:_), ?rel ?u x2 |- ?rel ?v ?x2V] => idtac "The hypothesis that matches the goal " ih;
    specialize (ih x2V (ltac:(clear ih; oracle)))
  | [ih: forall (x:_) (p:_) (q:_), ?rel x ?u _ |- ?rel ?xV ?u _] => 
    specialize (ih xV);
    specialize_wit ih (ltac:(clear ih; oracle));
    specialize_wit ih (ltac:(clear ih; oracle))
  | [ih: forall (x:_) (p:_) (q:_), ?rel x ?u _ |- ?rel ?xV ?u _] => specialize (ih xV);  idtac "The hypothesis that matches the goal " ih;
    match type of ih with
    | forall (p:?pTp) (q:_), _ => 
      let pKnd := type of pTp in
      eq_fail pKnd Prop;
      repeat_or_fail (specialize_hyp ih)
    end
  | [ih: forall (x:_) (p:_) (q:_), ?rel x _ |- ?rel ?xV _] => specialize (ih xV); idtac "The hypothesis that matches the goal " ih;
    match type of ih with
    | forall (p:?pTp) (q:_), _ => 
      let pKnd := type of pTp in
      repeat_or_fail (specialize_hyp ih)
    end
  | [ih: ?rel _ |- ?rel _] => idtac "The hypothesis that matches the goal " ih
  | [f__f_rel1 : forall (x : {_ : _ | _}) (v : _), proj (?f_def1 x) = v <-> ?f_rel1 (proj x) v |- 
    ?f_rel1 ?u ⌊ ?f_def1 (exist ?p_u ?u ?u_p) -⌋] => idtac "The hypothesis that matches the goal " f__f_rel1;
    specialize (f__f_rel1 (exist p_u u u_p)); repeat progress autorewrite with fix_notation_hints in f__f_rel1;
    try rewrite <- f__f_rel1; try reflexivity
  end.

Ltac f_rel_finish :=
  repeat autounfold with get_rel_db in *;
  tryif fill_ih_holes then idtac else (idtac "Failure to find hypothesis that exactly matches goal."; match goal with
  | [ih: ?rel ?x _ _ |- ?rel ?x _ _] => idtac "The hypothesis that roughly matches the goal " ih
  | [ih: ?rel _ ?y _ |- ?rel _ ?y _] => idtac "The hypothesis that roughly matches the goal " ih
  | _ => print_proof_state; fail
  end
  );
  (* unify the goal with an appropriate IH, apply the IH, then solve the proof obligations generated during unification using PI *)
  try f__f_rel_ih; try finish; try cleanup; try finish.

Ltac pack_goal_rewriting := 
  match goal with
  | [f_frel: forall (args: ArgList ?argTps) (v:?resTp), ⌊ ?f args -⌋ = v <->
    ?frel (prArgList args _ _) v |- ?frel _ ⌊ ?f ?args' -⌋ ] => 
    rewrite <- (f_frel args' ⌊ f args' -⌋); try reflexivity
  end.

Ltac goal_rewriting :=
  try unfold rel_u;
  repeat destruct_disjs; repeat progress autorewrite with int_rel_back;
  try pack_goal_rewriting.

Ltac f__f_rel_ex_body :=
  autounfold with lia_unfold in *;
  simpl_proj;
  (* fill in required witnesses in IHs *)
  try (timeout 120 specialize_hyps); (* this may create a witness that doesn't match the one in the goal *)
  strong_specialize_hyps;
  (* rewrite the projection of the unfolded definition in the goal into a new variable axiomatized using a relation of a previously declared reflected function *)
  repeat (timeout 120 axiomatize_next_term);
  (* apply constructor of relation in goal, if now possible *)
  let resVal := fresh "res" in
  repeat destruct_disjs; repeat progress autorewrite with int_rel_back;
  match goal with
  | |- ?relApp ?res => 
    try set res as resVal in *
  end; 
  autorewrite with f_rel_back; (* this may create existential variables in the goal *)
  repeat shape_based; 
  try unfold rel_u;
  repeat destruct_disjs; repeat progress autorewrite with int_rel_back;
  try pack_goal_rewriting; 
  try subst resVal;
  try timeout 20 quicksolve;

  (* cleanup context, to aid finding witnesses later on *)
  (* repeat lia_preprocessor_step; try (quick_simpl; fast_done); *)
  try split_hyps; try invert_all_axiomatizations;
  (* repeat concat_either (instantiate_hyp) (specialize_hyps); *)

  (* solve/delay these variables *)
  repeat first [instantiate_goal | eager_instantiate_goal];

  (* try repeating those backwards reasoning steps *)
  repeat (
    goal_rewriting;
    progress autorewrite with f_rel_back; repeat shape_based;
    try split_hyps; try invert_all_axiomatizations;
    repeat first [instantiate_goal | eager_instantiate_goal];
    autounfold with get_rel_db in *
  );

  (* try to take figure out how to deal with disjuncts in the goal resulting from a backwards reasoning lemma *)
  repeat lia_preprocessor_step;
  try first [split; [quicksolve|]|split; [|quicksolve]];
  repeat (unshelve eexists _; try quicksolve; try first [split; [quicksolve|]|split; [|quicksolve]]);
  simpl_proj;
  try rconstructor;
  
  simpl_proj; autounfold with lia_unfold in *; simpl_proj; (* cleanup integer arithmetic stuff *)
  repeat autounfold with get_rel_db in *;
  try pack_goal_rewriting.

(* tactic to prove the existence lemma *)
Ltac f__f_rel_ex' indVars conds recCalls :=
  existence_lemma_induction indVars conds;
  (* specialize the IHs to the values from the recursive calls *)
  try specializes recCalls;

  f__f_rel_ex_body.

Ltac f__f_rel_ex indVars recCalls := f__f_rel_ex' indVars _nil recCalls.

(* tactic to prove the rewrite lemma using the existence lemma *)
Ltac f__f_rel_rw :=
  split;
  [ 
    intros <-; auto with rel_ax_db
    | match goal with
    | |- ?rel ?v -> ?tm = ?v => assert (rel tm) by (auto with rel_ax_db f_rel_funct_db)
    end; intros; 
    match goal with
    | |- ?tm = _ => set tm in *
    | _ => idtac
    end; now unify_vars
  ].

(* tactic to prove the theorem ralation f with its relation using the rewrite and functionhood lemmata *)
Ltac f__f_rel :=
  intros; repeat cleanup_hints; simpl_proj;
  split; (*quick_simpl;*) intros;
  [ match goal with
    | [h: _ = ?v |- ?rel ?v] => rewrite <- h; unshelve eauto with rel_ax_db f_rel_funct_db
    end
    | unshelve eauto with rel_ax_db f_rel_funct_db
  ].

Ltac eq_refl :=
  let x := fresh "x" in
  intros x;
  induction x; quick_simpl; try quicksolve; simpl; 
  quick_simpl; repeat split; 
  let unfoldIsTrueNotation := fresh "unfoldIsTrueNotation" in
  assert (forall v, is_true v -> v = true) as unfoldIsTrueNotation by quicksolve;
  try apply unfoldIsTrueNotation;
  try quicksolve. 

Ltac eq_refl_rec := 
  repeat match goal with
  | |- is_true (?eq ?v ?v) => generalize dependent v
  | [h: _ |- _] => clear
  | [ |- forall v, is_true (?eq v v)] => eq_refl
  end.

Ltac eqb_eq_lem :=
  intros s t H; multivariable_induction (s _::_ t _::_ _nil) _nil _nil; try quicksolve;
  simpl in *; quick_simpl; split_hyps; quick_simpl; try quicksolve;
  let unfoldIsTrueNotation := fresh "unfoldIsTrueNotation" in
  assert (forall v, is_true v <-> v = true) as unfoldIsTrueNotation by quicksolve;
  try apply unfoldIsTrueNotation; try rewrite <- unfoldIsTrueNotation in *;
  try quicksolve; shelve.
