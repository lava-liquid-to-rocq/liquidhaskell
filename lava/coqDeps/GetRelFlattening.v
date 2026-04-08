Require Import Logic.FunctionalExtensionality.
Load TacticUtils.

(* This file contains the function packs and other higher-order stuff *)

(** Typeclass for functions *)

Inductive UArgListT : Type :=
  | noUArgsT: UArgListT
  | consUArgsT (X:Type) (tl:UArgListT): UArgListT.
Inductive ArgListT : Type := 
  | noArgsT : ArgListT
  | consArgsT (X X':Type): (X' ⤖ X) -> (forall (x:X'), ArgListT) -> ArgListT.


Inductive ArgList: ArgListT -> Type :=
  | noArgs: ArgList noArgsT
  | consArgs {X X':Type} {prX: X' ⤖ X} (x:X') {tlT: forall (x:X'), ArgListT} (tl: ArgList (tlT x)): 
      ArgList (consArgsT X X' prX tlT).
Inductive UArgList: UArgListT -> Type :=
  | noUArgs: UArgList noUArgsT
  | consUArgs {X:Type} (x:X) {tlT: UArgListT} (tl:UArgList tlT):
      UArgList (consUArgsT X tlT).

Ltac synthesizePrInstance := quicksolve.
Global Notation "X ::UT tl" := (consUArgsT X tl) (at level 60, right associativity).
Global Notation "X' ::RT tl" := (consArgsT _ X' _ tl) (at level 60, right associativity).
Global Notation "x ::R tl" := (@consArgs _ _ _ x _ tl) (at level 60, right associativity).
Global Notation "x ::U tl" := (@consUArgs _ x _ tl) (at level 60, right associativity).
Global Notation nilUT := noUArgsT.
Global Notation nilU := noUArgs.
Global Notation nilRT := noArgsT.
Global Notation nilR := noArgs.

(* Since destruct and inversion cannot handle ArgLists correctly *)

Lemma existT_inj {A:Type} {P:A->Type} (x:A) (p q:P x):
  existT P x p = existT P x q -> p = q.
Proof.
  intro H.
  pose (@eq_sigT_snd A P x x p q H) as K. 
  rewrite <- eq_rect_eq in K; apply K.
Qed. 
Lemma existT_eq {A:Type} {P:A->Type} (x y:A) (p:P x) (q:P y):
  forall (eq:x = y), p = (eq_rect _ (fun x=>P x) q _ (eq_sym eq)) -> existT P x p = existT P y q.
Proof.
  intros -> ->.
  rewrite <- eq_rect_eq.
  reflexivity.
Qed. 
Lemma consArgsT_inj1 {X X' X0 X'0:Type} {g:X'0 ⤖ X0} {g':X' ⤖ X} 
  {argTps': X'0 -> ArgListT} {tlT:X' -> ArgListT}: 
  X' ::RT tlT = X'0 ::RT argTps' -> X = X0.
Proof. 
  exact (fun eq =>
  @f_equal ArgListT Type (fun l => match l with
      | noArgsT => X
      | consArgsT Y _ _ _ => Y
      end) _ _ eq).
Qed.
Lemma consArgsT_inj2 {X X' X0 X'0:Type} {g:X'0 ⤖ X0} {g':X' ⤖ X} 
  {argTps':X'0 -> ArgListT} {tlT: X' -> ArgListT}: 
  X' ::RT tlT = X'0 ::RT argTps' -> X' = X'0.
Proof. 
  exact (fun eq =>
  @f_equal ArgListT Type (fun l => match l with
      | noArgsT => X'
      | Y ::RT _ => Y
      end) _ _ eq).
Qed.
Lemma consArgsT_inj3 {X X':Type} {g g':X' ⤖ X} {argTps' tlT}: 
  consArgsT X X' g' tlT = consArgsT X X' g argTps' -> g = g'.
Proof. 
  inversion 1 as [[H1 H2]].
  apply existT_inj in H1.
  apply existT_inj in H1.
  exact (eq_sym H1).
Qed.
Lemma consArgsT_inj4 {X X0 X':Type} {g:X' ⤖ X0} {g':X' ⤖ X} {argTps1 argTps2}: 
  consArgsT X X' g' argTps2 = consArgsT X0 X' g argTps1 -> argTps1 = argTps2.
Proof. 
  inversion 1 as [[K L M]]. 
  revert K; intros <-.
  apply existT_inj in M.
  apply (eq_sym M).
Qed.
Lemma consArgsT_inj {X X' X0 X'0:Type} {g:X'0 ⤖ X0} {g':X' ⤖ X} {argTps' tlT}: 
  consArgsT X X' g' tlT = consArgsT X0 X'0 g argTps' -> 
    {eqX : X = X0 &
    {eqX' : X' = X'0 & 
    {eqG: g=(eq_rect X (fun Y => X'0 ⤖ Y) (eq_rect X' (fun Y => Y ⤖ X) g' X'0 eqX') X0 eqX) & 
    argTps' = eq_rect X' (fun Y => Y -> ArgListT) tlT X'0 eqX'} } }.
Proof. 
  refine (fun eq => existT _ (@f_equal ArgListT Type (fun l => match l with
      | noArgsT => X
      | consArgsT Y _ _ _ => Y
      end) _ _ eq) _).
  unshelve refine (existT _ (@f_equal ArgListT Type (fun l => match l with
      | noArgsT => X'
      | consArgsT _ Y _ _ => Y
      end) _ _ eq) _).
  pose proof (@f_equal ArgListT Type (fun l => match l with
      | noArgsT => X
      | consArgsT Y _ _ _ => Y
      end) _ _ eq) as eqX. simpl in eqX.
  revert eqX. intros <-.
  pose proof (@f_equal ArgListT Type (fun l => match l with
      | noArgsT => X'
      | consArgsT _ Y _ _ => Y
      end) _ _ eq) as eqX'; simpl in eqX'.
  revert eqX'. intros <-.
  repeat rewrite <- eq_rect_eq.
  inversion eq.
  apply existT_inj in H0.
  apply existT_inj in H0.
  apply existT_inj in H1.
  refine (existT _ (eq_sym H0) (eq_sym H1)).
Qed.
  
Lemma noArgsLemma: forall (args: ArgList noArgsT), args = noArgs.
Proof. 
  intro args. 
  unshelve refine (
  match args as a1 in (ArgList a) return (forall 
    (teq:a = noArgsT),
    args = eq_rect a ArgList a1 noArgsT teq -> _) with
  | noArgs => fun teq eq => @eq_ind_r (ArgList noArgsT) _ _ eq _ 
    (eq_rect_eq _ _ _ _ teq)
  | @consArgs X X' prX x tlT tl => fun teq eq => _
  end eq_refl eq_refl
  ). inversion teq.
Qed.
Definition uncons {X X':Type} {g} {argTps': forall (x:X'), ArgListT} (args: ArgList (consArgsT X X' g argTps')):
  sigT (fun x=>ArgList (argTps' x)).
Proof.
  refine (match args as a1 in (ArgList a0) return (forall 
    (teq : a0 = consArgsT X X' g argTps') (eq: args = eq_rect _ _ a1 _ teq), 
    sigT (fun x=>ArgList (argTps' x))) with
  | noArgs => fun teq => False_rect _ (@eq_ind ArgListT noArgsT
                   (fun e : ArgListT =>
                    match e with
                    | noArgsT => True
                    | consArgsT _ _ _ _ => False
                    end) I (X' ::RT argTps') teq)
  | @consArgs X X' g' x tlT tl => fun teq eq => _
  end eq_refl (eq_rect_eq _ _ _ _ _)
  ). 
  (*refine (existT _ (eq_rect _ _ x _ (consArgsT_inj2 teq)) _).
  pose proof (consArgsT_inj2 teq) as eqX'. revert eqX'.
  intros <-. rewrite <- eq_rect_eq.
  refine (eq_rect tlT (fun a => ArgList (a x)) tl argTps' (eq_sym (consArgsT_inj4 teq))).*)
  pose (consArgsT_inj teq) as s.
  destruct s as [eqX [eqX' [eqG eqArgs]]].
  refine (existT _ (eq_rect _ _ x _ eqX') _).
  rewrite eqArgs. 
  (*clear eqG eqArgs.
  revert eqX'. intros <-.
  repeat rewrite <- eq_rect_eq.
  exact tl.*)
  enough (tlT x = eq_rect X' (fun Y : Type => Y -> ArgListT) tlT X'0 eqX' 
   (@eq_rect Type X' (fun x0 : Type => x0) x X'0 eqX')) as H.
 - rewrite <- H. exact tl.
 - clear g argTps' args g' tl teq eq eqX eqG eqArgs.
   revert eqX'. intros <-. repeat rewrite <- eq_rect_eq. reflexivity.
Defined.

Ltac cleanup_eq_rect T x P tm z :=
  let H := fresh "H" in
  let bla := fresh "bla" in
  pose (@eq_rect_eq T x P tm z) as H; 
  set (@eq_rect T x P tm x z) as bla in *;
  revert H; intros <-.

Ltac cleanup_leading_eq_rects h :=
  let temp := fresh "temp" in
  pose proof (eq_refl h) as temp; 
  unfold eq_rect_r in *;
  try unfold h in temp;
  match type of temp with
  | @eq_rect ?T ?x ?P ?tm ?x ?z = _ => clear temp;
    cleanup_eq_rect T x P tm z
  | @eq_rect ?T ?x ?P ?tm ?x ?z _ = _ => clear temp; 
    cleanup_eq_rect T x P tm z
  | @eq_rect ?T ?x ?P ?tm ?x ?z _ _ = _ => clear temp; 
    cleanup_eq_rect T x P tm z
  | @eq_rect ?T ?x ?P ?tm ?x ?z _ _ _ = _ => clear temp; 
    cleanup_eq_rect T x P tm z
  | @eq_rect ?T ?x ?P ?tm ?x ?z _ _ _ _= _ => clear temp; 
    cleanup_eq_rect T x P tm z
  | @eq_rect ?T ?x ?P ?tm ?x ?z _ _ _ _ _= _ => clear temp; 
    cleanup_eq_rect T x P tm z
  | @eq_rect ?T ?x ?P ?tm ?x ?z _ _ _ _ _ _= _ => clear temp; 
    cleanup_eq_rect T x P tm z
  | @eq_rect ?T ?x ?P ?tm ?x ?z _ _ _ _ _ _ _= _ => clear temp; 
    cleanup_eq_rect T x P tm z
  | @eq_rect ?T ?x ?P ?tm ?x ?z _ _ _ _ _ _ _ _= _ => clear temp; 
    cleanup_eq_rect T x P tm z
  | @eq_rect ?T ?x ?P ?tm ?x ?z _ _ _ _ _ _ _ _ _= _ => clear temp; 
    cleanup_eq_rect T x P tm z
  end.

Lemma uncons_correct_aux: forall {X X': Type} {g:X' ⤖ X} {argTps'} (x:X') (args': ArgList (argTps' x)), 
  uncons (@consArgs X X' g x argTps' args') = existT _ x args'.
Proof.
  intros. 
  simpl. unfold eq_rect_r. unfold internal_eq_rew_dep. 
  set (consArgsT_inj eq_refl) as e.
  destruct e. destruct s. destruct s. 
  repeat rewrite <- eq_rect_eq in x2.
  clear x0. clear x2. 
  match goal with
  | |- _ ?x_ ?args'_ = _ x args' =>
    set x_ as x0 in *
  end.
  match goal with
  | |- _ x0 ?args'_ = _ =>
    set args'_ as tl0 in *
  end.
  enough (x = x0) as H.
  - simpl in tl0. symmetry.
    refine (@existT_eq _ (fun x2 : X' => ArgList (argTps' x2)) x x0 args' tl0 H _).
    subst tl0. subst x0.
    match goal with
    | |- _ = ?RHS_ =>
      match RHS_ with
      | eq_rect ?X ?P ?tm_ ?Y ?Z =>
        match tm_ with
        | eq_rect ?X2 ?P2 ?tm2_ ?Y2 ?Z2 =>
          set RHS_ as RHS in *;
          set tm_ as term in *;
          set tm2_ as term2 in *
        end
      end
    end. 
    set (match
      x1 as e in (_ = a)
      return
        (argTps' x =
         eq_rect X' (fun Y : Type => Y -> ArgListT) argTps' a e
           (eq_rect X' (fun x0 : Type => x0) x a e))
    with
    | eq_refl =>
        eq_ind argTps' (fun a : X' -> ArgListT => argTps' x = a x)
          (eq_ind x (fun x0 : X' => argTps' x = argTps' x0) eq_refl x
             (eq_rect_eq Type X' (fun x0 : Type => x0) x eq_refl)) argTps'
          (eq_rect_eq Type X' (fun Y : Type => Y -> ArgListT) argTps'
             eq_refl)
    end) as prf2_ in *.
    pose proof (exist _ prf2_ eq_refl) as [prf2 ->].
    set (eq_rect X' (fun Y : Type => Y -> ArgListT) argTps' X' x1
       (eq_rect X' (fun x0 : Type => x0) x X' x1)) as bla2 in *.
    cleanup_leading_eq_rects bla2. 
    set (eq_rect X' (fun x0 : Type => x0) x X' x1) as x0 in *. subst bla2.
    subst term2; subst term; subst RHS.

    pose (fun (x1:{v:X'|x=v}) => args' = eq_rect (` x1) (fun x2 : X' => ArgList (argTps' x2))
  (eq_rect argTps' (fun y : X' -> ArgListT => ArgList (y (` x1)))
     (eq_rect (argTps' x) (fun a : ArgListT => ArgList a) args'
        (argTps' (` x1)) (@f_equal _ _ argTps' _ _ ⌈ x1 ⌉)) argTps' (eq_sym e)) x 
  (eq_sym ⌈ x1 ⌉)) as P.
    assert (P (exist (fun v : X' => x = v) x eq_refl)) as Px.
    { unfold P. simpl. rewrite <- eq_rect_eq. reflexivity. }
    assert (exist (fun v : X' => x = v) x eq_refl = exist (fun v : X' => x = v) x0 H) as K.
    { rewrite H. reflexivity. }
    pose proof (@eq_ind _ (exist _ x eq_refl) P Px (exist _ x0 H) K).
    unfold P in H0. 
    simpl in H0.
    
    set (f_equal argTps' H) as prf2_ in H0.
    assert (prf2_ = prf2) as rw by (apply proof_irrelevance).
    rewrite rw in H0.
    apply H0.
  - clear tl0 e. subst x0.
    apply (@eq_rect_eq _ X' (fun x0 : Type => x0) x x1).
Qed.
Definition uncons_correct_rw {X X': Type} {g:X' ⤖ X} (x:X')  {argTps':X'->ArgListT} (args': ArgList (argTps' x)): 
  uncons (x ::R args') = existT _ x args' := @uncons_correct_aux X X' g argTps' x args'.
Lemma uncons_correct: forall {X} {X'} {g} {argTps'} (args: ArgList (consArgsT X X' g argTps')), 
  args = consArgs (projT1 (uncons args)) (projT2 (uncons args)).
Proof.
  intros X X' g argTps' args.
  refine (match args as a1 in (ArgList a0) return (forall 
    (teq : a0 = consArgsT X X' g argTps') (eq: args = eq_rect _ _ a1 _ teq), 
    _) with
  | noArgs => fun teq => False_rect _ (@eq_ind ArgListT noArgsT
                   (fun e : ArgListT =>
                    match e with
                    | noArgsT => True
                    | consArgsT _ _ _ _ => False
                    end) I (consArgsT X X' g argTps') teq)
  | @consArgs X X' g' x tlT tl => fun teq => _
  end eq_refl (eq_rect_eq _ _ _ _ _)
  ). 
  intros ->.
  
  pose proof (consArgsT_inj teq) as [<- [<- [-> ->]]]. simpl.
  repeat rewrite <- eq_rect_eq.
  repeat rewrite uncons_correct_aux. 
  reflexivity.
Qed. 
Opaque uncons.

Definition convArgList (args args':ArgListT) (teq: args=args'):
  ArgList args -> ArgList args' := fun l => eq_rect args ArgList l args' teq.

Definition unucons {X:Type} {uargTps': UArgListT} (uargs: UArgList (consUArgsT X uargTps')):
  X * (UArgList uargTps').
Proof.
  refine (match uargs as a1 in (UArgList a0) return (forall 
    (teq : a0 = consUArgsT X uargTps') (eq: uargs = eq_rect _ _ a1 _ teq), 
    X * (UArgList uargTps')) with
  | noUArgs => fun teq => False_rect _ (@eq_ind UArgListT noUArgsT
                   (fun e : UArgListT =>
                    match e with
                    | noUArgsT => True
                    | consUArgsT _ _ => False
                    end) I (consUArgsT X uargTps') teq)
  | @consUArgs X x tlT tl => fun teq eq => _
  end eq_refl (eq_rect_eq _ _ _ _ _)
  ). 
  refine (pair _ _).
    + refine (eq_rect X _ x X0 (@f_equal UArgListT Type (fun l => match l with
      | noUArgsT => X
      | consUArgsT Y _ => Y
      end) _ _ teq)).
    + refine (eq_rect _ _ tl _ (@f_equal UArgListT UArgListT (fun l => match l with
      | noUArgsT => uargTps'
      | consUArgsT _ Y => Y
      end) _ _ teq)).
Defined. 
Lemma unucons_correct_aux {X:Type} {uargTps': UArgListT} (x:X)
  (uargs':UArgList uargTps'):
  unucons (@consUArgs X x uargTps' uargs') = (x, uargs'). 
Proof.
  reflexivity.
Qed.
Lemma unucons_correct {X:Type} {uargTps': UArgListT} (uargs: UArgList (consUArgsT X uargTps')):
  uargs = @consUArgs X (fst (unucons uargs)) uargTps' (snd (unucons uargs)).
Proof.
  refine (match uargs as a1 in (UArgList a0) return (forall 
    (teq : a0 = consUArgsT X uargTps') (eq: uargs = eq_rect _ _ a1 _ teq), 
    _) with
  | noUArgs => fun teq => False_rect _ (@eq_ind UArgListT noUArgsT
                   (fun e : UArgListT =>
                    match e with
                    | noUArgsT => True
                    | consUArgsT _ _ => False
                    end) I (consUArgsT X uargTps') teq)
  | @consUArgs X x tlT tl => fun teq => _
  end eq_refl (eq_rect_eq _ _ _ _ _)
  ). 
  intros ->.
  pose proof (@f_equal UArgListT Type (fun l => match l with
      | noUArgsT => X
      | consUArgsT Y _ => Y
      end) _ _ teq) as H; simpl in H. revert H; intros <-.
  pose proof (@f_equal UArgListT UArgListT (fun l => match l with
      | noUArgsT => uargTps'
      | consUArgsT _ Y => Y
      end) _ _ teq) as H; simpl in H; revert H; intros ->.
  rewrite <- eq_rect_eq.
  rewrite unucons_correct_aux.
  reflexivity.
Qed.

Fixpoint projectsArgListT (args:ArgListT) (uargs:UArgListT): Prop.
Proof.
  destruct args.
  - destruct uargs.
    + exact True.
    + exact False.
  - destruct uargs.
    + exact False.
    + exact (X = X0 /\ forall (x:X'), projectsArgListT (a x) uargs).
Defined. 

Fixpoint prArgListT {argTps: ArgListT} (args:ArgList argTps): UArgListT.
Proof.
  destruct args.
  - exact noUArgsT.
  - exact (consUArgsT X (prArgListT (tlT x) args)).
Defined.

Fixpoint prArgList {argTps: ArgListT} (args:ArgList argTps) (uargTps:UArgListT): 
  projectsArgListT argTps uargTps -> UArgList uargTps.
Proof.
intros p.
destruct args.
- destruct uargTps.
  + exact noUArgs.
  + exfalso. apply p.
- destruct uargTps.
  + exfalso. apply p.
  + destruct p as [<- p].
    refine ((prX.(proj) x) ::U (prArgList (tlT x) args uargTps (p x))).
Defined.
Definition projectsArgListCons {X X' prX} {argTps': forall (x':X'), ArgListT} 
  (x':X') (uargTps':UArgListT)
  (z:projectsArgListT (@consArgsT X X' prX argTps') (consUArgsT X uargTps')):
  projectsArgListT (argTps' x') uargTps' := (pr2 z) x'.

Lemma prArgListCons {X X' prX} {argTps': forall (x':X'), ArgListT} 
  (x':X') (args':ArgList (argTps' x')) (uargTps':UArgListT) (z:_): 
  prArgList (@consArgs X X' prX x' argTps' args') (consUArgsT X uargTps') z = 
  consUArgs (prX.(proj) x') (prArgList args' uargTps' (projectsArgListCons x' uargTps' z)).
Proof.
  unfold projectsArgListCons.
  destruct z as [? z]. simpl in *.
  rewrite <- eq_rect_eq.
  reflexivity.
Qed.
Fixpoint gprArgList_po {argTps: ArgListT}
  {uargTps:UArgListT} {p:projectsArgListT argTps uargTps} (x:ArgList argTps):
  forall (y:ArgList argTps), 
  prArgList x uargTps p = prArgList y uargTps p -> x = y.
Proof.
  destruct x.
  - intros y H. unfold prArgList in H.
    unshelve refine (match y with
    | noArgs => eq_refl
    | @consArgs X X' prX x tlT tl => _
    end). 
    unfold IDProp; refine (fun A a => a).
  - intros y H.
    unshelve refine (
    match y as a1 in (ArgList a) return (forall 
      (args0: ArgList (consArgsT X X' prX tlT)) 
      (teq:a = consArgsT X X' prX tlT),
      args0 = eq_rect a ArgList a1 (consArgsT X X' prX tlT) teq ->
      args0 = y -> @consArgs X X' prX x tlT x0 = args0) with
    | noArgs => ltac:(intros ? K -> ->; inversion K)
    | @consArgs X X' prX x_ tlT tl =>_
    end y eq_refl eq_refl eq_refl
    ).
    + intros ? teq temp ->. revert temp. intros ->. 
    inversion teq. 
    (* as usual we need to use revert H; intros <-,
       instead of rewrite <- H in  *, which fails *)
    revert H1; intros <-.
    revert H2; intros <-.
    apply existT_inj in H4. revert H4; intros <-.
    apply existT_inj in H3. 
    apply existT_inj in H3. revert H3; intros <-. rewrite <- eq_rect_eq in *. clear teq.
    destruct uargTps; [exfalso; apply p|].
    destruct p as [p0 p].
    simpl in *.
    pose proof p0 as p0_.
    revert p0_. intros <-.
    replace p0 with (eq_refl X) in * by (apply proof_irrelevance). clear p0.
    repeat rewrite <- eq_rect_eq in H.
    inversion H as [[H1 H2]]. clear H.
    apply existT_inj in H1. apply (prX.(po)) in H1. revert H1; intros ->.
    apply existT_inj in H2.
    enough (K:x0 = tl) by (rewrite K; reflexivity).
    refine (gprArgList_po (tlT x_) uargTps (p x_) x0 tl H2).
Qed.
#[global] Instance gprArgList {argTps: ArgListT} {uargTps:UArgListT} {p:projectsArgListT argTps uargTps}: 
  (ArgList argTps) ⤖ (UArgList uargTps) := 
  {| proj:=fun args => prArgList args uargTps p; po:=gprArgList_po |}.

Class Pack (argTps:ArgListT) {uargTps:UArgListT} {z:projectsArgListT argTps uargTps}
  (T: Type) (p: forall (args: ArgList argTps), T -> Prop) := {
  f (args:ArgList argTps): {v:T | p args v};
  frel (uargs: UArgList uargTps) (v:T): Prop;
  f_frel (args:ArgList argTps) (v:T): proj1_sig (f args) = v <-> frel (prArgList args uargTps z) v;
  funct (uargs: UArgList uargTps) v v': frel uargs v -> frel uargs v' -> v = v'
}.

Class uPack (uargTps: UArgListT) (T: Type) := {
	rel_u (uargs: UArgList uargTps): T -> Prop; (* The graph relation *)
	funct_u (uargs:UArgList uargTps) (v v':T): rel_u uargs v -> rel_u uargs v' -> v = v'
}.

Definition uPack_wf (argTps:ArgListT) {uargTps:UArgListT} (z:projectsArgListT argTps uargTps)
  {T: Type} (p: forall (args: ArgList argTps), T -> Prop)
  (upack:uPack uargTps T): Prop :=
  exists (f: forall (args:ArgList argTps), {v:T | p args v}),
    forall (args:ArgList argTps) (v:T), proj1_sig (f args) = v <-> upack.(rel_u) (prArgList args uargTps z) v.

Ltac uPack_wf :=
  match goal with
  | [f_frel : (forall (args : ArgList ?argTps) (v : ?tp), ⌊ ?f args _⌋ = v <->
      ?frel (prArgList args ?uargTps _) v) |- uPack_wf ?argTps ?z ?p ?upack] => 
    exists f;
    exact f_frel
  end.

Lemma instantiate_frel_res: forall {argTps} {uargTps:UArgListT} {z:projectsArgListT argTps uargTps}
  {T: Type} {p: forall (args: ArgList argTps), T -> Prop}
  {g: forall (args:ArgList argTps), {v:T | p args v} }
  {frel: UArgList uargTps -> T -> Prop}
  (p:forall (w:T), Prop) {uargs: UArgList uargTps}
  (f_frel : forall (args : ArgList argTps) (v : T), ⌊ g args _⌋ = v <->
    frel (prArgList args uargTps z) v)
  (args_r: {args:ArgList argTps | prArgList args uargTps z = uargs})
  (prf: forall (w:T), frel uargs w -> p w),
  exists (w:T), frel uargs w /\ p w.
Proof.
  intros.
  destruct args_r as [args argsRw].
  pose ⌊ g args _⌋ as w.
  exists w.
  split;
  [|refine (prf w _)];
  rewrite <- argsRw;
  now rewrite <- f_frel0.
Qed.

Ltac synthesize_args :=
  repeat (match goal with
  | |- {args: ArgList {v:?tp | ?q} ::RT ?tlt | prArgList args (_ ::UT ?tlut) (conj _ (fun _ => ?ztl)) = ?x_u ::U ?utl} => 
    let hd := fresh "arg_" in
    let rc := fresh "rc" in
    refine (let hd : {v:tp | q} := (ltac:(refine (exist _ x_u _); timeout 5 quicksolve)) in _);
    enough {args: ArgList (tlt hd) | prArgList args tlut ztl = utl} as rc by (
      refine (exist _ (hd ::R ⌊ rc -⌋) _); cbn; now rewrite ⌈ rc ⌉)
  | |- {args: ArgList nilRT | prArgList args nilUT I = nilU} =>
    refine (exist _ nilR eq_refl)
  end).


Definition packPr_proj {argTps: ArgListT} {uargTps:UArgListT} {z:projectsArgListT argTps uargTps} 
  {T:Type} {p: forall (xs:ArgList argTps), T -> Prop}: 
  (@Pack argTps uargTps z T p) -> (@uPack uargTps T) := fun pack => {| rel_u:=pack.(frel); funct_u:=pack.(funct) |}.

Lemma packPr_proj_rw (argTps: ArgListT) {uargTps:UArgListT} {z:projectsArgListT argTps uargTps} 
  {T:Type} {p: forall (xs:ArgList argTps), T -> Prop} {g rel cor rel_funct}:
  @packPr_proj argTps uargTps z T p {| f:=g; frel:=rel; f_frel:=cor; funct:=rel_funct |} = {| rel_u:=rel; funct_u:=rel_funct |}.
Proof.
  reflexivity.
Qed.
#[global] Hint Rewrite packPr_proj_rw:get_rel_db. 

Local Lemma packPr_po {argTps: ArgListT} {uargTps:UArgListT} {z:projectsArgListT argTps uargTps} 
  {T:Type} {p: forall (xs:ArgList argTps), T -> Prop}:
  forall (x y:@Pack argTps uargTps z T p), packPr_proj x = packPr_proj y -> x = y.
Proof.
    intros [f rel f_rel funct] [f' rel' f_rel' funct'] H.
    inversion H as [H1]; revert H1; clear H; intros ->.
    enough (fEq: f = f') by (revert fEq; intros ->; 
      replace f_rel with f_rel' by (apply proof_irrelevance);
      now replace funct with funct' by (apply proof_irrelevance)).
    apply functional_extensionality_dep; intro x.
    specialize (f_rel x). specialize (f_rel' x).
    assert (proj1_sig (f x) = proj1_sig (f' x)) as K.
    { assert (forall v, proj1_sig (f x) = v <-> proj1_sig (f' x) = v) as Hp.
      { intro y; now rewrite (f_rel' y). }
      now rewrite Hp. 
    }
    destruct (f x) as [fx fx_p], (f' x) as [f'x f'x_p].
    simpl in K. revert K. intros ->.
    now replace fx_p with f'x_p by (apply proof_irrelevance).
Qed.

#[global] Instance packPr {argTps: ArgListT} {uargTps:UArgListT} {z:projectsArgListT argTps uargTps} 
  {T:Type} {p: forall (xs:ArgList argTps), T -> Prop}: 
  (@Pack argTps uargTps z T p) ⤖ (@uPack uargTps T) := {| 
    proj:=packPr_proj; 
    po:=packPr_po |}.

Global Notation packProj p := ((@packPr _ _ _ _ _).(proj) p).

Inductive get_rel {argTps: ArgListT} {uargTps:UArgListT} {z:projectsArgListT argTps uargTps} 
  {T:Type} {p: forall (x:ArgList argTps), T -> Prop}
	(f: forall (x:ArgList argTps), {v:T|p x v}): (UArgList uargTps) -> T -> Prop :=
	Get_rel (x: UArgList uargTps) (v:T) (xp:{x':ArgList argTps | prArgList x' uargTps z= x}): proj1_sig (f (proj1_sig xp)) = v -> get_rel f x v.

Ltac projPO :=
  match goal with
  | [h: ?inst.(proj) _ = ?inst.(proj) _ |- _] => apply inst.(po) in h; 
    first [rewrite h in * | revert h; intros ->]
  | [inst: @GeneralizedProjection ?T ?T' |- ?x' = ?y'] => 
    let xpTp := type of x' in
    eq_fail xpTp T';
    apply inst.(po)
  | [h: @prArgList ?xTp ?x ?uT ?z = @prArgList ?xTp ?x' ?uT _ |- _] =>
      apply (@gprArgList xTp uT z).(po) in h;
      try rewrite -> h in *
  end.

Ltac get_rel_rel := intros; 
  split; intros H;
  [unshelve econstructor; try (refine (exist _ _ eq_refl); assumption); simpl; 
  assumption|
  strong_inversion H; simpl in *; repeat cleanup_hints; simpl in *; 
  repeat projPO; easy].

Lemma get_rel_rel {xT: ArgListT} {uT:UArgListT} {z:projectsArgListT xT uT} 
  {T:Type} {p: forall x:ArgList xT, T -> Prop} 
  f: forall (x:ArgList xT) (v:T), proj1_sig (f x) = v <-> @get_rel xT uT z T p f (prArgList x uT z) v.
Proof.
  get_rel_rel.
Qed.

Ltac get_rel_funct :=
  let H:=fresh "H" in
  let K:=fresh "K" in
  intros H K; strong_inversion H; strong_inversion K;
  match goal with
  | [xp: {x': ArgList ?argTps | @prArgList ?argTps x' _ _ = ?x} |- _] => isVar argTps; isVar x;
    match goal with
    [xp': {x': ArgList argTps | @prArgList argTps x' _ _ = x} |- _] => 
      tryif (eq_fail xp xp') then fail else idtac;
      let x1'_def := fresh "x1'_def" in
      let x2'_def := fresh "x2'_def" in
      destruct xp' as [? x1'_def], xp as [? x2'_def]; fix_notations;
      rewrite <- x1'_def in x2'_def
    end
  end;
  repeat projPO; reflexivity.

Lemma get_rel_funct {argTps: ArgListT} {uargTps:UArgListT} {z:projectsArgListT argTps uargTps} 
  {T:Type} {p: forall (x:ArgList argTps), T -> Prop} 
      f (x:UArgList uargTps) (v v':T):
	@get_rel argTps uargTps z T p f x v -> @get_rel argTps uargTps z T p f x v' -> v = v'.
Proof.
  get_rel_funct.
Qed.

Definition mkPack {argTps: ArgListT} {uargTps:UArgListT} {z:projectsArgListT argTps uargTps} 
  {T:Type} {p: forall x:ArgList argTps, T -> Prop} 
  (f: forall x:ArgList argTps, {v:T|p x v}) : @Pack argTps uargTps z T p.
Proof.
  refine ({| f := f; frel := @get_rel argTps uargTps z T p f; 
              f_frel := get_rel_rel f; funct := get_rel_funct f |}).
Defined.

Definition mkUPack {argTps: ArgListT} {uargTps:UArgListT} {z:projectsArgListT argTps uargTps} 
  {T:Type} {p: forall x:ArgList argTps, T -> Prop} 
  (f: forall x:ArgList argTps, {v:T|p x v}) : @uPack uargTps T :=
  ({| rel_u := @get_rel argTps uargTps z T p f; 
             funct_u := get_rel_funct f |}).

Inductive SubArgList: ArgListT -> ArgListT -> Type :=
  | noArgsSub: SubArgList noArgsT noArgsT
  | consArgsSub (X X' X'':Type) (prX': X' ⤖ X) (prX'': X'' ⤖ X) (argsT : forall (x:X'), ArgListT) (argsT': forall (x:X''), ArgListT) 
      (castX: forall (x:X'), X'' ↼ x): forall (_:X'),
        (forall (x:X'), SubArgList (argsT x) (argsT' (castX x).(genSubCast))) -> 
          SubArgList (@consArgsT X X' prX' argsT) (@consArgsT X X'' prX'' argsT').

Fixpoint subArgListWf {argTps argTps': ArgListT} (subArgs: SubArgList argTps argTps'):
  forall (v v':UArgListT), projectsArgListT argTps' v -> projectsArgListT argTps v' -> v = v'.
Proof.
  destruct subArgs as [|? ? ? ? ? ? ? ? x ?].
  - intros v v' H K. 
    destruct v; destruct v'; try easy. 
  - intros v v' H1 H2. 
    destruct v; destruct v'; try easy. simpl in *. 
    destruct H1 as [<- H1], H2 as [<- H2]. f_equal.
    exact (subArgListWf (argsT x) (argsT' (@genSubCast X X' X'' prX' prX'' x (castX x))) (s x) v v' (H1 (@genSubCast X X' X'' prX' prX'' x (castX x))) (H2 x)).
Qed.
Lemma unconsSubArgList_Aux {X X' prX tlT X0 X'0 g a} 
  (subArgs: SubArgList (consArgsT X X' prX tlT) (consArgsT X0 X'0 g a)):
  X = X0.
Proof.
  inversion subArgs.
  apply H.
Qed. 

Ltac unconsSubArgList_pre X X' prX tlT X'0 g a subArgs := 
  let eqA0 := fresh "eqA0" in
  let eqA1 := fresh "eqA1" in
  refine (match
     subArgs as term in (SubArgList a0 a1)
     return
       (forall (eqA0: a0 = consArgsT X X' prX tlT) 
        (eqA1: a1 = consArgsT X X'0 g a)
        (eqTm: (eq_rect a1 _ (eq_rect a0 (fun Y=>SubArgList Y a1) term _ eqA0) _ eqA1) = subArgs),
        _)
   with
   | noArgsSub =>fun eqA0 eqA1 eqTm=>
      False_rect _ (@eq_ind ArgListT noArgsT
                   (fun e : ArgListT =>
                    match e with
                    | noArgsT => True
                    | consArgsT _ _ _ _ => False
                    end) I (consArgsT X X' prX tlT) eqA0)
   | consArgsSub X0 X'1 X'' prX' prX'' argsT argsT' castX x x0 =>fun eqA0 eqA1 eqTm=>
       _
   end eq_refl eq_refl eq_refl);
  
  pose proof (consArgsT_inj2 eqA0) as ->;
  pose proof (consArgsT_inj2 eqA1) as ->;
  pose proof (consArgsT_inj1 eqA1) as ->;
  pose proof (consArgsT_inj3 eqA0) as ->;
  pose proof (consArgsT_inj3 eqA1) as ->;
  pose proof (consArgsT_inj4 eqA0) as ->;
  pose proof (consArgsT_inj4 eqA1) as ->.

Definition unconsSubArgList1 {X X' prX tlT X'0 g a} 
  (subArgs: SubArgList (consArgsT X X' prX tlT) (consArgsT X X'0 g a)):
  forall (x:X'), X'0 ↼ x. 
Proof.
  unconsSubArgList_pre X X' prX tlT X'0 g a subArgs.
  exact castX.
Defined.
Definition unconsSubArgList2 {X X' prX tlT X'0 g a} 
  (subArgs: SubArgList (consArgsT X X' prX tlT) (consArgsT X X'0 g a)):
  X'. 
Proof.
  unconsSubArgList_pre X X' prX tlT X'0 g a subArgs.
  refine x.
Defined.

Definition unconsSubArgList {X X' prX tlT X'0 g a} 
  (subArgs: SubArgList (consArgsT X X' prX tlT) (consArgsT X X'0 g a)):
  sigT (fun (castX: forall (x:X'), X'0 ↼ x) => sigT (fun (y:X') => forall (x:X'), 
    SubArgList (tlT x) (a (castX x).(genSubCast)))). 
Proof.
  unconsSubArgList_pre X X' prX tlT X'0 g a subArgs.
  refine (existT _ castX (existT _ x x0)).
Defined.
Definition unconsSubArgList3 {X X' prX tlT X'0 g a} 
  (subArgs: SubArgList (consArgsT X X' prX tlT) (consArgsT X X'0 g a)):=
  projT2 (projT2 (unconsSubArgList subArgs)).

Lemma unconsSubArgList_correct {X X' prX tlT X'0 g a} 
  (subArgs: SubArgList (consArgsT X X' prX tlT) (consArgsT X X'0 g a)):
  subArgs = consArgsSub X X' X'0 prX g tlT a 
    (projT1 (unconsSubArgList subArgs)) (projT1 (projT2 (unconsSubArgList subArgs))) (projT2 (projT2 (unconsSubArgList subArgs))).
Proof.
  set (unconsSubArgList subArgs) as unconsSubArgs in *.

  unconsSubArgList_pre X X' prX tlT X'0 g a subArgs.
  revert eqTm. intros <-.
  simpl in *. repeat rewrite <- eq_rect_eq in *.
  set (@eq_rect ArgListT (consArgsT X X'0 prX'' argsT') (SubArgList (consArgsT X X' prX' argsT))
       (@eq_rect ArgListT (consArgsT X X' prX' argsT)
          (fun Y : ArgListT => SubArgList Y (consArgsT X X'0 prX'' argsT'))
          (consArgsSub X X' X'0 prX' prX'' argsT argsT' castX x x0) (consArgsT X X' prX' argsT) eqA0)
       (consArgsT X X'0 prX'' argsT') eqA1) as consSubArgs in *. 
  pose proof (@eq_rect_eq ArgListT (consArgsT X X'0 prX'' argsT') (SubArgList (consArgsT X X' prX' argsT))
  (@eq_rect ArgListT (consArgsT X X' prX' argsT)
       (fun Y : ArgListT => SubArgList Y (consArgsT X X'0 prX'' argsT'))
       (consArgsSub X X' X'0 prX' prX'' argsT argsT' castX x x0) (consArgsT X X' prX' argsT) eqA0) eqA1) as H.
  set (@eq_rect ArgListT (consArgsT X X'0 prX'' argsT') (SubArgList (consArgsT X X' prX' argsT))
  (@eq_rect ArgListT (consArgsT X X' prX' argsT)
     (fun Y : ArgListT => SubArgList Y (consArgsT X X'0 prX'' argsT'))
     (consArgsSub X X' X'0 prX' prX'' argsT argsT' castX x x0) (consArgsT X X' prX' argsT) eqA0)
  (consArgsT X X'0 prX'' argsT') eqA1) as bla in *.
  revert H. intros <-.
  pose proof (@eq_rect_eq ArgListT (consArgsT X X' prX' argsT)
    (fun Y : ArgListT => SubArgList Y (consArgsT X X'0 prX'' argsT'))
    (consArgsSub X X' X'0 prX' prX'' argsT argsT' castX x x0) eqA0
  ) as H.
  set (@eq_rect ArgListT (consArgsT X X' prX' argsT)
    (fun Y : ArgListT => SubArgList Y (consArgsT X X'0 prX'' argsT'))
    (consArgsSub X X' X'0 prX' prX'' argsT argsT' castX x x0) (consArgsT X X' prX' argsT) eqA0) as bla in *.
  revert H. intros <-.
  subst consSubArgs. clear eqA0 eqA1. 
  simpl in *. unfold eq_rect_r in *.
  repeat (cleanup_leading_eq_rects unconsSubArgs).
  
  subst unconsSubArgs. simpl in *. reflexivity.
Defined.

Fixpoint subCastArgList {argTps argTps': ArgListT} (subArgs: SubArgList argTps argTps') (args:ArgList argTps):
  (ArgList argTps').
Proof.
  destruct args.
  - destruct argTps'.
    + exact noArgs.
    + exfalso. inversion subArgs.
  - destruct argTps'. 
    + exfalso. inversion subArgs.
    + 
      pose proof (unconsSubArgList_Aux subArgs) as <-.
      pose proof (unconsSubArgList subArgs) as [castX [_ p]].
      refine (consArgs (castX x).(genSubCast) (subCastArgList _ _ (p x) args)).
Defined.

Fixpoint subCastArgList_po {argTps argTps': ArgListT} (subArgs: SubArgList argTps argTps') 
  {uargTps:UArgListT} {z:projectsArgListT argTps uargTps} {z':projectsArgListT argTps' uargTps}
  (xs:ArgList argTps):
  prArgList (subCastArgList subArgs xs) uargTps z' = prArgList xs uargTps z.
Proof.
  destruct subArgs.
  - pose proof (noArgsLemma xs) as ->.
    unfold subCastArgList.
    f_equal. apply proof_irrelevance.
  - pose proof (uncons_correct xs) as ->.
    set (projT1 (uncons xs)) as hd in *.
    set (projT2 (uncons xs)) as tl in *.
    simpl. repeat rewrite <- eq_rect_eq in *.
    destruct uargTps; [exfalso; apply z|].
    simpl in tl. simpl in z. simpl in z'.
    destruct z as [<- z].
    destruct z' as [? z'].
    rewrite <- eq_rect_eq.
    set (unconsSubArgList (consArgsSub X X' X'' prX' prX'' argsT argsT' castX x s)) as term in *.
    destruct term eqn:E.
    simpl in term.
    unfold eq_rect_r in *.
    repeat cleanup_leading_eq_rects term.
    destruct s0 eqn:F.
    simpl in *.
    rewrite <- eq_rect_eq in *.
    unfold genSubCast. simpl.
    set (x0 hd) as temp in *.
    pose proof temp.(cast_pr) as cast_pr. unfold genSubCast in cast_pr.
    revert cast_pr. intros ->. f_equal.
    simpl. 
    set (z' ⌊ temp _⌋) as prf_ in *.
    pose proof prf_ as prf; replace prf_ with prf in * by (apply proof_irrelevance); clear prf_.
    clear z'. 
    set (z hd) as prf'_ in *; pose proof prf'_ as prf'; 
    replace prf'_ with prf' in * by (apply proof_irrelevance); clear prf'_ z.
    subst term. 
    inversion E as [[K1 K2 K3]].
    revert K1 K2. intros <- <-.
    apply existT_inj in K3. revert K3. intros <-.
    apply subCastArgList_po.
Qed.

(* a generalized subsumption cast for Packs *)
#[global] Instance SubPack_cast 
  {argTps: ArgListT} {T:Type} {p: forall x:ArgList argTps, T -> Prop}
  {argTps': ArgListT} {q: forall x:ArgList argTps', T -> Prop}
  {uargTps:UArgListT} {z:projectsArgListT argTps uargTps} {z':projectsArgListT argTps' uargTps}
  (fpack: @Pack argTps uargTps z T p) (castX: SubArgList argTps' argTps)
  (castT: forall (args:ArgList argTps'), 
    {v:T | q args v} ↼ (fpack.(f) (subCastArgList castX args))):
  (@Pack argTps' uargTps z' T q).
Proof.
  destruct fpack as [f rel f__frel funct].
    unshelve refine {| 
      f:=fun x=>(castT x).(genSubCast); 
      frel:=rel; 
      f_frel:=fun args' v => _; 
      funct:=funct|}.
    destruct (castT args') as [castT_cst castT_po].
    destruct castT_cst as [y y_p]. simpl in *. 
    rewrite castT_po.
    rewrite -> (f__frel (subCastArgList castX args') v).
    replace (prArgList args' uargTps z') with (prArgList (subCastArgList castX args') uargTps z); [easy|].
    apply (subCastArgList_po castX args').
Defined.

Local Lemma SubPack_cast_pr: forall 
  {argTps: ArgListT} {T:Type} {p: forall x:ArgList argTps, T -> Prop}
  {argTps': ArgListT} {q: forall x:ArgList argTps', T -> Prop}
  {uargTps:UArgListT} {z:projectsArgListT argTps uargTps} {z':projectsArgListT argTps' uargTps}
  (fpack: @Pack argTps uargTps z T p) (castX: SubArgList argTps' argTps)
  (castT: forall (args:ArgList argTps'), 
    {v:T | q args v} ↼ (fpack.(f) (subCastArgList castX args))),
  packPr.(proj) (@SubPack_cast argTps T p argTps' q uargTps z z' fpack castX castT) = packPr.(proj) fpack.
Proof.
  intros. unfold SubPack_cast.
  destruct fpack as [f rel f__frel funct].
  reflexivity.
Qed.

Definition subPack {argTps: ArgListT} {T:Type} {p: forall x:ArgList argTps, T -> Prop}
  {argTps': ArgListT} {q: forall x:ArgList argTps', T -> Prop}
  {uargTps:UArgListT} {z:projectsArgListT argTps uargTps} {z':projectsArgListT argTps' uargTps}
  (fpack: @Pack argTps uargTps z T p) (castX: SubArgList argTps' argTps)
  (castT: forall (args:ArgList argTps'), 
    {v:T | q args v} ↼ (fpack.(f) (subCastArgList castX args))):
   (@Pack argTps' uargTps z' T q) ↼ fpack :=
  {| genSubCast := SubPack_cast fpack castX castT; cast_pr := SubPack_cast_pr fpack castX castT |}.

Fixpoint getPackF_spec {argTps:ArgListT}: forall {T: Type} {p: forall (args: ArgList argTps), T -> Prop}, Type :=
  match argTps with
  | noArgsT => fun T p => {v:T|p noArgs v}
  | consArgsT X X' g argTps' => fun T p => forall (x: X'), @getPackF_spec (argTps' x) T (fun xTs => p (@consArgs X X' g x argTps' xTs))
  end.
Fixpoint getFun {argTps:ArgListT}: forall {T: Type} {p: forall (args: ArgList argTps), T -> Prop} (pack_f:forall (args: ArgList argTps), {v:T| p args v}), 
  @getPackF_spec argTps T p := match argTps with
  | noArgsT => fun T p f => f noArgs
  | consArgsT X X' g argTps' => fun T p f x => 
    (getFun (fun xs => f (@consArgs X X' g x argTps' xs)))
  end.
Definition getPackF {argTps:ArgListT} {uargTps:UArgListT} {z:projectsArgListT argTps uargTps} 
  {T: Type} {p: forall (args: ArgList argTps), T -> Prop} (pack:@Pack argTps uargTps z T p):=
  getFun pack.(f).

Ltac getPackRel_Aux pack_rel :=
  match type of pack_rel with
  | forall (uargs: UArgList ?uargTps) (v:?T), Prop =>
    match uargTps with
    | noUArgsT => exact (pack_rel noUArgs)
    | consUArgsT ?X ?uargTps' => 
      let x := fresh "x" in
      intros x;
      getPackRel_Aux (fun xs => pack_rel (@consUArgs X x uargTps' xs))
    end 
  end.
Global Notation getPackRel pack := ltac:(getPackRel_Aux pack.(frel)).
Global Notation getUPackRel upack := ltac:(getPackRel_Aux upack.(rel_u)).

Ltac getPackRel_spec uargTps T :=
  let remUArgTps := fresh "remUArgTps" in
  pose uargTps as remUArgTps;
  repeat (
    let temp := fresh "temp" in
    assert (remUArgTps = remUArgTps) as temp by reflexivity; subst remUArgTps;
    match type of temp with
    | noUArgsT => exact (T->Prop)
    | consUArgsT ?X ?uargTps' => refine (X -> _);
      pose uargTps' as remUArgTps
    end; clear temp).
Fixpoint getPackRelSpec {uargTps:UArgListT}: forall {T: Type}, Type :=
  match uargTps with
  | noUArgsT => fun T => T->Prop
  | consUArgsT X uargTps' => fun T => X->@getPackRelSpec uargTps' T
  end.
Local Fixpoint getPackRel_Aux {uargTps:UArgListT}: forall {T: Type} (pack_rel:forall (uargs: UArgList uargTps) (v:T), Prop), 
  @getPackRelSpec uargTps T := match uargTps with
  | noUArgsT => fun T rel => rel noUArgs
  | consUArgsT X uargTps' => fun T rel x => (getPackRel_Aux (fun xs => rel (@consUArgs X x uargTps' xs)))
  end.
(*Definition getPackRel {argTps:ArgListT} {uargTps:UArgListT} {z:projectsArgListT argTps uargTps} 
  {T: Type} {p: forall (args: ArgList argTps), T -> Prop} 
  (pack:@Pack argTps uargTps z T p):=
  getPackRel_Aux pack.(frel).
Definition getUPackRel {uargTps:UArgListT} {T: Type} (upack:@uPack uargTps T):=
  getPackRel_Aux upack.(rel_u).*)

Fixpoint getCor_spec {argTps:ArgListT}: 
  forall {uargTps:UArgListT} {z:projectsArgListT argTps uargTps} {T: Type} 
  {p: forall (args: ArgList argTps), T -> Prop}
  (pack_f: forall  (args:ArgList argTps), {v:T | p args v}) 
  (pack_frel: forall (uargs: UArgList uargTps) (v:T), Prop), Type.
Proof.
  intros uargTps z T p pack_f pack_frel.
  destruct argTps; destruct uargTps.
  - exact (forall v, proj1_sig (@getFun noArgsT T p pack_f) = v <-> (ltac:(getPackRel_Aux pack_frel)) v).
  - exfalso. apply z.
  - exfalso. apply z.
  - refine (forall (x':X'), _).
    refine (getCor_spec (a x') uargTps (pr2 z x') T (fun xs => p (@consArgs X X' g x' a xs)) _ _).
    + exact (fun xs => pack_f (@consArgs X X' g x' a xs)). 
    + pose proof (pr1 z) as <-.
      exact (fun xs => pack_frel (consUArgs (g.(proj) x') xs)).
Defined.
Local Fixpoint getCor_Aux {argTps:ArgListT}: 
  forall {uargTps:UArgListT} {z:projectsArgListT argTps uargTps} {T: Type} 
  {p: forall (args: ArgList argTps), T -> Prop}
  (pack_f: forall  (args:ArgList argTps), {v:T | p args v}) 
  (pack_frel: forall (uargs: UArgList uargTps) (v:T), Prop)
  (pack_f__frel:forall (args:ArgList argTps) (v:T), proj1_sig (pack_f args) = v <-> 
  pack_frel (prArgList args uargTps z) v), @getCor_spec argTps uargTps z T p pack_f pack_frel.
Proof.
  intros uargTps z T p pack_f pack_frel pack_cor.
  destruct argTps; destruct uargTps.
  - intro v. exact (pack_cor noArgs v).
  - exfalso. apply z.
  - exfalso. apply z.
  - intro x'. destruct z as [<- z]. 
    apply (getCor_Aux (a x') uargTps (z x') T (fun xs => p (@consArgs X X' g x' a xs))
    (fun xs => pack_f (@consArgs X X' g x' a xs)) 
    (fun xs => pack_frel (consUArgs (g.(proj) x') xs))
    (fun args v => pack_cor (consArgs x' args) v)
    ).
Defined.
Definition getPackCor {argTps:ArgListT} {uargTps:UArgListT} {z:projectsArgListT argTps uargTps} 
  {T: Type} {p: forall (args: ArgList argTps), T -> Prop} 
  (pack:@Pack argTps uargTps z T p) :=
  getCor_Aux pack.(f) pack.(frel) pack.(f_frel).

Fixpoint getFunct_spec {uargTps:UArgListT}: forall {T: Type} 
  (pack_frel: forall (uargs: UArgList uargTps) (v:T), Prop), Type.
Proof.
  refine (fun T pack_frel =>
  match uargTps as u return ((UArgList u -> T -> Prop) -> Type) with
   | noUArgsT =>
       fun pack_frel0 : UArgList noUArgsT -> T -> Prop =>
       forall v v' : T, ltac:(getPackRel_Aux pack_frel0) v -> ltac:(getPackRel_Aux pack_frel0) v' -> v = v'
   | consUArgsT X tl =>
       (fun (X0 : Type) (uargTps0 : UArgListT)
          (pack_frel0 : UArgList (consUArgsT X0 uargTps0) -> T -> Prop) =>
        forall x : X0,
        getFunct_spec uargTps0 T (fun xs : UArgList uargTps0 => pack_frel0 (consUArgs x xs))) X
         tl
   end pack_frel).
Defined.
Local Fixpoint getFunct_Aux {uargTps:UArgListT}: forall {T: Type}
  (pack_frel: forall (uargs: UArgList uargTps) (v:T), Prop)
  (pack_funct:forall (uargs: UArgList uargTps) (v v':T), 
  pack_frel uargs v -> pack_frel uargs v' -> v = v'), getFunct_spec pack_frel.
Proof.
  refine (fun T frel funct=>_).
  destruct uargTps.
  - exact (funct noUArgs).
  - refine (fun x => getFunct_Aux uargTps T
      (fun xs => frel (consUArgs x xs))
      (fun uargs => funct (consUArgs x uargs))
    ).
Defined.

Definition getPackFunct {argTps:ArgListT} {uargTps:UArgListT} {z:projectsArgListT argTps uargTps} 
  {T: Type} {p: forall (args: ArgList argTps), T -> Prop} 
  (pack:@Pack argTps uargTps z T p) :=
  getFunct_Aux pack.(frel) pack.(funct).
Definition getUPackFunct {uargTps:UArgListT} 
  {T: Type} (upack:@uPack uargTps T) :=
  getFunct_Aux upack.(rel_u) upack.(funct_u).

Class FlattenedPack {f_type frel_type:Type} := {
  flattenedF: f_type;
  flattenedFrel: frel_type;
  cor_type: Type;
  flattenedCor: cor_type;
  funct_type: Type;
  flattenedFunct: funct_type
}.
#[global] Instance flattenPack {argTps:ArgListT} {uargTps:UArgListT} {z:projectsArgListT argTps uargTps}
  {T: Type} {p: forall (args: ArgList argTps), T -> Prop} 
  (pack:@Pack argTps uargTps z T p): @FlattenedPack (@getPackF_spec argTps T p) (@getPackRelSpec uargTps T).
Proof.
  refine {| flattenedF:=getPackF pack; flattenedFrel:=getPackRel_Aux pack.(frel); 
  flattenedCor:=getPackCor pack; flattenedFunct:=getPackFunct pack|}.
Defined.

Ltac cleanup_pack_stuff:=
  repeat (
  first [
    rewrite <- eq_rect_eq in * |
    progress unfold proj in * |
    progress unfold genSubCast in * |
    progress unfold eq_rect_r in * |
    progress unfold internal_eq_rew_dep in * |
    progress unfold getPackF in * |
    progress unfold getFun in * |
    progress unfold rel_u in * |
    match goal with
    | [H : _ _ {| rel_u := _; funct_u := _ |} _ |- _] => 
      simpl in H; do_nonbranching (strong_inversion H)
    | [H : _ {| rel_u := _; funct_u := _ |} _ _ |- _] => 
      simpl in H; do_nonbranching (strong_inversion H)
    | [H : _ _ _{| rel_u := _; funct_u := _ |} _ |- _] => 
      simpl in H; do_nonbranching (strong_inversion H)
    | [H : _ _ {| rel_u := _; funct_u := _ |} _ _ |- _] => 
      simpl in H; do_nonbranching (strong_inversion H)
    | [H : _ {| rel_u := _; funct_u := _ |} _ _ _ |- _] => 
      simpl in H; do_nonbranching (strong_inversion H)
    end; try unfold rel_u in *; simpl in * |
    rewrite uncons_correct_aux in * |
    match goal with
    | [f: forall (args: ArgList ?argTps), {v: ?utp | (
      let (x, a) := uncons args in 
        fun _ : uncons args = existT _ x a => ?cond v /\ True) eq_refl 
      } |- _] => 
      let H := fresh "f_ret_wf" in
      assert (H: forall (args: ArgList argTps), cond (proj1_sig (f args))) by
        (intros args; 
        let fapp_u := fresh "fapp_u" in
        let fapp_p := fresh "fapp_p" in
        destruct (f args) as [fapp_u fapp_p];
        destruct (uncons args); easy);
      match goal with
      | |- cond proj1_sig (f ?ts) => 
        apply (H ts)
      | |- cond proj1_sig (f ?ts) /\ _ => 
        split; [apply (H ts)|]
      | |- forall _, cond (proj1_sig (f ?ts)) /\ _ => intro; 
        split; [apply (H ts)|]
      | |- forall _, cond (proj1_sig (f ?ts)) => intro; 
        apply (H ts)
      end
    end
  ]
).

Ltac uncons_rw args x a e_p := 
  let e := fresh "e" in
  let E := fresh "E" in
  let temp := fresh "temp" in
  pose (uncons_correct args) as e_p; 
  pose (uncons args) as e;
  destruct e as [x a] eqn:E;
  assert (uncons args = e) as temp by reflexivity; rewrite temp in e_p; 
  try rewrite temp in *; clear temp;
  rewrite E in e_p; try subst e;
  try rewrite E in *; simpl in e_p; try clear E; try clear e.

Ltac unucons_rw args x u e_p := 
  let e := fresh "e" in
  let E := fresh "E" in
  let temp := fresh "temp" in
  pose (unucons_correct args) as e_p; 
  pose (unucons args) as e;
  destruct e as [x u] eqn:E;
  assert (unucons args = e) as temp by reflexivity; rewrite temp in e_p; 
  try rewrite temp in *; clear temp;
  rewrite E in e_p; try subst e;
  try rewrite E in *; simpl in e_p; try clear E; try clear e.

Ltac isprArgListAppl tm :=
  match tm with
  | prArgList _ _ _ => idtac
  end.

Ltac getFapp F unfoldedArgs :=
  let temp := fresh "temp" in
  let remArgs := fresh "remainingArgs" in
  let remArgsRefl := fresh "remainingArgsRefl" in
  pose F as temp;
  pose unfoldedArgs as remArgs;
  repeat (
    assert (remArgs = remArgs) as remArgsRefl by reflexivity;
    subst remArgs;
    match type of remArgsRefl with
    | consArgs ?x ?tl = _ => clear remArgsRefl;
      let temp2 := fresh "temp2" in
      pose (temp x) as temp2;
      subst temp;
      pose tl as remArgs;
      pose temp2 as temp;
      subst temp2 
    | noArgs => clear remArgsRefl
    end
  ); clear remArgs; 
  assert (temp = temp) as remArgsRefl by reflexivity;
  subst temp;
  match type of remArgsRefl with
  | ?res = _ => clear remArgsRefl; 
    exact res
  end.

Ltac getRelapp Rel unfoldedUArgs :=
  let temp := fresh "temp" in
  let remArgs := fresh "remainingArgs" in
  let remArgsRefl := fresh "remainingArgsRefl" in
  pose Rel as temp;
  pose unfoldedUArgs as remArgs;
  repeat (
    assert (remArgs = remArgs) as remArgsRefl by reflexivity;
    subst remArgs;
    match type of remArgsRefl with
    | consUArgs ?x ?tl = _ => clear remArgsRefl;
      let temp2 := fresh "temp2" in
      pose (temp x) as temp2;
      subst temp;
      pose tl as remArgs;
      pose temp2 as temp;
      subst temp2 
    | noArgs => clear remArgsRefl
    end
  ); clear remArgs; 
  assert (temp = temp) as remArgsRefl by reflexivity;
  subst temp;
  match type of remArgsRefl with
  | ?res = _ => clear remArgsRefl; 
    exact res
  end.

Ltac uncons_rw_all args :=
  let e_p := fresh "e_p" in
  let a := fresh "a" in
  pose args as a;
  repeat (
    let aRefl := fresh "aRefl" in
    let x := fresh "x_" in
    let tl := fresh "tl" in
    assert (a = a) as aRefl by reflexivity;
    subst a;
    match type of aRefl with
    | ?xs = _ => clear aRefl;
      uncons_rw xs x tl e_p;
      revert e_p; intros ->;
      tryif (isVar e_p) then fail else idtac;
      pose tl as a
    end
  ); clear a.

Ltac uncons_rw_app_all f args :=
  let e_p := fresh "e_p" in
  let a := fresh "a" in
  pose args as a;
  repeat (
    let aRefl := fresh "aRefl" in
    let x := fresh "x_" in
    let tl := fresh "tl" in
    assert (a = a) as aRefl by reflexivity;
    subst a;
    match type of aRefl with
    | ?xs = _ => clear aRefl;
      uncons_rw xs x tl e_p;
      revert e_p; intros ->;
      tryif (isVar e_p) then fail else idtac;
      pose tl as a;
      specialize (f x)
    end
  ); clear a.

Ltac unucons_rw_all uargs :=
  let e_p := fresh "e_p" in
  let a := fresh "a" in
  pose uargs as a;
  repeat (
    let aRefl := fresh "aRefl" in
    let x := fresh "x_" in
    let tl := fresh "tl" in
    assert (a = a) as aRefl by reflexivity;
    subst a;
    match type of aRefl with
    | ?xs = _ => clear aRefl;
      unucons_rw xs x tl e_p;
      revert e_p; intros ->;
      pose tl as a
    end
  ); clear a.

Ltac unucons_rw_app_all rel uargs :=
  let e_p := fresh "e_p" in
  let a := fresh "a" in
  pose uargs as a;
  repeat (
    let aRefl := fresh "aRefl" in
    let x := fresh "x_" in
    let tl := fresh "tl" in
    assert (a = a) as aRefl by reflexivity;
    subst a;
    match type of aRefl with
    | ?xs = _ => clear aRefl;
      unucons_rw xs x tl e_p;
      revert e_p; intros ->;
      pose tl as a;
      specialize (rel x)
    end
  ); clear a.

Ltac mkProjectsArgListTG argTps uargTps :=
  let tempA := fresh "tempA" in
  let tempU := fresh "tempU" in
  let tempARefl := fresh "tempARefl" in
  let tempURefl := fresh "tempURefl" in
  pose argTps as tempA; pose uargTps as tempU;
  try unfold argTps in tempA; try unfold uargTps in tempU;
  repeat (
    try simpl in tempA;
    assert (tempA = tempA) as tempARefl by reflexivity;
    subst tempA;

    (* in case uargTps is a shelved goal *)
    tryif (
    try simpl in tempU;
    assert (tempU = tempU) as tempURefl by reflexivity;
    unfold tempU in tempURefl;
    match type of tempURefl with
      | consUArgsT _ _ = _ => clear tempURefl
      | noUArgsT = _ => clear tempURefl
    end
    ) then idtac else (
    match type of tempARefl with
    | @consArgsT ?X ?X' ?PX ?tl = _ => 
      let temp := fresh "temp" in
      let tempU' := fresh "tempU_" in
      refine (let tempU' : UArgListT := _ in _);
      assert (tempU = consUArgsT X tempU') as temp by (unfold tempU; reflexivity);
      try replace uargTps with tempU by reflexivity;
      revert temp; intros ->;
      set (consUArgsT X tempU') as tempU in *; subst tempU'
    | noArgsT = _ =>
      let temp := fresh "temp" in
      assert (tempU = noUArgsT) as temp by (unfold tempU; reflexivity);
      try replace uargTps with tempU by reflexivity;
      revert temp; intros ->;
      pose noUArgsT as tempU
    end);

    assert (tempU = tempU) as tempURefl by reflexivity;
    subst tempU; simpl in *;
    match type of tempARefl with
    | @consArgsT ?X ?X' ?PX ?tl = _ => clear tempARefl;
      match type of tempURefl with
      | consUArgsT X ?tlu = _ => clear tempURefl;
        first [
        refine (@conj _ (forall (x:X'), projectsArgListT (tl x) tlu) (eq_refl X) _) | 
        split; [reflexivity|]];
        let x' := fresh "x'" in
        intro x';
        pose (tl x') as tempA; pose tlu as tempU
      end
    | noArgsT = _ => clear tempARefl; clear tempURefl; exact I
    end
  ).

Ltac hyps_of_tp tp already Res :=
  return Res _nil;
  repeat progress (match goal with
    | [h: tp |- _] => tryif (contains_res h Res) then fail else (
        tryif (contains_res h already) then fail else prepend_res Res h
      )
    end).

Global Ltac flattenP P args v :=
  try (
  isVar P; 
  match type of P with
  | ?pTp => subst pTp
  end);
  let pz := fresh "pz" in
  pose P as pz;
  uncons_rw_app_all pz args;
  exact (pz v).

Goal forall (X X':Type) (PX: X' ⤖ X) (Z:Type) (PZ: forall (x:X'), Z -> Prop) 
  (F: forall (x:X'), {v:Z|PZ x v}) (x1 x2: X'), Z -> Prop.
Proof.
  intros X X' PX Z PZ F x1 x2. 
  intros v.
  refine (let argTps : ArgListT := (X' ::RT (fun _ => nilRT)) in _).
  refine (let args: ArgList argTps := (x2 ::R nilR) in _).
  let pz := fresh "pz" in
  pose PZ as pz.
  flattenP pz args v.
Defined.

Ltac returnRefTp f :=
  let fApp := fresh "fApp" in
  pose f as fApp;
  repeat (
  match type of fApp with
  | forall (x:?X'), _ => 
    let x := fresh "x_" in
    refine (forall (x:X'), _);
    let temp := fresh "temp" in
    pose fApp as temp;
    subst fApp;
    pose (temp x) as fApp; subst temp
  | {_:?T | ?p} => let v := fresh "v" in
    exact (forall (v:T), Prop)
  | {v:?T | ?pApp v} => exact (forall (v:T), Prop)
  end).

Ltac returnRef f :=
  let fApp := fresh "fApp" in
  let temp := fresh "temp" in
  pose f as fApp;
  repeat (
  match type of fApp with
  | forall (x:?X'), _ => 
    let x := fresh "x_" in
    refine (fun (x:X') => _);
    pose fApp as temp;
    subst fApp;
    pose (temp x) as fApp; subst temp
  | {_:?T | ?p} => let v := fresh "v" in
    exact (fun (v:T) => p)
  | {v:?T | ?pApp v} => exact (fun (v:T) => pApp v)
  end).

Global Ltac buildArgTps f :=
  let fApp := fresh "fApp" in
  let temp := fresh "temp" in
  pose f as fApp;
  repeat (
  match type of fApp with
  | forall (x:?X'), _ => 
    refine (consArgsT _ X' (ltac:(synthesizePrInstance)) _);
    let x := fresh "x_" in
    refine (fun (x:X') => _);
    pose fApp as temp;
    subst fApp;
    pose (temp x) as fApp; subst temp
  | {_:?T | _} => exact noArgsT
  end).

Global Ltac buildUArgTpsF f :=
  let fApp := fresh "fApp" in
  let temp := fresh "temp" in
  pose f as fApp;
  repeat (
  match type of fApp with
  | forall (x:{v:?X | _}), _ => 
    refine (consUArgsT X _);
    let x := fresh "x_" in
    refine (fun (x:X) => _);
    pose fApp as temp;
    subst fApp;
    pose (temp x) as fApp; subst temp
  | forall (x:@Pack ?xArgTps ?xUArgTps ?z ?T ?p), _ => 
    refine (consUArgsT (uPack xUArgTps T) _);
    let x := fresh "x_" in
    refine (fun (x:(uPack xUArgTps T)) => _);
    pose fApp as temp;
    subst fApp;
    pose (temp x) as fApp; subst temp
  | {_:?T | _} => exact noArgsT
  end).

Ltac returnUTp rel :=
  let relTp := fresh "relTp" in
  let temp := fresh "temp" in
  let res := fresh "res" in
  let relTp := type of rel in
  pose relTp as res; 
  repeat (
    let temp := fresh "temp" in
    assert (res = res) as temp by reflexivity; subst res;
    match type of temp with
    | ?tp = _ => clear temp; match tp with
      | ?Z -> Prop => exact Z
      end
    | (?X' -> ?retTp) = _ => clear temp; tryif (eq_fail retTp Prop) then fail else idtac;
      pose retTp as res
    end).

Ltac returnUTpPZTp PZTp :=
  pose PZTp as res; 
  repeat (
    let temp := fresh "temp" in
    assert (res = res) as temp by reflexivity; subst res;
    match type of temp with
    | ?tp = _ => clear temp; match tp with
      | ?Z -> Prop => exact Z
      end
    | (?X' -> ?retTp) = _ => clear temp; tryif (eq_fail retTp Prop) then fail else idtac;
      pose retTp as res
    end).

Ltac returnUTpF F :=
  let argTps := fresh "argTps" in
  let PZTp := fresh "PZTp" in
  refine (let argTps : ArgListT := ltac:(buildArgTps F) in _);
  refine (let PZTp : Type := ltac:(returnRefTp F) in _); simpl in PZTp;
  returnUTpPZTp PZTp.

Global Ltac buildUArgTps rel :=
  let relTp := fresh "relTp" in
  let temp := fresh "temp" in
  let res := fresh "res" in
  let relTp := type of rel in
  pose relTp as res; 
  repeat (
    let temp := fresh "temp" in
    assert (res = res) as temp by reflexivity; subst res;
    match type of temp with
    | ?tp = _ => clear temp; match tp with
      | ?Z -> Prop => exact noUArgsT
      end
    | (?X -> ?retTp) = _ => clear temp; 
      tryif (eq_fail retTp Prop) then fail else idtac;
      refine (consUArgsT X _);
      pose retTp as res
    end).

Ltac buildPackG_spec F :=
  let z := fresh "z" in
  let Z := fresh "Z" in
  let PZTp := fresh "PZTp" in
  let PZ := fresh "PZ" in
  let p := fresh "p" in
  let argTps := fresh "argTps" in
  let uargTps := fresh "uargTps" in
  refine (let uargTps: UArgListT := ltac:(buildUArgTpsF F) in _);
  refine (let argTps : ArgListT := ltac:(buildArgTps F) in _);
  refine (let z: projectsArgListT argTps uargTps := ltac:(mkProjectsArgListTG argTps uargTps) in _);
  refine (let PZTp : Type := ltac:(returnRefTp F) in _); simpl in PZTp;
  refine (let PZ : PZTp := ltac:(subst PZTp; returnRef F) in _);
  refine (let Z: Type := ltac:(returnUTpPZTp PZTp) in _); 
  simpl in *;
  refine (let p: forall (args: ArgList argTps), Z -> Prop := fun args v => ltac:(flattenP PZ args v) in _);
  simpl in p;
  exact (@Pack argTps uargTps z Z p).

Global Lemma exist_inj {A:Type} {p:A} (x y:{v:A|v=p} ): x = y.
Proof.
  destruct x as [x ->], y as [y ->]. reflexivity.
Qed.

(*Global Lemma eq_rect_eq' (U : Type) (p p': U) (Q : U -> Type) (x : Q p) (h : p = p'):
  eq_rect p Q x p' h = eq_rect (exist _ p eq_refl) (fun (y:{q:U | q = p}) => Q ⌊ y -⌋).
@eq_rect ?A ?p ?Q ?x ?p' ?h*)

Global Ltac buildPackG_ F Rel F_Rel Funct :=
  let z := fresh "z" in
  let Z := fresh "Z" in
  let PZTp := fresh "PZTp" in
  let PZ := fresh "PZ" in
  let p := fresh "p" in
  let argTps := fresh "argTps" in
  let uargTps := fresh "uargTps" in
  let pack_f := fresh "pack_f" in
  let pack_rel := fresh "pack_rel" in
  let pack_cor := fresh "pack_cor" in
  let pack_funct := fresh "pack_funct" in
  refine (let uargTps: UArgListT := ltac:(buildUArgTps Rel) in _);
  refine (let argTps : ArgListT := ltac:(buildArgTps F) in _);
  refine (let z: projectsArgListT argTps uargTps := ltac:(mkProjectsArgListTG argTps uargTps) in _);
  refine (let PZTp : Type := ltac:(returnRefTp F) in _); simpl in PZTp;
  refine (let PZ : PZTp := ltac:(subst PZTp; returnRef F) in _);
  refine (let Z: Type := ltac:(returnUTpPZTp PZTp) in _); simpl in *;
  refine (let p: forall (args: ArgList argTps), Z -> Prop := fun args v => ltac:(flattenP PZ args v) in _);
  refine (let pack_f : forall (args:ArgList argTps), {v:Z | p args v} := 
  ltac:(intros args; unfold p;
  try clear F_Rel;
  uncons_rw_app_all F args;
  refine F
  ) in _); 
  refine (let pack_rel : forall (uargs:UArgList uargTps) (v:Z), Prop := fun uargs v => (ltac:(
    try unfold uargTps in *; 
    let rel := fresh "relAp" in
    pose Rel as rel;
    unucons_rw_app_all rel uargs;
    apply (rel v))) in _);
  
  unshelve refine {| f:=pack_f; frel:=pack_rel; f_frel:=_; funct:=_ |};

  try (intros args v;
  (* First part: destructing the argument list *)
  uncons_rw_all args;
  try unfold uargTps;
  
  (* if only this didn't fail for no apparent reason, we'd be about done here:
  repeat rewrite prArgListCons.*)

  let temp := fresh "temp" in
  match goal with 
  | |- _ <-> pack_rel ?tm v =>
    let temp2 := fresh "temp2" in
    pose tm as temp;
    let prArgListAppl := fresh "prArgListAppl" in
    let prArgListApplRefl := fresh "prArgListApplRefl" in
    repeat_or_fail (
      let tempRefl := fresh "tempRefl" in
      assert (temp = temp) as tempRefl by reflexivity; subst temp;
      match type of tempRefl with
      | ?tmp = _ => clear tempRefl;
        findSubExpr prArgListAppl isprArgListAppl tmp;
        assRefl prArgListAppl as prArgListApplRefl;
        match type of prArgListApplRefl with
        | ?term = _ => clear prArgListApplRefl; 
          set term as temp2 in *;
          match term with
          | prArgList (consArgs ?x' ?tl') (consUArgsT ?X ?tlUT) ?z =>
            let rw := fresh "rw" in
            eassert (rw: temp2 = _) by (refine (@prArgListCons X _ _ _ x' tl' _ _));
            match type of rw with
            | _ = ?RHS => 
              revert rw; intros ->;
              pose RHS as temp
            end
          end
        end
      end
    )
  end; clear temp;
  pose proof (noArgsLemma (ltac:(assumption))) as ->;
  let z_ := fresh "z_" in
  destruct z as [? z_]; simpl;
  
  (* second part: rewriting the applications of pack_f and pack_rel using two inline lemmata and 
     applying F_Rel to solve the goal *)
  match goal with
  | |- proj1_sig (pack_f ?unfoldedArgs) = v <->
pack_rel ?unfoldedUArgs v =>
    unshelve (assert (proj1_sig (pack_f unfoldedArgs) = proj1_sig (ltac:(getFapp F unfoldedArgs) )) as f_lem by shelve;
    assert (pack_rel unfoldedUArgs = (ltac:(getRelapp Rel unfoldedUArgs))) as rel_lem by shelve; simpl;
    rewrite f_lem; rewrite rel_lem; try apply F_Rel); simpl
  end;
  (* final part: proving the two lemmata *)
  [ unfold pack_f; 
    repeat (
    let rw := fresh "rw" in
    match goal with
    | |- proj1_sig ((let (x, a) := uncons (@consArgs ?X ?X' ?prX ?argTps' ?x' ?tl') in ?bdy) ?z) = ?FApp =>
      pose proof (@uncons_correct_aux X X' prX x' argTps' tl') as rw;
      match type of rw with
      | ?LHS = ?RHS => 
        let rhsTp := type of RHS in
        pose (
        fun (x0:{v:rhsTp | LHS = v}) => proj1_sig ((let (x, a) as s return (LHS = s -> _) := proj1_sig x0 in bdy) ⌈ x0 ⌉) = FApp
      ) as P;
      assert (exist _ RHS rw = exist _ LHS eq_refl) as rwEq by
      (rewrite rw; solve_pi_unif_subgoal);
      enough (P (exist _ RHS rw)) as P_RHS;
      [ apply (@eq_ind _ _ P P_RHS (exist _ LHS eq_refl) rwEq)| subst P; simpl; unfold eq_rect_r; 
      repeat rewrite <- eq_rect_eq; 
      clear rwEq]
      end
    end; 
    tryif (revert rw; intros ->; rewrite <- eq_rect_eq) then idtac else (
      simpl;
      match goal with
      | |- proj1_sig (@eq_rect ?A ?p ?Q ?x ?p' ?h) = ?RHS =>
        let P := fresh "P" in
        pose (fun (s:{v:A|v=p}) => proj1_sig (eq_rect p Q x (proj1_sig s) (eq_sym ⌈ s ⌉)) = RHS) as P;
        let p'r := fresh "p'r" in
        pose (exist (fun v=>v=p) p' (eq_sym h)) as p'r;
        let tempRw := fresh "tempRw" in
        assert ((proj1_sig (@eq_rect A p Q x p' h ) = RHS ) = P p'r) 
        as tempRw by (unfold p'r; unfold P; simpl; repeat replace (eq_sym (eq_sym h)) with h by (apply proof_irrelevance); reflexivity); 
        revert tempRw; intros ->;
        unshelve refine (@eq_ind {v:A|v=p} (exist _ p (eq_refl p)) P
          _ p'r (exist_inj (exist _ p (eq_refl p)) p'r ));
        subst P; subst p'r; simpl;
        unfold eq_rect_r; unfold internal_eq_rew_dep;
        repeat (match goal with 
        | |- proj1_sig ((let (x, a) := let (_, _) := consArgsT_inj eq_refl in _ in ?bdy) ?z) = ?FApp =>
          let temp := fresh "temp" in
          set (consArgsT_inj eq_refl) as temp;
          destruct temp as [? ?]
        | |- proj1_sig ((let (x, a) := let (_, _) := ?s in _ in ?bdy) ?z) = ?FApp =>
          destruct s as [? ?]
        | |- proj1_sig (@eq_rect ?A ?x ?P ?LHS ?x ?z) = ?FApp =>
          pose proof (eq_sym (@eq_rect_eq A x P LHS z)) as ->
        end)
      end
    );
    try rewrite <- eq_rect_eq); 
    solve_pi_unif_subgoal |
    unfold pack_rel; simpl in *;
    solve_pi_unif_subgoal]);
    try (intros uargs v v' H K;
    try unfold uargTps in *;
    unfold pack_rel in *; simpl in *;
    unucons_rw_app_all Funct uargs;
    symmetry; apply Funct; now assumption).

Ltac buildUPackG_spec Rel :=
  let Z := fresh "Z" in
  let uargTps := fresh "uargTps" in
  refine (let uargTps: UArgListT := ltac:(buildUArgTps Rel) in _);
  refine (let Z: Type := ltac:(returnUTp Rel) in _); 
  simpl in *;
  exact (@uPack uargTps Z).

Global Ltac buildUPackG Rel Funct :=
  let Z := fresh "Z" in
  let uargTps := fresh "uargTps" in
  let pack_rel := fresh "pack_rel" in
  let pack_funct := fresh "pack_funct" in
  refine (let uargTps: UArgListT := ltac:(buildUArgTps Rel) in _);
  refine (let Z: Type := ltac:(returnUTp Rel) in _); simpl in *;
  refine (let pack_rel : forall (uargs:UArgList uargTps) (v:Z), Prop := (ltac:(
    let uargs := fresh "uargs" in
    let v := fresh "v" in
    intros uargs v;
    try unfold uargTps in *; 
    let rel := fresh "relAp" in
    pose Rel as rel;
    unucons_rw_app_all rel uargs;
    apply (rel v))) in _);
  unshelve refine {| rel_u:=pack_rel; funct_u:=_ |};
  intros uargs ? ? ? ?;
  try unfold uargTps in *;
  unfold pack_rel in *; simpl in *;
  unucons_rw_app_all Funct uargs;
  symmetry; apply Funct; now assumption.

Global Ltac fun_to_rel F Z :=
  let z := fresh "z" in
  let PZTp := fresh "PZTp" in
  let PZ := fresh "PZ" in
  let p := fresh "p" in
  let argTps := fresh "argTps" in
  let uargTps := fresh "uargTps" in
  let pack_f := fresh "pack_f" in
  let pack_rel := fresh "pack_rel" in
  refine (let argTps : ArgListT := ltac:(buildArgTps F) in _);
  refine (let uargTps : UArgListT := _ in _);
  refine (let z: projectsArgListT argTps uargTps := ltac:(mkProjectsArgListTG argTps uargTps) in _);
  refine (let PZTp : Type := ltac:(returnRefTp F) in _); simpl in PZTp;
  refine (let PZ : PZTp := ltac:(subst PZTp; returnRef F) in _); simpl in *;
  refine (let p: forall (args: ArgList argTps), Z -> Prop := fun args v => ltac:(flattenP PZ args v) in _);
  refine (let pack_f : forall (args:ArgList argTps), {v:Z | p args v} := 
  ltac:(intros args; unfold p;
  uncons_rw_app_all F args;
  repeat (specialize (F (ltac:(assumption))));
  refine F
  ) in _); 
  refine (let pack_rel : forall (uargs:UArgList uargTps) v, Prop := fun uargs v =>
    @get_rel argTps uargTps (ltac:(mkProjectsArgListTG argTps uargTps)) _ p pack_f uargs v in _);
  refine (getPackRel_Aux pack_rel).


Global Ltac fun_to_pack F :=
  let z := fresh "z" in
  let Z := fresh "Z" in
  let PZTp := fresh "PZTp" in
  let PZ := fresh "PZ" in
  let p := fresh "p" in
  let argTps := fresh "argTps" in
  let uargTps := fresh "uargTps" in
  let pack_f := fresh "pack_f" in
  let pack_rel := fresh "pack_rel" in
  refine (let argTps : ArgListT := ltac:(buildArgTps F) in _);
  refine (let uargTps : UArgListT := ltac:(buildUArgTpsF F) in _);
  refine (let z: projectsArgListT argTps uargTps := ltac:(mkProjectsArgListTG argTps uargTps) in _);
  refine (let PZTp : Type := ltac:(returnRefTp F) in _); simpl in PZTp;
  refine (let Z : Type := ltac:(returnUTpPZTp PZTp) in _);
  refine (let PZ : PZTp := ltac:(subst PZTp; returnRef F) in _); simpl in *;
  refine (let p: forall (args: ArgList argTps), Z -> Prop := fun args v => ltac:(flattenP PZ args v) in _);
  refine (let pack_f : forall (args:ArgList argTps), {v:Z | p args v} := 
  ltac:(intros args; unfold p;
  let G := fresh "G" in
  pose F as G;
  uncons_rw_app_all G args;
  repeat (specialize (G (ltac:(assumption))));
  refine G
  ) in _); 
  refine (mkPack pack_f).

Section GenericTest1.
(* Converting from a generic binary function with relation and properties to a Pack *)
Variable X X':Type.
Variable PX: X' ⤖ X.
Variable Z:Type.
Variable PZ: forall (x:X'), Z -> Prop.
Variable F: forall (x:X'), {v:Z|PZ x v}.
Variable Rel: X -> Z -> Prop.
Variable F_Rel: forall (x:X') (v:Z), proj1_sig (F x) = v <-> Rel (PX.(proj) x) v.
Variable Funct: forall (x:X) (v v':Z), Rel x v -> Rel x v' -> v = v'.

Definition buildPack1_ : ltac:(buildPackG_spec F).
Proof.
  buildPackG_ F Rel F_Rel Funct.
Defined.
Definition buildUPack1 : ltac:(buildUPackG_spec Rel).
Proof. 
  buildUPackG Rel Funct. 
Defined.
Definition unreflectedRel1 : X -> Z -> Prop.
Proof.
  clear F_Rel.
  fun_to_rel F Z.
Defined.
Definition unreflectedPack1: ltac:(buildPackG_spec F).
Proof.
  fun_to_pack F.
Defined.
End GenericTest1. 
Global Notation buildPack1 F Rel F_Rel Rel_Funct:= (buildPack1_ _ _ _ _ _ F Rel F_Rel Rel_Funct).
Section GenericTest2.
(* Converting from a generic binary function with relation and properties to a Pack *)
Variable X X':Type.
Variable PX: X' ⤖ X.
Variable Y:Type.
Variable Y': forall (x:X'), Type.
Variable PY: forall (x:X'), (Y' x) ⤖ Y.
Variable Z:Type.
Variable PZ: forall (x:X') (y:Y' x), Z -> Prop.
Variable F: forall (x:X') (y:Y' x), {v:Z|PZ x y v}.
Variable Rel: X -> Y -> Z -> Prop.
Variable F_Rel: forall (x:X') (y:Y' x) (v:Z), proj1_sig (F x y) = v <-> Rel (PX.(proj) x) ((PY x).(proj) y) v.
Variable Funct: forall (x:X) (y:Y) (v v':Z), Rel x y v -> Rel x y v' -> v = v'.

Definition buildPack2_ : ltac:(buildPackG_spec F).
Proof.
  buildPackG_ F Rel F_Rel Funct.
Defined.
Definition buildUPack2 : ltac:(buildUPackG_spec Rel).
Proof. 
  buildUPackG Rel Funct. 
Defined.
Definition unreflectedRel2 : X -> Y -> Z -> Prop.
Proof.
  clear F_Rel.
  fun_to_rel F Z.
Defined.
Definition unreflectedPack2: ltac:(buildPackG_spec F).
Proof.
  fun_to_pack F.
Defined.
End GenericTest2. 
Global Notation buildPack2 F Rel F_Rel Rel_Funct:= (buildPack2_ _ _ _ _ _ _ _ _ F Rel F_Rel Rel_Funct).
Section GenericTest2'.
(* Converting from a binary function with twice the same argument type, its relation and properties to a Pack *)
Variable X X':Type.
Variable PX: X' ⤖ X.
Variable Z:Type.
Variable PZ: forall (x:X') (y:X'), Z -> Prop.
Variable F: forall (x:X') (y:X'), {v:Z|PZ x y v}.
Variable Rel: X -> X -> Z -> Prop.
Variable F_Rel: forall (x:X') (y:X') (v:Z), proj1_sig (F x y) = v <-> Rel (PX.(proj) x) (PX.(proj) y) v.
Variable Funct: forall (x:X) (y:X) (v v':Z), Rel x y v -> Rel x y v' -> v = v'.

Definition buildPack2'_spec : Type.
Proof.
  buildPackG_spec F.
Defined.
Definition buildPack2' : buildPack2'_spec.
Proof.
  buildPackG_ F Rel F_Rel Funct.
Defined.
Definition buildUPack2'_spec : Type.
Proof.
  buildUPackG_spec Rel.
Defined.
Definition buildUPack2' : buildUPack2'_spec.
Proof. 
  buildUPackG Rel Funct. 
Defined.
Definition unreflectedRel2' : X -> X -> Z -> Prop.
Proof.
  clear F_Rel.
  fun_to_rel F Z.
Defined.
End GenericTest2'. 
Section GenericTest3.
(* Converting from a generic binary function with relation and properties to a Pack *)
Variable X X':Type.
Variable PX: X' ⤖ X.
Variable Y:Type.
Variable Y': forall (x:X'), Type.
Variable PY: forall (x:X'), (Y' x) ⤖ Y.
Variable Z:Type.
Variable Z': forall (x:X') (y:Y' x), Type.
Variable PZ: forall (x:X') (y:Y' x), (Z' x y) ⤖ Z.
Variable T: Type.
Variable PT: forall (x:X') (y:Y' x) (z:Z' x y), T -> Prop.
Variable F: forall (x:X') (y:Y' x) (z:Z' x y), {v:T|PT x y z v}.
Variable Rel: X -> Y -> Z -> T -> Prop.
Variable F_Rel: forall (x:X') (y:Y' x) (z:Z' x y) (v:T), proj1_sig (F x y z) = v <-> 
  Rel (PX.(proj) x) ((PY x).(proj) y) ((PZ x y).(proj) z) v.
Variable Funct: forall (x:X) (y:Y) (z:Z) (v v':T), Rel x y z v -> Rel x y z v' -> v = v'.

Definition buildPack3_ : (ltac:(buildPackG_spec F)).
Proof.
  buildPackG_ F Rel F_Rel Funct.
Defined.
Definition buildUPack3_ : ltac:(buildUPackG_spec Rel).
Proof. 
  buildUPackG Rel Funct. 
Defined.
Definition unreflectedRel3 : X -> Y -> Z -> T -> Prop.
Proof.
  clear F_Rel.
  fun_to_rel F T.
Defined.
Definition unreflectedPack3: ltac:(buildPackG_spec F).
Proof.
  fun_to_pack F.
Defined.
End GenericTest3.
Global Notation buildPack3 F Rel F_Rel Rel_Funct:= (buildPack3_ _ _ _ _ _ _ _ _ _ _ _ F Rel F_Rel Rel_Funct).
Section GenericTest4.
(* Converting from a generic binary function with relation and properties to a Pack *)
Variable W W':Type.
Variable PW: W' ⤖ W.
Variable X:Type.
Variable X': forall (w:W'), Type.
Variable PX: forall (w:W'), (X' w) ⤖ X.
Variable Y:Type.
Variable Y': forall (w:W') (x:X' w), Type.
Variable PY: forall (w:W') (x:X' w), (Y' w x) ⤖ Y.
Variable Z:Type.
Variable Z': forall (w:W') (x:X' w) (y:Y' w x), Type.
Variable PZ: forall (w:W') (x:X' w) (y:Y' w x), (Z' w x y) ⤖ Z.
Variable T: Type.
Variable PT: forall (w:W') (x:X' w) (y:Y' w x) (z:Z' w x y), T -> Prop.
Variable F: forall (w:W') (x:X' w) (y:Y' w x) (z:Z' w x y), {v:T|PT w x y z v}.
Variable Rel: W -> X -> Y -> Z -> T -> Prop.
Variable F_Rel: forall (w:W') (x:X' w) (y:Y' w x) (z:Z' w x y) (v:T), proj1_sig (F w x y z) = v <-> 
  Rel (PW.(proj) w) ((PX w).(proj) x) ((PY w x).(proj) y) ((PZ w x y).(proj) z) v.
Variable Funct: forall (w:W) (x:X) (y:Y) (z:Z) (v v':T), Rel w x y z v -> Rel w x y z v' -> v = v'.

Definition buildPack4_ : (ltac:(buildPackG_spec F)).
Proof.
  buildPackG_ F Rel F_Rel Funct.
Defined.
Definition buildUPack4_ : ltac:(buildUPackG_spec Rel).
Proof. 
  buildUPackG Rel Funct. 
Defined.
Definition unreflectedRel4 : W -> X -> Y -> Z -> T -> Prop.
Proof.
  clear F_Rel.
  fun_to_rel F T.
Defined.
Definition unreflectedPack4: ltac:(buildPackG_spec F).
Proof.
  fun_to_pack F.
Defined.
End GenericTest4.
Global Notation buildPack4 F Rel F_Rel Rel_Funct:= (buildPack4_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F Rel F_Rel Rel_Funct).

Global Definition refinement_proj_unapply {A:Type} {p:A -> Prop} (tm: {v:A|p v}):
  proj1_sig tm = refinement_proj.(proj) tm := eq_refl.

Global Ltac buildPackG F Rel F_Rel Funct :=
  let cor := fresh "cor" in
  match type of F_Rel with
  | forall x1 v, ⌊ ?f x1 -⌋ = v <-> ?rel _ v =>
    first [
      now apply (buildPack1 F Rel F_Rel Funct) |
      assert (forall x1 v, ⌊ f x1 -⌋ = v <-> rel (proj x1) v) as cor by
        (apply F_Rel);
      apply (buildPack1 F Rel cor Funct)]
  | forall x1 x2 v, ⌊ ?f x1 x2 -⌋ = v <-> ?rel _ _ v =>
    first [
      now apply (buildPack1 F Rel F_Rel Funct) |
      assert (forall x1 x2 v, ⌊ f x1 x2 -⌋ = v <-> rel (proj x1) (proj x2) v) as cor by
      (apply F_Rel);
    apply (buildPack2 F Rel cor Funct)]
  | forall x1 x2 x3 v, ⌊ ?f x1 x2 x3 -⌋ = v <-> ?rel _ _ _ v =>
    first [
      now apply (buildPack1 F Rel F_Rel Funct) |
      assert (forall x1 x2 x3 v, ⌊ f x1 x2 x3 -⌋ = v <-> rel (proj x1) (proj x2) (proj x3) v) as cor by
      (apply F_Rel);
    apply (buildPack3 F Rel cor Funct)]
  | forall x1 x2 x3 x4 v, ⌊ ?f x1 x2 x3 x4 -⌋ = v <-> ?rel _ _ _ _ v =>
    first [
      now apply (buildPack1 F Rel F_Rel Funct) |
      assert (forall x1 x2 x3 x4 v, ⌊ f x1 x2 x3 x4 -⌋ = v <-> rel (proj x1) (proj x2) (proj x3) (proj x4) v) as cor by
      (apply F_Rel);
    apply (buildPack4 F Rel cor Funct)]
  | forall x1 v, proj1_sig (?f x1) = v <-> ?rel _ v =>
    first [
      now apply (buildPack1 F Rel F_Rel Funct) |
      assert (forall x1 v, proj1_sig (f x1) = v <-> rel (proj x1) v) as cor by
        (apply F_Rel);
      apply (buildPack1 F Rel cor Funct)]
  | forall x1 x2 v, proj1_sig (?f x1 x2) = v <-> ?rel _ _ v =>
    first [
      now apply (buildPack1 F Rel F_Rel Funct) |
      assert (forall x1 x2 v, proj1_sig (f x1 x2) = v <-> rel (proj x1) (proj x2) v) as cor by
      (apply F_Rel);
    apply (buildPack2 F Rel cor Funct)]
  | forall x1 x2 x3 v, proj1_sig (?f x1 x2 x3) = v <-> ?rel _ _ _ v =>
    first [
      now apply (buildPack1 F Rel F_Rel Funct) |
      assert (forall x1 x2 x3 v, proj1_sig (f x1 x2 x3) = v <-> rel (proj x1) (proj x2) (proj x3) v) as cor by
      (apply F_Rel);
    apply (buildPack3 F Rel cor Funct)]
  | forall x1 x2 x3 x4 v, proj1_sig (?f x1 x2 x3 x4) = v <-> ?rel _ _ _ _ v =>
    first [
      now apply (buildPack1 F Rel F_Rel Funct) |
      assert (forall x1 x2 x3 x4 v, proj1_sig (f x1 x2 x3 x4) = v <-> rel (proj x1) (proj x2) (proj x3) (proj x4) v) as cor by
      (apply F_Rel);
    apply (buildPack4 F Rel cor Funct)]
  | _ => 
    let F_ := fresh "F" in
    let Rel_ := fresh "Rel" in
    let F_Rel_ := fresh "F_Rel" in
    let Funct_ := fresh "Funct" in
    pose F as F_;
    pose Rel as Rel_;
    pose F_Rel as F_Rel_;
    pose Funct as Funct_;
    buildPackG_ F_ Rel_ F_Rel_ Funct_
  end.
