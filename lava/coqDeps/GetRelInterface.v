Require Import Logic.FunctionalExtensionality.
Load SimpleTacticUtils.

(* This file contains the classes and inductive types for packs *)

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

Global Notation "X ::UT tl" := (consUArgsT X tl) (at level 2, right associativity).
Global Notation "X' ::RT tl" := (consArgsT _ X' _ tl) (at level 2, right associativity).
Global Notation "x ::R tl" := (@consArgs _ _ _ x _ tl) (at level 2, right associativity).
Global Notation "x ::U tl" := (@consUArgs _ x _ tl) (at level 2, right associativity).
Global Notation nilUT := noUArgsT.
Global Notation nilU := noUArgs.
Global Notation nilRT := noArgsT.
Global Notation nilR := noArgs.

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


Inductive SubArgList: ArgListT -> ArgListT -> Type :=
  | noArgsSub: SubArgList noArgsT noArgsT
  | consArgsSub (X X' X'':Type) (prX': X' ⤖ X) (prX'': X'' ⤖ X) (argsT : forall (x:X'), ArgListT) (argsT': forall (x:X''), ArgListT) 
      (castX: forall (x:X'), X'' ↼ x): forall (_:X'),
        (forall (x:X'), SubArgList (argsT x) (argsT' (castX x).(genSubCast))) -> 
          SubArgList (@consArgsT X X' prX' argsT) (@consArgsT X X'' prX'' argsT').
