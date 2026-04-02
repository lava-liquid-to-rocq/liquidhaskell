Require Import ZArith Int.
Open Scope Z_scope.
Open Scope Int_scope.

(* A simplified model for uPacks and the universe issue with nesting them. *)
Section SimplifiedModel.
(* For self-containedness's sake we copy the definition of UArgListT here. *)
Polymorphic Inductive UArgListT' : Type :=
  | noUArgsT': UArgListT'
  | consUArgsT' (X:Type) (tl:UArgListT'): UArgListT'.
Polymorphic Inductive UArgList' : UArgListT' -> Type :=
    noUArgs' : UArgList' noUArgsT'
  | consUArgs' : forall {X : Type },
                X ->
                forall {tlT : UArgListT' },
                UArgList' tlT ->
                UArgList' (consUArgsT' X tlT).
Print UArgList'.

Polymorphic Definition uPack2 (A:UArgListT') (B:Type): Type := 
  UArgList' A -> B.
Print uPack2.
(* Definition ValF2_u': uPack2 (consUArgsT (uPack2 (consUArgsT Z noUArgsT) Z) (consUArgsT Z noUArgsT)) Z -> Z. *)

(* The above example is a minimal faling example based on the structure on the real example below: *)
Axiom ValF2_u': @uPack2 (consUArgsT' (@uPack2 (consUArgsT' Z noUArgsT') Z) (consUArgsT' Z noUArgsT')) Z -> Z.
End SimplifiedModel.
From coqDeps Require Export LiquidPreludeUtil.
(* which in turn models the issue in the translation of higher-order datatypes of rank >2, exemplified below: *) 
Inductive Identity_F2 : Type :=
  ValF2_u: uPack ((uPack (Z ::UT noUArgsT) Z) ::UT (Z ::UT noUArgsT)) Z -> Z -> Identity_F2.