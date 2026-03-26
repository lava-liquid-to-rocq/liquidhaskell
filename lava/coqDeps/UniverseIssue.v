Require Import ZArith Int.
Open Scope Z_scope.
Open Scope Int_scope.

(* For self-containedness's sake we copy the definition of UArgListT here. *)
  Polymorphic Inductive UArgListT@{u} : Type@{u+1} :=
  | noUArgsT: UArgListT
  | consUArgsT (X:Type@{u}) (tl:UArgListT): UArgListT.
Inductive UArgList@{u v} : UArgListT@{u} -> Type@{u+1} :=
    noUArgs : UArgList noUArgsT@{u}
  | consUArgs : forall {X : Type@{u} },
                X ->
                forall {tlT : UArgListT },
                UArgList tlT ->
                UArgList (consUArgsT@{u} X tlT).

Polymorphic Definition uPack2@{u} (A:UArgListT@{u}) (B:Type@{u}): Type@{u+1} := 
  UArgList A -> B.

(* We want to define something like this:
Definition inter@{u} : UArgListT@{u+1} := consUArgsT (@uPack2@{u} (consUArgsT Z nilUT) Z) (consUArgsT Z nilUT).

But Rocq doesn't allow us to specify the universe levels as above. 

If instead we omit the explicit universe levels, as below, Rocq creates a new fresh variable for the universe level.
*)

Definition inter : UArgListT := consUArgsT (@uPack2 (consUArgsT Z noUArgsT) Z) (consUArgsT Z noUArgsT).
Print inter.
(* yields
inter =
(uPack2@{UArgList.u} Z ::UT noUArgsT Z) ::UT Z ::UT noUArgsT
     : UArgListT@{inter.u0}

Here Rocq remembers u < u0, in fact u0 should be just u + 1 *)

(* When we now attempt to actually use inter inside a more interesting term, we get issues:

We would like to simply write:
Definition ValF2_u'@{u}: @uPack2@{u+1} (consUArgsT (@uPack2@{u} (consUArgsT Z noUArgsT) Z) (consUArgsT Z noUArgsT)) Z -> Z. 

But Rocq doesn't allow the universe level increment syntax in that place. So instead we can try:
*)
Fail Definition ValF2_u'@{u}: @uPack2 (consUArgsT (@uPack2@{u} (consUArgsT Z noUArgsT) Z) (consUArgsT Z noUArgsT)) Z -> Z. 

(* Which yields the error:
The term "(uPack2@{u} Z ::UT noUArgsT Z) ::UT Z ::UT noUArgsT" has type
 "UArgListT@{coqDeps.UniverseIssue.155}"
while it is expected to have type "UArgListT@{UArgList.u}"
(universe inconsistency: Cannot enforce coqDeps.UniverseIssue.155 =
UArgList.u because UArgList.u < coqDeps.UniverseIssue.155).

Apparently Rocq identifies the universe levels of the two uPacks, which is of course absolutely hopelessly wrong. 
But as we cannot explicitely specify the correct level, I'm not sure how to address that issue.*)

(* The above example is a minimal faling example based on the structure on the real example below: *)
Fail Definition ValF2_u': @uPack (consUArgsT (@uPack (consUArgsT Z noUArgsT) Z) (consUArgsT Z noUArgsT)) Z -> Z.
(* which in turn models the issue in the translation of higher-order datatypes of rank >2, exemplified below: *) 
Fail Inductive Identity_F2 : Type :=
  ValF2_u': @uPack2 ((@uPack2 (Z ::UT noUArgsT) Z) ::UT (Z ::UT noUArgsT)) Z -> Z.