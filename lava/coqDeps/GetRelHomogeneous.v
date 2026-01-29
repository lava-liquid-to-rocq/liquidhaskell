Require Import Logic.FunctionalExtensionality.
Load TacticUtils.

(* This file contains the function packs and other higher-order stuff *)

(** Typeclass for functions *)

Class Pack (X: Type) (X': Type) (prX: X' ⤖ X) (Y:Type) (Y': forall (x:X'), Type) 
  (prY: forall (x:X'), (Y' x) ⤖ Y) (Xr:Type) (Yr:Type):= {
	f : forall (x:X'), Y' x;      (* The refined function *)
  frel:Xr->Yr->Prop;
  correspondenceTp:Prop;        (*The type of the correspondence lemma, depends on Xr, Xy *)
  f_frel:correspondenceTp;
  functionhoodTp:Prop;          (*The type of the functionhood property, depends on Xr, Xy *)
  funct:functionhoodTp;
}.

Class PackBB (A:Type) (p:A->Prop) (B:Type) (q:forall (x:{v:A|p v}), B->Prop) := {
  fBB: forall (x:{v:A|p v}), {v:B|q x v};
  frelBB: (A->Prop)->(B->Prop)->Prop;
  fBB_frelBB (a:{v:A|p v}) (a_rel:A->Prop) 
    (a_rel_funct: forall v v', a_rel v -> a_rel v' -> v = v') (b:B) (b_rel:B->Prop) 
    (b_rel_funct: forall v v', b_rel v -> b_rel v' -> v = v'):
    a_rel ⌊ a ⌋ -> b_rel b -> 
      (⌊ fBB a ⌋ = b <-> frelBB a_rel b_rel);
  functBB (a_rel:A->Prop) 
    (a_rel_funct: forall v v', a_rel v -> a_rel v' -> v = v') (b_rel:B->Prop) 
    (b_rel_funct: forall v v', b_rel v -> b_rel v' -> v = v'): frelBB a_rel b_rel ->
    forall (b1 b2:B), b_rel b1 -> b_rel b2 -> b1 = b2;
}.
Class uPack (A B: Type) (Ar Br:Type) := {
  frel_u : Ar -> Br -> Prop;   (* The graph relation *)
  functionhoodTp_u:Prop;
	funct_u: functionhoodTp_u    (*functionhood of frel_u, depends on arity of Xr Yr *)
}.

Definition packPr {X: Type} {X': Type} {prX: X' ⤖ X} {Y:Type} {Y': forall (x:X'), Type} 
  {prY: forall (x:X'), (Y' x) ⤖ Y} {Xr:Type} {Yr:Type} 
  (pack:Pack X X' prX Y Y' prY Xr Yr): (@uPack X Y Xr Yr) :=
  {|frel_u:=pack.(frel); funct_u:=pack.(funct)|}.

Definition packPrPo {X: Type} {X': Type} {prX: X' ⤖ X} {Y:Type} {Y': forall (x:X'), Type} 
  {prY: forall (x:X'), (Y' x) ⤖ Y} {Xr:Type} {Yr:Type}:Prop :=
forall (x y:Pack X X' prX Y Y' prY Xr Yr), packPr x = packPr y -> x = y.

#[global] Instance packPr' {X: Type} {X': Type} {prX: X' ⤖ X} {Y:Type} {Y': forall (x:X'), Type} 
  {prY: forall (x:X'), (Y' x) ⤖ Y} {Xr:Type} {Yr:Type}
  (po:@packPrPo X X' prX Y Y' prY Xr Yr): 
  (Pack X X' prX Y Y' prY Xr Yr) ⤖ (uPack X Y Xr Yr) :=
  {|proj:=packPr; po:= po|}.

Class PackBF (A:Type) (p:A->Prop) (X Y:Type) 
  (X': forall (a:{v:A|p v}), Type) (prX: forall (a:{v:A|p v}), (X' a) ⤖ X) 
  (Y': forall (a:{v:A|p v}) (x:X' a), Type) (prY: forall (a:{v:A|p v}) (x:X' a), (Y' a x) ⤖ Y)
  (Xr: Type) (Yr:Type)  
  (prB_po: forall (a:{v:A|p v}), @packPrPo X (X' a) (prX a) Y (Y' a) (prY a) Xr Yr):Type
  := {
  fBF: forall (a:{v:A|p v}), @Pack X (X' a) (prX a) Y (Y' a) (prY a) Xr Yr;
  frelBF: (A->Prop)->(Xr->Yr->Prop)->Prop;
  fBF_frelBF (a:{v:A|p v}) (a_rel:A->Prop)  
    (a_rel_funct: forall v v', a_rel v -> a_rel v' -> v = v') (b:@uPack X Y Xr Yr):  
    a_rel ⌊ a ⌋ -> 
      (packPr (fBF a) = b <-> frelBF a_rel b.(frel_u));
  functBF (a_rel:A->Prop)  
    (a_rel_funct: forall v v', a_rel v -> a_rel v' -> v = v') (b_rel:Xr->Yr->Prop) 
    (b_rel_funct: forall x v v', b_rel x v -> b_rel x v' -> v = v'): frelBF a_rel b_rel -> 
    forall (xr:Xr) (v v':Yr), b_rel xr v -> b_rel xr v' -> v = v';
}.
Class PackFB (X: Type) (X': Type) (prX: X' ⤖ X) (Y:Type) (Y': forall (x:X'), Type) 
  (prY: forall (x:X'), (Y' x) ⤖ Y) (Xr: Type) (Yr:Type)  
  (prA_po: @packPrPo X X' prX Y Y' prY Xr Yr)
  (B:Type) (p:forall (x:(@Pack X X' prX Y Y' prY Xr Yr)), B->Prop) := {
  fFB: forall (a:(@Pack X X' prX Y Y' prY Xr Yr)), {v:B|p a v};
  frelFB: (Xr->Yr->Prop)->(B->Prop)->Prop;
  fFB_frelFB (a:(@Pack X X' prX Y Y' prY Xr Yr)) (b:B) (b_rel:B->Prop) 
    (b_rel_funct: forall v v', b_rel v -> b_rel v' -> v = v'):
    b_rel b -> (⌊ fFB a ⌋ = b <-> frelFB (a.(frel)) b_rel);
  functFB (a_rel:Xr->Yr->Prop)  
    (a_rel_funct: forall x v v', a_rel x v -> a_rel x v' -> v = v') (b_rel:B->Prop)  
    (b_rel_funct: forall v v', b_rel v -> b_rel v' -> v = v'): frelFB a_rel b_rel ->
    forall (b1 b2:B), b_rel b1 -> b_rel b2 -> b1 = b2;
}.
Class PackFF (X: Type) (X': Type) (prX: X' ⤖ X) (Y:Type) (Y': forall (x:X'), Type) 
  (prY: forall (x:X'), (Y' x) ⤖ Y) (Xr: Type) (Yr:Type)  
  (pr1_po: @packPrPo X X' prX Y Y' prY Xr Yr)
  (A:Type) (A': forall (x:(@Pack X X' prX Y Y' prY Xr Yr)), Type)
  (prA:forall (x:(@Pack X X' prX Y Y' prY Xr Yr)), (A' x) ⤖ A)
  (B:Type) (B':forall (x:(@Pack X X' prX Y Y' prY Xr Yr)) (a:A' x), Type)
  (prB:forall (x:(@Pack X X' prX Y Y' prY Xr Yr)) (a:A' x),(B' x a) ⤖ B)
  (Ar Br: Type)
  (pr2_po:forall (x:(@Pack X X' prX Y Y' prY Xr Yr)), 
    @packPrPo A (A' x) (prA x) B (B' x) (prB x) Ar Br) := {
  fFF: forall (x:(@Pack X X' prX Y Y' prY Xr Yr)), 
    (@Pack A (A' x) (prA x) B (B' x) (prB x) Ar Br);
  frelFF: (Xr->Yr->Prop)->(Ar->Br->Prop)->Prop;
  fFF_frelFF (x:(@Pack X X' prX Y Y' prY Xr Yr)) (b:@uPack A B Ar Br):
    packPr (fFF x) = b <-> frelFF (x.(frel)) (b.(frel_u));
  functFF (a_rel:Xr->Yr->Prop)  
    (a_rel_funct: forall x v v', a_rel x v -> a_rel x v' -> v = v') (b_rel:Ar->Br->Prop)  
    (b_rel_funct: forall x v v', b_rel x v -> b_rel x v' -> v = v'): 
    frelFF a_rel b_rel -> forall (ar:Ar) (v v':Br), b_rel ar v -> b_rel ar v' -> v = v';
}.

#[global] Instance packBB (A:Type) (p:A->Prop) (B:Type) (q:forall (x:{v:A|p v}), B->Prop)
  (pack: PackBB A p B q): @Pack A {v:A|p v} refinement_proj B (fun x => {v:B|q x v}) 
  (fun x => @refinement_proj B (q x)) (A->Prop) (B->Prop) := 
  {|f:=fBB; frel:=frelBB; f_frel:=fBB_frelBB; funct:=functBB|}.

#[global] Instance packBF (A:Type) (p:A->Prop) (X Y:Type) 
  (X': forall (a:{v:A|p v}), Type) (prX: forall (a:{v:A|p v}), (X' a) ⤖ X) 
  (Y': forall (a:{v:A|p v}) (x:X' a), Type) (prY: forall (a:{v:A|p v}) (x:X' a), (Y' a x) ⤖ Y)
  (Xr: Type) (Yr:Type)  
  (prB_po: forall (a:{v:A|p v}), @packPrPo X (X' a) (prX a) Y (Y' a) (prY a) Xr Yr)
  (pack: PackBF A p X Y X' prX Y' prY Xr Yr (fun a=>prB_po a)): @Pack A {v:A|p v} refinement_proj 
  (@uPack X Y Xr Yr) (fun a=>@Pack X (X' a) (prX a) Y (Y' a) (prY a) Xr Yr) (fun a=>@packPr' X (X' a) (prX a) Y (Y' a) (prY a) Xr Yr (prB_po a)) (A->Prop) (Xr->Yr->Prop) :=
  {|f:=fBF; frel:=frelBF; f_frel:=fBF_frelBF; funct:=functBF|}.

#[global] Instance packFB (X: Type) (X': Type) (prX: X' ⤖ X) (Y:Type) (Y': forall (x:X'), Type) 
  (prY: forall (x:X'), (Y' x) ⤖ Y) (Xr: Type) (Yr:Type)  
  (prA_po: @packPrPo X X' prX Y Y' prY Xr Yr)
  (B:Type) (p:forall (x:(@Pack X X' prX Y Y' prY Xr Yr)), B->Prop)
  (pack:@PackFB X X' prX Y Y' prY Xr Yr prA_po B p):
  @Pack (@uPack X Y Xr Yr) (@Pack X X' prX Y Y' prY Xr Yr) {|proj:=packPr; po:=prA_po|} B (fun a=>{v:B|p a v}) 
    (fun a=>refinement_proj) (Xr->Yr->Prop) (B->Prop):=
  {|f:=fFB; frel:=frelFB; f_frel:=fFB_frelFB; funct:=functFB|}.

#[global] Instance packFF (X: Type) (X': Type) (prX: X' ⤖ X) (Y:Type) (Y': forall (x:X'), Type) 
  (prY: forall (x:X'), (Y' x) ⤖ Y) (Xr: Type) (Yr:Type)  
  (pr1_po: @packPrPo X X' prX Y Y' prY Xr Yr)
  (A:Type) (A': forall (x:(@Pack X X' prX Y Y' prY Xr Yr)), Type)
  (prA:forall (x:(@Pack X X' prX Y Y' prY Xr Yr)), (A' x) ⤖ A)
  (B:Type) (B':forall (x:(@Pack X X' prX Y Y' prY Xr Yr)) (a:A' x), Type)
  (prB:forall (x:(@Pack X X' prX Y Y' prY Xr Yr)) (a:A' x),(B' x a) ⤖ B)
  (Ar Br: Type)
  (pr2_po:forall (x:(@Pack X X' prX Y Y' prY Xr Yr)), 
    @packPrPo A (A' x) (prA x) B (B' x) (prB x) Ar Br)
  (pack:@PackFF X X' prX Y Y' prY Xr Yr pr1_po A A' prA B B' prB Ar Br pr2_po):
  @Pack (@uPack X Y Xr Yr) (@Pack X X' prX Y Y' prY Xr Yr) {|proj:=packPr; po:=pr1_po|} (@uPack A B Ar Br)
    (fun x=>@Pack A (A' x) (prA x) B (B' x) (prB x) Ar Br) (fun x=>{|proj:=packPr; po:=pr2_po x|}) (Xr->Yr->Prop) (Ar->Br->Prop)
  := {| f:=fFF; frel:=frelFF; f_frel:=fFF_frelFF; funct:=functFF|}.

Class uPackBB (A B:Type) := {
  frelBB_u: (A->Prop)->(B->Prop)->Prop;
  functBB_u (a_rel:A->Prop) 
    (a_rel_funct: forall v v', a_rel v -> a_rel v' -> v = v') (b_rel:B->Prop) 
    (b_rel_funct: forall v v', b_rel v -> b_rel v' -> v = v'): 
    frelBB_u a_rel b_rel -> forall (v v':B), b_rel v -> b_rel v' -> v = v'
}.

Class uPackBF (A X Y Xr Yr:Type) := {
  frelBF_u: (A->Prop)->(Xr->Yr->Prop)->Prop;
  functBF_u (a_rel:A->Prop) 
    (a_rel_funct: forall v v', a_rel v -> a_rel v' -> v = v') (b_rel:Xr->Yr->Prop) 
    (b_rel_funct: forall x v v', b_rel x v -> b_rel x v' -> v = v'): 
    frelBF_u a_rel b_rel -> 
    forall (xr:Xr) (v v':Yr), b_rel xr v -> b_rel xr v' -> v = v';
}.

Class uPackFB (X Y Xr Yr B:Type) := {
  frelFB_u: (Xr->Yr->Prop)->(B->Prop)->Prop;
  functFB_u (a_rel:Xr->Yr->Prop)
    (a_rel_funct: forall x v v', a_rel x v -> a_rel x v' -> v = v') (b_rel:B->Prop) 
    (b_rel_funct: forall v v', b_rel v -> b_rel v' -> v = v'): frelFB_u a_rel b_rel ->
    forall (v v':B), b_rel v -> b_rel v' -> v = v';
}.

Class uPackFF (X Y Xr Yr A B Ar Br:Type) := {
  frelFF_u: (Xr->Yr->Prop)->(Ar->Br->Prop)->Prop;
  functFF_u (a_rel:Xr->Yr->Prop)
    (a_rel_funct: forall x v v', a_rel x v -> a_rel x v' -> v = v') (b_rel:Ar->Br->Prop) 
    (b_rel_funct: forall x v v', b_rel x v -> b_rel x v' -> v = v'): frelFF_u a_rel b_rel ->
    forall (ar:Ar) (v v':Br), b_rel ar v -> b_rel ar v' -> v = v';
}.

#[global] Instance upackBB A B (upack:@uPackBB A B): @uPack A B (A->Prop) (B->Prop) :=
  {| frel_u:=frelBB_u; funct_u:=functBB_u |}.

#[global] Instance upackBF {A X Y Xr Yr} (upack:@uPackBF A X Y Xr Yr): 
  @uPack A (@uPack X Y Xr Yr) (A->Prop) (Xr->Yr->Prop) :=
  {| frel_u:=frelBF_u; funct_u:=functBF_u |}.

#[global] Instance upackFB {X Y Xr Yr B} (upack:@uPackFB X Y Xr Yr B): 
  @uPack (@uPack X Y Xr Yr) B (Xr->Yr->Prop) (B->Prop) :=
  {| frel_u:=frelFB_u; funct_u:=functFB_u |}.

#[global] Instance upackFF {X Y Xr Yr A B Ar Br} (upack:@uPackFF X Y Xr Yr A B Ar Br): 
  @uPack (@uPack X Y Xr Yr) (@uPack A B Ar Br) (Xr->Yr->Prop) (Ar->Br->Prop) :=
  {| frel_u:=frelFF_u; funct_u:=functFF_u |}.

Definition singleFct {A:Type} (a:A): forall (x y:A), (fun t=>t=a) x->(fun t=>t=a) y->x=y.
Proof.
  intros x y H K. rewrite <- K in H. apply H.
Qed. 
Ltac packPrPo :=
  intros [f1 frel1 f_frel1 funct1] [f2 frel2 f_frel2 funct2] eq;
  unfold frelBB in *; unfold functBB in *;
  unfold frelBF in *; unfold functBF in *;
  unfold frelFB in *; unfold functFB in *;
  unfold frelFF in *; unfold functFF in *;
  (* use inversion to show that the relations agree *)
  let H := fresh "H" in
  inversion eq as [H]; revert H; intros ->;
  (* use proof irrelevance to show that the functionhood lemmas agree *)
  replace funct1 with funct2 in * by (apply proof_irrelevance);
  enough (H:f1 = f2) by (revert H; intros ->; 
    replace f_frel1 with f_frel2 by (apply proof_irrelevance); reflexivity);
  let x := fresh "x" in
  apply functional_extensionality_dep; intro x;
  specialize (f_frel1 x); specialize (f_frel2 x);
  (* use the projection proof irrelevance property in the goal and cleanup*)
  match type of f1 with
  | forall _, { v:?B|_} => idtac "f1 returns a subset type"; 
    apply refinement_proj.(po);
    unfold proj; unfold refinement_proj;
    first [
      specialize (f_frel1 (fun a=>a=⌊ x ⌋) (singleFct ⌊ x ⌋) ⌊ f1 x ⌋ (fun b=>b=⌊ f1 x ⌋) (singleFct ⌊ f1 x ⌋) eq_refl eq_refl);
      specialize (f_frel2 (fun a=>a=⌊ x ⌋) (singleFct ⌊ x ⌋) ⌊ f1 x ⌋ (fun b=>b=⌊ f1 x ⌋) (singleFct ⌊ f1 x ⌋) eq_refl eq_refl)
    | let tp:= type of f_frel1 in idtac tp;
      specialize (f_frel1 ⌊ f1 x ⌋ (fun b=>b=⌊ f1 x ⌋) (singleFct ⌊ f1 x ⌋) (ltac:(reflexivity)));
      specialize (f_frel2 ⌊ f1 x ⌋ (fun b=>b=⌊ f1 x ⌋) (singleFct ⌊ f1 x ⌋) (ltac:(reflexivity)))
    ]
  | forall (a: ?x1Tp), Pack ?X (?X' a) (?prX a) ?Y (?Y' a) (?prY a) ?Xr ?Yr =>
    match goal with
    | [pr_po: forall (a: ?x1Tp), packPrPo |- _] => 
      specialize (pr_po x);
      unfold packPrPo in pr_po;
      match goal with
      | |- ?s = ?t => refine (pr_po s t _)
      end;
      unfold proj in *; unfold refinement_proj;
      (*case PackBF vs case PackFF *)
      first [ specialize (f_frel1 (fun a=>a=⌊ x ⌋) (singleFct ⌊ x ⌋) (packPr (f1 x))); 
              specialize (f_frel2 (fun a=>a=⌊ x ⌋) (singleFct ⌊ x ⌋) (packPr (f1 x))) |
              specialize (f_frel1 (packPr (f1 x))); 
              specialize (f_frel2 (packPr (f1 x))) |
            let tp:= type of f_frel1 in idtac tp;fail]
    end
  end; 
  match type of f_frel1 with
  | forall (b_rel: forall (b:?B), Prop), _ =>
    specialize (f_frel1 (fun b=>True));
    specialize (f_frel2 (fun b=>True))
  | _ => idtac
  end;
  repeat (match type of f_frel1 with
  | ?P -> _ =>
    specialize (f_frel1 (ltac:(quicksolve)));
    specialize (f_frel2 (ltac:(quicksolve)))
  end);
  rewrite <- f_frel1 in f_frel2;
  apply (eq_sym ((pr2 f_frel2) eq_refl)).

#[global] Instance packPrBB (A:Type) (p:A->Prop) (B:Type) (q:forall (x:{v:A|p v}), B->Prop): 
  (PackBB A p B q) ⤖ (uPackBB A B).
Proof.
  refine {|proj:=fun pack => {|frelBB_u:=frelBB; functBB_u:=functBB|}; |}.
  packPrPo.
Defined.

#[global] Instance packPrBF {A:Type} {p:A->Prop} {X Y:Type} 
  {X': forall (a:{v:A|p v}), Type} {prX: forall (a:{v:A|p v}), (X' a) ⤖ X} 
  {Y': forall (a:{v:A|p v}) (x:X' a), Type} {prY: forall (a:{v:A|p v}) (x:X' a), (Y' a x) ⤖ Y}
  {Xr: Type} {Yr:Type}  
  {prB_po: forall (a:{v:A|p v}), @packPrPo X (X' a) (prX a) Y (Y' a) (prY a) Xr Yr}:
  (PackBF A p X Y X' prX Y' prY Xr Yr prB_po) ⤖ (uPackBF A X Y Xr Yr).
Proof.
  refine {|proj:=fun pack => {|frelBF_u:=frelBF; functBF_u:=functBF|}; |}.
  packPrPo.
Defined.

#[global] Instance packPrFB {X: Type} {X': Type} {prX: X' ⤖ X} {Y:Type} {Y': forall (x:X'), Type} 
  {prY: forall (x:X'), (Y' x) ⤖ Y} {Xr: Type} {Yr:Type} 
  {prA_po: @packPrPo X X' prX Y Y' prY Xr Yr}
  {B:Type} {p:forall (x:(@Pack X X' prX Y Y' prY Xr Yr)), B->Prop}:
  (@PackFB X X' prX Y Y' prY Xr Yr prA_po B p) ⤖ (uPackFB X Y Xr Yr B).
Proof.
  unshelve refine {|proj:=fun pack => {|frelFB_u:=pack.(frelFB); functFB_u:=pack.(functFB)|}; po:=_|}.
  packPrPo.
Defined.

#[global] Instance packPrFF {X: Type} {X': Type} {prX: X' ⤖ X} {Y:Type} {Y': forall (x:X'), Type} 
  {prY: forall (x:X'), (Y' x) ⤖ Y} {Xr: Type} {Yr:Type} 
  {pr1_po: @packPrPo X X' prX Y Y' prY Xr Yr}
  {A:Type} {A': forall (x:(@Pack X X' prX Y Y' prY Xr Yr)), Type}
  {prA:forall (x:(@Pack X X' prX Y Y' prY Xr Yr)), (A' x) ⤖ A}
  {B:Type} {B':forall (x:(@Pack X X' prX Y Y' prY Xr Yr)) (a:A' x), Type}
  {prB:forall (x:(@Pack X X' prX Y Y' prY Xr Yr)) (a:A' x),(B' x a) ⤖ B}
  {Ar Br: Type}
  {pr2_po:forall (x:(@Pack X X' prX Y Y' prY Xr Yr)), 
    @packPrPo A (A' x) (prA x) B (B' x) (prB x) Ar Br}:
  (@PackFF X X' prX Y Y' prY Xr Yr pr1_po A A' prA B B' prB Ar Br pr2_po) ⤖ (uPackFF X Y Xr Yr A B Ar Br).
Proof.
  refine {|proj:=fun pack => {|frelFF_u:=pack.(frelFF); functFF_u:=functFF|}; po:=_|}.
  packPrPo.
Defined.

Definition singletonPred {A:Type}: Type := {p:A->Prop|forall (x y:A), p x -> p y -> x = y}.

Inductive get_relBB {A:Type} {p:A->Prop} {B:Type} {q:forall (x:{v:A|p v}), B->Prop}
  (f: forall (x:{v:A|p v}), {v:B|q x v}): (A->Prop) -> (B->Prop) -> Prop :=
	Get_relBB (x_rel:A->Prop) (x_rel_funct: forall (x1 x2:A), x_rel x1 -> x_rel x2 -> x1 = x2) 
    (y_rel:B->Prop) (y_rel_funct: forall v v', y_rel v -> y_rel v' -> v = v') 
     (x:{v:A|p v}) (y:B): x_rel ⌊ x ⌋ -> y_rel y ->
    ⌊ f x ⌋ = y -> get_relBB f x_rel y_rel.

Inductive get_relBF {A p X Y X' prX Y' prY Xr Yr} 
  (f:forall (a:{v:A|p v}), @Pack X (X' a) (prX a) Y (Y' a) (prY a) Xr Yr): 
  (A->Prop) -> (Xr->Yr->Prop) -> Prop :=
  Get_relBF (x_rel:A->Prop) (x_rel_funct: forall (x1 x2:A), x_rel x1 -> x_rel x2 -> x1 = x2) 
     (x:{v:A|p v}) (y:uPack X Y Xr Yr):
    x_rel ⌊ x ⌋ -> packPr (f x) = y -> get_relBF f x_rel y.(frel_u).

Inductive get_relFB {X: Type} {X': Type} {prX: X' ⤖ X} {Y:Type} {Y': forall (x:X'), Type} 
  {prY: forall (x:X'), (Y' x) ⤖ Y} {Xr: Type} {Yr:Type} 
  {prA: (@Pack X X' prX Y Y' prY Xr Yr) ⤖ (@uPack X Y Xr Yr)}
  {B:Type} {p:forall (x:(@Pack X X' prX Y Y' prY Xr Yr)), B->Prop}
  (f:forall (a:(@Pack X X' prX Y Y' prY Xr Yr)), {v:B|p a v}):
  (Xr->Yr->Prop)->(B->Prop)->Prop :=
  Get_relFB (x:@Pack X X' prX Y Y' prY Xr Yr) (y_rel:B->Prop) 
    (y_rel_funct: forall v v', y_rel v -> y_rel v' -> v = v') (y:B): y_rel y->
    ⌊ f x ⌋ = y -> get_relFB f (x.(frel)) y_rel.

Inductive get_relFF {X: Type} {X': Type} {prX: X' ⤖ X} {Y:Type} {Y': forall (x:X'), Type} 
  {prY: forall (x:X'), (Y' x) ⤖ Y} {Xr: Type} {Yr:Type} 
  {pr1: (@Pack X X' prX Y Y' prY Xr Yr) ⤖ (@uPack X Y Xr Yr)}
  {A:Type} {A': forall (x:(@Pack X X' prX Y Y' prY Xr Yr)), Type}
  {prA:forall (x:(@Pack X X' prX Y Y' prY Xr Yr)), (A' x) ⤖ A}
  {B:Type} {B':forall (x:(@Pack X X' prX Y Y' prY Xr Yr)) (a:A' x), Type}
  {prB:forall (x:(@Pack X X' prX Y Y' prY Xr Yr)) (a:A' x), (B' x a) ⤖ B}
  {Ar Br: Type}
  {pr2:forall (x:(@Pack X X' prX Y Y' prY Xr Yr)), 
    (@Pack A (A' x) (prA x) B (B' x) (prB x) Ar Br) ⤖ (@uPack A B Ar Br)} 
  (f: forall (x:(@Pack X X' prX Y Y' prY Xr Yr)), 
    (@Pack A (A' x) (prA x) B (B' x) (prB x) Ar Br)):
  (Xr->Yr->Prop)->(Ar->Br->Prop)->Prop :=
  Get_relFF (x:@Pack X X' prX Y Y' prY Xr Yr) (y:uPack A B Ar Br):
    packPr (f x) = y -> get_relFF f (x.(frel)) (y.(frel_u)).

Definition mkPackBB {A:Type} {p:A->Prop} {B:Type} {q:forall (x:{v:A|p v}), B->Prop}
  (f: forall (x:{v:A|p v}), {v:B|q x v}): 
  @PackBB A p B q.
Proof.
  refine ({| fBB := f; frelBB := get_relBB f |}).
  - intros a' a_rel a_rel_fct b b_rel b_rel_fct H K.
    split. 
    + intros <-. Check Get_relBB.
      refine (Get_relBB f a_rel a_rel_fct b_rel b_rel_fct _ _ H K _). reflexivity.
    + inversion 1. 
      revert H4; intros ->.
      revert H5; intros ->. clear x_rel_funct y_rel_funct.
      pose proof (a_rel_fct _ _ H H1) as L.
      pose proof (b_rel_fct _ _ K H2) as L2.
      revert L2; intros ->.
      rewrite <- H3.
      destruct a' as [a a_p], x as [x x_p]; simpl in *.
      revert L; intros ->.
      now replace a_p with x_p by (apply proof_irrelevance).
  - intros.
    now apply b_rel_funct. 
Defined.


Definition mkPackBF {A:Type} {p:A->Prop} {X Y:Type} 
  {X': forall (a:{v:A|p v}), Type} {prX: forall (a:{v:A|p v}), (X' a) ⤖ X} 
  {Y': forall (a:{v:A|p v}) (x:X' a), Type} {prY: forall (a:{v:A|p v}) (x:X' a), (Y' a x) ⤖ Y}
  {Xr: Type} {Yr:Type}  
  {prB_po: forall (a:{v:A|p v}), @packPrPo X (X' a) (prX a) Y (Y' a) (prY a) Xr Yr}
  (f: forall (a:{v:A|p v}), @Pack X (X' a) (prX a) Y (Y' a) (prY a) Xr Yr): 
  @PackBF A p X Y X' prX Y' prY Xr Yr prB_po.
Proof.
  refine ({| fBF := f; frelBF := get_relBF f |}).
  - intros a a_rel a_rel_funct y H. unfold proj. 
    split. 
    + intros K. apply (Get_relBF f a_rel a_rel_funct a y H K). 
    + inversion 1. 
      revert H3; intros ->. 
      destruct y as [y_frel ? y_funct]. destruct y0 as [y0_frel ? y0_funct]; simpl in *.
      revert H1; intros ->.
      unfold frel_u in *; simpl in *.
      pose proof (a_rel_funct _ _ H H2) as K.
      apply (refinement_proj.(po)) in K.
      revert K; intros ->. 
      rewrite H4.
      enough (K: functionhoodTp_u1=functionhoodTp_u0) by (revert K; intros ->; 
        now replace y_funct with y0_funct by (apply proof_irrelevance)).
      (* now this is comp[letely impossible to prove, we are stuck here *)
      admit.
.

(*Inductive get_relS {X: Type} {X': Type} {prX: X' ⤖ X} {T:Type} {p: forall (a:X'), T -> Prop}
	(f: forall (x:X'), {v:T|p x v}): X -> T -> Prop :=
	Get_rel (x: X) (v:T) (xp:{x':X' | prX.(proj) x' = x}): ⌊ f ⌊xp⌋ ⌋ = v -> get_relS f x v.

Definition get_relF {X: Type} {X': Type} {prX: X' ⤖ X} {Y:Type} {Y': forall (x:X'), Type} {prY: forall (x:X'), (Y' x) ⤖ Y}
  (f: forall (x:X'), Y' x) (x: X) (xp:{x':X' | prX.(proj) x' = x}): Y := (prY ⌊xp⌋).(proj) (f ⌊xp⌋ ).

Ltac get_rel_rel := intros; 
  split; intros H;
  [unshelve econstructor; try (refine (exist _ _ eq_refl); assumption); simpl; assumption|
  strong_inversion H; simpl in *; repeat cleanup_hints; simpl in *; repeat projPO; easy].

Lemma get_rel_relS {X: Type} {X': Type} {prX: X' ⤖ X} {T:Type} {p: forall (a:X'), T -> Prop} f:
	forall (x:X') (v:T), ⌊ f x ⌋ = v <-> @get_relS X X' prX T p f (prX.(proj) x) v.
Proof.
  get_rel_rel.
Qed.

Ltac get_rel_funct :=
  intros; 
  repeat match goal with
  | [h:_ _ _ _ |- _] => strong_inversion h
  end;
  repeat cleanup_hints; simpl in *; subst;
  repeat projPO; reflexivity.

Lemma get_rel_funct {X: Type} {X': Type} {prX: X' ⤖ X} {T:Type} {p: forall (a:X'), T -> Prop} f (x:X) (v v':T):
	@get_relS X X' prX T p f x v -> @get_relS X X' prX T p f x v' -> v = v'.
Proof.
  get_rel_funct.
Qed.
Definition mkPackS {X: Type} {X': Type} {prX: X' ⤖ X} {T:Type} {p: forall (a:X'), T -> Prop} 
  (f: forall (x:X'), {v:T|p x v}) : @Pack X X' prX T (fun x => {v:T| p x v}) (fun x => refinement_proj) (X -> T -> Prop).
Proof.
  refine ({| f_def := f; f_rel := get_relS f; 
              f__f_rel := get_rel_relS f; f_funct := get_rel_funct f |}).
Defined.

Definition projPackS {X: Type} {X': Type} {prX: X' ⤖ X} {T:Type} {p: forall (a:X'), T -> Prop}
  (pack: @Pack X X' prX T (fun x => {v:T| p x v}) (fun x => refinement_proj) (X -> T -> Prop)) := {| f_funct_uTp:=pack.(f_funcTp); f_rel_u := pack.(f_rel); f_funct_u := pack.(f_funct) |}.
#[global] Hint Unfold projPackS:get_rel_db.
Ltac pack_eq_lem :=
  intros xd yd xr yr xl xf yl yf; intros -> ->;
  assert (xl = yl) as Hl by (apply proof_irrelevance);
  assert (xf = yf) as Hf by (apply proof_irrelevance);
  rewrite Hl; rewrite Hf; reflexivity.

Lemma packEqLem {X: Type} {X': Type} {prX: X' ⤖ X} {T:Type} {p: forall (a:X'), T -> Prop}:
  forall (xd yd: forall (x:X'), {v:T|p x v}) (xr yr: X -> T -> Prop) 
(xl : forall (x: X') (v : T), ⌊ xd x ⌋ = v <-> xr (proj x) v)
(xf : forall (x : X) (v v': T), xr x v -> xr x v' -> v = v')
(yl : forall (x: X') (v : T), ⌊ yd x ⌋ = v <-> yr (proj x) v)
(yf : forall (x : X) (v v': T), yr x v -> yr x v' -> v = v'), 
xd = yd -> xr = yr ->
{| f_def := xd; f_rel := xr; f__f_rel := xl; f_funct := xf |} =
{| f_def := yd; f_rel := yr; f__f_rel := yl; f_funct := yf |}.
Proof.
  pack_eq_lem.
Qed.
#[global] Hint Resolve packEqLem:get_rel_db.
Ltac pack_po :=
  intros [xd xr xl xf] [yd yr yl yf]; autounfold with get_rel_db;
  simpl in *; intros H0;
  assert (xr = yr) as H by (now injection H0); revert H; intros ->;
  assert (xd = yd) as Hd by (repeat (apply functional_extensionality_dep; intro); projPO;
    rewrite xl; now apply yl);
  revert Hd; intros ->;
  auto with get_rel_db.
Lemma packPo {X: Type} {X': Type} {prX: X' ⤖ X} {T:Type} {p: forall (a:X'), T -> Prop}: 
  forall (x y:(@Pack X X' prX T (fun x=>{v:T|p x v}) (fun x=>refinement_proj) (X -> T -> Prop))), projPackS x = projPackS y -> x = y.
Proof.
  pack_po.
Qed.
  
#[global] Instance packPr {X: Type} {X': Type} {prX: X' ⤖ X} {T:Type} {p: forall (a:X'), T -> Prop}: 
  (@Pack X X' prX T p) ⤖ (@uPack X T) := { 
	proj := projPack;
  po := ltac:(apply packPo)
}.
Definition packProj {X: Type} {X': Type} (prX: X' ⤖ X) {T:Type} (p: forall (a:X'), T -> Prop) :=
  @packPr X X' prX T p.
#[global] Hint Unfold packProj:core_db.
Definition mkUPack {X: Type} {X': Type} {prX: X' ⤖ X} {T:Type} {p: forall (a:X'), T -> Prop}
  (f: forall (x:X'), {v:T|p x v}) : @uPack X T.
Proof.
  refine ({| f_rel_u := get_rel f; 
             f_funct_u := get_rel_funct f |}).
Defined.

(* a generalized subsumption cast for Packs *)
#[global] Instance SubPack {X: Type} {T:Type}
  {X': Type} {prX: X' ⤖ X} {p: forall (a:X'), T -> Prop}
  {Y': Type} {prY: Y' ⤖ X} {q: forall (y:Y'), T -> Prop}
  (f: @Pack X X' prX T p) (castX: forall (x:Y'), X' ↼ x)
  (castT: forall (x:Y'), {v:T | q x v} ↼ (f.(f_def) (castX x).(genSubCast))):
  @GeneralizedSubsumptionCast (@uPack X T) (@Pack X X' prX T p) (@Pack X Y' prY T q) packPr (packProj prY q) f.
Proof.
  unshelve refine {| genSubCast := _; cast_pr := _ |}.
  - destruct f as [f rel f__frel funct].
    unfold f_def in *.
    unfold genSubCast in *.
    unshelve refine {| f_def := _; f_rel := rel; f__f_rel := _; f_funct := funct |}.
     -- intros x. apply (castT x).(genSubCast).
     -- intros x v. 
        repeat (match goal with
        | [pr: ?X' ⤖ ?X |- _] => idtac pr; destruct pr as [pr ?]
        end).
        specialize (f__frel (castX x).(genSubCast) v).
        unfold proj in *; unfold genSubCast in *.
        repeat (match goal with
        | [cast:forall (x:?xTp), @GeneralizedSubsumptionCast _ _ ?X' {| proj := ?pr; po := ?pr_po |} {| proj := ?pr2; po := ?pr2_po |} _ |- _] => 
          let cast_pr := fresh "cast_pr_" in
          let temp := fresh "temp" in
          match goal with
          | [y: xTp |- _] => 
            tryif (
            match goal with
            | [h: pr2 _ = pr y |- _] => idtac
            end
            ) then (fail) else (idtac);
            pose (cast y) as temp;
            let cprTp := type of temp in
            match cprTp with
            | @GeneralizedSubsumptionCast ?A ?A' X' {| proj := pr; po := pr_po |} {| proj := pr2; po := pr2_po |} ?tm => idtac A A' X' pr pr2 tm;
              assert (pr2 temp.(genSubCast) = pr tm) as cast_pr by (now destruct temp);
              subst temp; unfold genSubCast in cast_pr; try rewrite <- cast_pr in *
            end
          end
        end).
        pose ((castT x).(cast_pr)) as castT_pr. unfold genSubCast in castT_pr; simpl in castT_pr.
        set (⌊ ⌊ castT x _⌋ ⌋) as tm in *. rewrite castT_pr. subst tm. 
        apply f__frel.
  - destruct f as [f rel rw funct]. simpl.
    unfold projPack. reflexivity.
Qed.*)