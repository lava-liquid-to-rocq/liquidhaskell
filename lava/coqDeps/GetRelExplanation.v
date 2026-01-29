Require Import Logic.FunctionalExtensionality.
Load TacticUtils.

(* Functions and their graph relations:
Given a function
f: A -> B
we need to define what its graph relation is.

As an example consider:
eqN : Nat -> (Nat -> bool)
eqN 0 0 = True
eqN (S n) (S m) = eqN n m
eqN _ _ = False

There are two approaches to defining the graph of eqN, depending on whether
we interpret it as a 2-ary function or as a (1-ary) function returning a function.

First approach; flattening function types:
For each n-ary function we define an n+1 ary relation.

Inductive eqN_rel: Nat -> Nat -> bool -> Prop :=
| eqN_rel_0: eqN_rel 0 0 true
| eqN_rel_s n m: eqN_rel n m -> eqN_rel

or for map:

map {A B} (f:A->B) (list A): list B
map f [] = []
map f (x:xs) = (f x):(map f xs)

map_rel {A B} (f_rel: A -> B -> Prop): list A -> list B -> Prop

The lemma connecting the graph map_rel with map is then:

map__map_rel: forall f f_rel (l:list A) (v:list B), 
  (forall x res, f x = res <-> f_rel x res) -> 
    (map f l = v <-> map_rel f_rel l v)


Second approach; nesting relations:
For each (1-ary) function, we create a binary relation.


map {A B} (f:A->B) (list A): list B

The relation _eqN_rel2_ for eqN becomes:
eqN_rel2: (Nat->Prop) -> (Nat->bool->Prop) -> Prop
eqN_rel2 n_rel2 r = (n_rel2 0 -> r 0 true) /\ 
    (forall n m, (n_rel2 n -> r m true) -> n_rel2 (S n) -> r (S m) true) /\
    (forall n, n_rel2 (S n) -> r 0 false) /\
    (forall m, n_rel2 0 -> r (S m) false).

The relation _map_rel2_ for map becomes:

map_rel2 {A B} (f_rel2: A -> B -> Prop): (list A -> list B -> Prop) -> Prop
map_rel2 frel2 r = r [] [] /\ forall x y, frel2 x y -> forall xs ys, r xs ys ->
                      r (x:xs) (y:ys)

With the correspondence lemmas:
eqN__eqN_rel2 (n_rel2:Nat->Prop) (r:Nat->bool->Prop)

map__map_rel2 (f:A->B) (f_rel2:A->B->Prop) (l:list A) (v:list B)
  (r:list A -> list B -> Prop):
    (forall x res, f x = res <-> f_rel2 x res) ->
      (r l v) ->
        (map f l = v <-> map_rel2 f_rel2 r)
*)

(** Refined functions and their graph relations *)
(* Given a function 
f: forall (x:X'), Y' x
we need to define what it means for relation
frel: X -> Y -> Prop
to be the graph relation of f.
Here X', Y' are refined types and there are projections
prX: X' -> X and prY: Y' -> Y out of those refinement types into unrefined types.
In Rocq with refinment types expressed as subset types, these projection will be just
proj1_sig, the projection returning the first component of a subset type.

Definition (functionhood):
We will say that frel is the graph of some function (it satisfies functionhood), 
if the following property holds for frel:
forall (x:X) (v v':Y), frel x v -> frel x v' -> v = v'

Definition (correspondence):
We will say frel is the graph of f if it satisfies the property:
forall (x:X') (v:Y): prY (f x) = v <-> frel (prX x) v

In the presence of a term x':X' with projection x, 
the functionhood of frel becomes a corrollary of the correspondence fo f and frel.
However, the functionhood of frel holds even for unrefined arguments not in the domain
of definition of a partil function f.

In order to be able to use unreflected functions (including local ones) in refinements,
we a way to define the graph relation for any function f. 
This is done as follows:

Inductive get_rel {X X': Type} {prX: X' -> X} {Y:Type} {Y': forall (x:X'), Type} 
	(f: forall (x:X'), Y' x): X -> Y -> Prop :=
	Get_rel (x: X) (v:Y) [x':X'] [xp:prX x' = x]: 
  prY (f x') = v -> get_rel f x v.

The definition states that the graph relation get_rel f holds on x and v, 
whenever there exists some x' of type X' whose projection is x and whose image
under f projects to v.
*)

(** Simplest case for function packs: 
    Function packs for first-order function arguments of arity 1 *)
(* In order to allow refined function to accept arguments of function types, 
   we introduce the notion of a function pack.

  A function pack is essentially a 4-tuple consisting of:
  1. the function f itself
  2. the graph relation frel for the function
  3. the correspondence lemma for f and frel
  4. the functionhood lemma for frel

  By passing function packs as arguments f to refined functions we ensure that
  subsequent argument and return types can use f inside of refinements, 
  even outside of their domains of definition (in case f is partial by using the
  graph relation of f instead.

  We therefore define a typeclass for simple first-order arity 1 function packs:
  
  Class Pack {X: Type} (X':Type) {prX: X' -> X} {Y: Type} (Y': forall (x:X'), Type) 
    {prY: forall (x:X'), (Y' x) -> Y}:= {
    f: forall (x:X'), Y' x;                               (* refined function *)
    frel: X -> Y -> Prop;                                 (* graph relation *)
    f_frel (x:X') (v:Y): prY (f x) = v <-> frel x v;      (* frel is graph of f *)
    funct (x:X) (v v':Y): frel x v -> frel x v' -> v = v' (* functionhood of frel *)
}.  

  If a function f: forall (g:forall (x:X'), Y' x), Z' g has a function pack as argument,
  then we need to also adapt the type in the graph relation of f accordingly.

  For this we introduce the unrefined function packs:

  Class UPack (X Y: Type) := {
    frel_u: X -> Y -> Prop;
    funct_u (x:X) (v v':Y): frel_u x v -> frel_u x v' -> v = v'
  }. 
  We can then use the UPack in those places where we need an unrefined argument.
  Crucially, the functionhood property in the UPack for g is necessary in the proof
  of the functionhood property for f.
*)

(** Packs for higher-order (but still arity 1) function arguments *)
(*
In order to allow higher-order function arguments we need to the types allowed in function packs.
So far we assumed that refined types (in the context of function packs) are 
subset types and unrefined types are basic types (i.e. not subset types and not function types). 
The projections from refined types to unrefined types are then just the projection
out of the subset type proj1_sig.

In order to allow higher-order function packs, we will additionally allow
other function packs as "refined types" and unrefined function packs as "unrefined types".
The projection operators from the refined to the unrefined types are then either
1. the projection out of a subset type
2. the projection that drop the function and correspondence from a Pack, 
   yielding the corresponding UPack

For technical reasons, we will also require the property that any two packs p, p' 
with the same projection up are in fact equal 
  (the refined function must be equal by correspondence and the 
  correspondence properties by proof irrelevance).
We thus create a class for "generalized projection" that must satisfy this property.

Class GeneralizedProjection {A A':Type} := {
  proj: A' -> A; (* the projection operator itself *)
  po: forall (x y:A'), proj x = proj y -> x = y (* "proof irrelevance" for the "refined" type w.r.t. proj *)
}.
Global Notation "A' ⤖ A" := (@GeneralizedProjection A A') (at level 1). 

And then we define an instance for this class for projections out of subset types
and for the projection from a Pack to its UPack.

Then besides generalising the notions of "refined types", "unrefined types" 
and projections (to "generalized projection"), we can leave our previous
definition virtually unchanged.
This means that the arrows -> in the projections in  the definition of Packs 
above become ⤖ instead (and that's basically the only change)
*)

(** Nesting higher-order arity 1 packs in the codomain *)
(* 
If we allow packs to occur as "refined types" in the codomain of a function pack
we can express higher arity functions with packs (of arity 1) as well using "currying":
f: A' -> B' -> C'
can be rewritten as
f: A' -> (B' -> C')
which be represented as a nested pack 
(keeping the unrefined types and generalized projection as implicit arguments):

Pack A' (Pack B' C')

relation:
A -> R 

However, this causes complications for the relation in the pack.
Let A, B, C denote the unrefined types for A', B', C'.
In order for the relation to still be a relation, we replace it's type with:
A -> R, 
where R is a type variable whose value is the type of the relation 
in the Pack B' C'.
If C' is not a pack itself, that means that R=B -> C -> Prop.

Since the relation is now really a function returning a relation, we need to 
also modify the functionhood and correspondence properties.
Since for non-nested packs the relation will still have the usual type, the
claims of the functionhood and correspondence properties will need to become
type variables as well.
The same also applies to the unrefined function packs.

Overall, we end up with the following axiomatization: *)

(*** Typeclass for functions *)

(* A class _GPack_ for possibly nested function packs.
  We will later define two more classes, one class _PackS_ for packs whose codomain
  is not a pack (but an ordinary subset type) and one class _PackF_ whose codomain is.
  This is used to type the codomain in the latter.
  Then we declare instances for _GPack_ for both types of packs and introduce
  the type _Pack_ of packs of either type.
 *)

Class GPack (X:Type) (X': Type) (prX: X' ⤖ X) (Y: Type) 
(Y': forall (x:X'), Type) (prY: forall (x:X'), (Y' x) ⤖ Y) (Yr: Type):= {
  f: forall (x:X'), Y' x;                                     (* refined function *)
  grF: X -> Yr;                                               (* graph relation *)
  relApType (x:X') (v:Y): Prop;
  f_rel (x:X') (v:Y): (prY x).(proj) (f x) = v <-> relApType x v; (* grF is graph of f *)
  functTp (x:X) (v v':Y): Prop; (* rel x v -> relS x v' -> v = v' *)
  funct (x:X) (v v':Y): functTp x v v'                        (* functionhood of grF *)
}.
Set Printing Universes.
Print GPack.

Class PackS (X: Type) (X': Type) (prX: X' ⤖ X) (Y:Type) (p: forall (x:X'), Y -> Prop) : Type:= {
	fS : forall (x:X'), {v:Y|p x v};                            (* the refined function *)
	relS : X -> Y -> Prop;                                      (* the graph relation *)
	f_relS (x:X') (v:Y): 
    ⌊ fS x ⌋ = v <-> relS (prX.(proj) x) v;                   (* relS is graph of fS *)
	functS (x:X) (v v':Y): relS x v -> relS x v' -> v = v'      (* functionhood of relS *)
}.

Class uPackS {X Y : Type} := {
	f_rel_uS : X -> Y -> Prop;                                  (* the graph relation *)
	f_funct_uS (x:X) (v v':Y): 
    f_rel_uS x v -> f_rel_uS x v' -> v = v'                   (* functionhood of f_rel_u *)
}.

Class uPackF {X Y R: Type} := {
	f_rel_uF : X -> R;                                          (* the graph relation *)
	f_funct_uF (x:X) (v v':R): 
    f_rel_uF x = v -> f_rel_uF x = v' -> v = v'               (* functionhood of f_rel_u *)
}. 

(* We have a problem here: we want to make the Y into a type argument, just like X, but doing so
  will cause issues trying to rewrite Y as part of pattern matches (destruct tactic) later in packPr.
  However, quantifying over it in the constructors will cause universe inconsistency issues in
  packPr. *)
Inductive uPack (X:Type): forall (Y:Type), Type :=
  | UPackF {Y R: Type}: @uPackF X Y R -> uPack X Y
  | UPackS {Y:Type}: @uPackS X Y -> uPack X Y.
Print uPack.

#[global] Instance extrRelRec {X A B R:Type} (rpY: uPack A B ⤖ R): (@uPackF X (uPack A B) (A -> R)) ⤖ (X -> A -> R) := { 
	proj := (fun upack => upack.(f_rel_uF));
  po := ltac:(destruct x as [x xp], y as [y yp]; simpl in *; intros ->; f_equal; apply proof_irrelevance);
}.

(* TODO: what if B is a uPack? *)
#[global] Instance extrRel {A B:Type}: @GeneralizedProjection (A -> B -> Prop) (@uPackS A B) := { 
	proj := (fun upack => upack.(f_rel_uS));
  po := ltac:(destruct x as [x xp], y as [y yp]; simpl in *; intros ->; f_equal; apply proof_irrelevance);
}.

Class PackF (X: Type) (X': Type) (prX: X' ⤖ X) {A A' prA B B' prB Yr} (extractRel: (uPack A B) ⤖ (A -> Yr)) (*(Y': forall (x:X'), @Pack A A' prA B (B' x) (prB x))*)
  (*(Y:Type) (Y': forall (x:X'), Type) (prY: forall (x:X'), (Y' x) ⤖ Y) {Yr:Type} {extractRel: Y ⤖ Yr}*) 
    (prY: forall (x:X'), (@GPack A A' prA B (B' x) (prB x) Yr) ⤖ (uPack A B)):= {
	fF (x:X'): @GPack A A' prA B (B' x) (prB x) Yr;              (* The refined function *)
	relF : X -> A -> Yr;                                        (* the graph relation *)
	f_relF (x:X') (v: uPack A B): (prY x).(proj) (fF x) = v <-> 
                  relF (prX.(proj) x) = extractRel.(proj) v   (* relP is graph of fF *)
                                                              (* since relP is function, functionhood is trivial *)
}.


#[global] Instance packS {X: Type} {X': Type} {prX: X' ⤖ X} {T:Type} {p: forall (x:X'), T -> Prop}
  (pack:@PackS X X' prX T p): 
@GPack X X' prX T (fun x => {v:T|p x v}) (fun x => @refinement_proj T (p x)) (T->Prop) := {
  f:=pack.(fS); grF:=pack.(relS);
  relApType:=fun x v => (pack.(relS) (prX.(proj) x) v);
  f_rel:=pack.(f_relS);
  functTp:=fun (x:X) (v v':T) => (pack.(relS) x v -> pack.(relS) x v' -> v = v');
  funct:=pack.(functS)
}. 

#[global] Instance packF {X: Type} {X': Type} {prX: X' ⤖ X} {A A' prA B B' prB Yr} {extractRel: (@uPack A B) ⤖ (A -> Yr)}
    {prY: forall (x:X'), (@GPack A A' prA B (B' x) (prB x) Yr) ⤖ (@uPack A B)} (pack:PackF X X' prX extractRel prY):
  @GPack X X' prX (@uPack A B) (fun x =>@GPack A A' prA B (B' x) (prB x) Yr) prY (A -> Yr) := {|
    f:=pack.(fF); grF:=pack.(relF);
    relApType:=fun x v => relF (prX.(proj) x) = extractRel.(proj) v;
    f_rel:=pack.(f_relF);
    functTp:=fun (x:X) (v v':@uPack A B) => pack.(relF) x = extractRel.(proj) v -> pack.(relF) x = extractRel.(proj) v' -> v = v';
    funct:=fun x v v' H K => (extractRel.(po) v v' (eq_sym (eq_stepl H K)))|}.

(* One desperate idea: Define one constructor for each arity below *)
Inductive get_relS {X: Type} {X': Type} {prX: X' ⤖ X} {T:Type} {p: forall (a:X'), T -> Prop}
	(f: forall (x:X'), {v:T|p x v}): X -> T -> Prop :=
	Get_rel (x: X) (v:T) (xp:{x':X' | prX.(proj) x' = x}): ⌊ f ⌊xp⌋ ⌋ = v -> get_relS f x v.

(*Inductive get_relF {X: Type} {X': Type} {prX: X' ⤖ X} {A A' prA B B' prB Yr} {extractRel: (@uPack A B) ⤖ (A -> Yr)}
    {prY: forall (x:X'), (Pack A A' prA B (prB x) (A -> Yr)) ⤖ (@uPack A B)} 
    (f: forall (x:X'), @Pack A A' prA B B' (prB x) (A -> Yr)): X -> A -> Type :=
  Get_relF (x: X) (a:A) [xp:{x':X' | prX.(proj) x' = x}]:
    extractRel.(proj) ((prY ⌊xp⌋).(proj) (f ⌊xp⌋)) a.*)

(*Definition gPack_exhaustive_spec (X:Type) (X': Type) (prX: X' ⤖ X)
    [PackType: Type] (pack:PackType): Type.
Proof.
  refine (exists (Y: Type) {Y': forall (x:X'), Type} (prY: forall (x:X'), (Y' x) ⤖ Y) (Yr: Type) 
    [teq: PackType=@GPack X X' prX Y Y' prY Yr] (gpack:PackType), 
      gpack=pack <-> _ /\ _).
  - refine (exists {p:forall (x:X'), Y -> Prop} 
      [teq':PackType=GPack X X' prX Y (fun x : X' => refinement_proj) (Y -> Prop)] 
      {inst: @PackS X X' prX Y p}, _=gpack).
    rewrite teq'.
    exact (packS inst).
  - refine (exists {A A' prA B B' prB Yr} 
    (extractRel: (uPack A B) ⤖ (A -> Yr)) 
    (prY: forall (x:X'), (@GPack A A' prA B (B' x) (prB x) Yr) ⤖ (uPack A B))
    [teq':PackType=GPack X X' prX (uPack A B) prY (A -> Yr)]
    {inst: PackF X X' prX extractRel prY}, _=gpack). 
    rewrite teq'.
    exact (packF inst).
Defined.
Print gPack_exhaustive_spec.
Axiom gPack_exhaustive: forall (X:Type) (X': Type) (prX: X' ⤖ X) [PackType: Type]
  (pack:PackType), gPack_exhaustive_spec X X' prX pack.*)

Inductive Pack (X:Type) (X': Type) (prX: X' ⤖ X): forall {Y: Type} {Y': forall (x:X'), Type} (prY: forall (x:X'), (Y' x) ⤖ Y) (Yr: Type), Type :=
  | PackS' (Y: Type) {p: forall (x:X'), Y -> Prop} 
    (pack:@PackS X X' prX Y p): 
    @Pack X X' prX Y (fun x => {v:Y|p x v}) (fun x => @refinement_proj Y (p x)) (Y -> Prop)
  | PackF' {A A' prA B B' prB Yr} {extractRel: (@uPack A B) ⤖ (A -> Yr)}
    {prY: forall (x:X'), (@GPack A A' prA B (B' x) (prB x) Yr) ⤖ (@uPack A B)} 
    (pack:PackF X X' prX extractRel prY): 
      @Pack X X' prX (@uPack A B) (fun x => (@GPack A A' prA B (B' x) (prB x) Yr)) prY (A -> Yr). 
Print Pack.

#[global] Instance pack {X: Type} {X': Type} {prX: X' ⤖ X} {Y: Type} {Y': forall (x:X'), Type} {prY: forall (x:X'), (Y' x) ⤖ Y} {Yr: Type}
  (pack: @Pack X X' prX Y Y' prY Yr): @GPack X X' prX Y Y' prY Yr.
Proof.
  induction pack.
  - destruct pack as [f rel f_rel funct].
    unshelve refine {| f:=f; grF:=rel; relApType:=fun (x:X') (v:Y) => _;
      f_rel:=f_rel; functTp:=_; funct:=funct |}.
  - destruct pack as [f rel f_rel].
    unshelve refine {| f:=f; grF:=rel; f_rel:=f_rel;
       relApType:=fun x v=>rel (prX.(proj) x) = extractRel.(proj) v|}.
    -- intros x v v'. exact (rel x = extractRel.(proj) v -> rel x = extractRel.(proj) v' -> v = v'). 
    -- simpl. intros x v v' -> H. 
       exact (extractRel.(po) v v' H).
Defined.

Definition get_relF {X: Type} {X': Type} {prX: X' ⤖ X} {A A' prA B B' prB Yr} {extractRel: (@uPack A B) ⤖ (A -> Yr)}
    {prY: forall (x:X'), (Pack A A' prA (prB x) (A -> Yr)) ⤖ (@uPack A B)} 
    (f: forall (x:X'), @Pack A A' prA B B' (prB x) (A -> Yr)) (x:X) (a:A)
    {xp:{x':X' | prX.(proj) x' = x} }: Yr.
Proof.
  refine (extractRel.(proj) ((prY ⌊xp⌋).(proj) (f ⌊xp⌋)) a).
Defined.


(* Higherorder stuff *)
Ltac projPO :=
  match goal with
  | [h: ?inst.(proj) _ = ?inst.(proj) _ |- _] => apply inst.(po) in h; 
    first [rewrite h in * | revert h; intros ->]
  | [inst: @GeneralizedProjection ?T ?T' |- ?x' = ?y'] => 
    let xpTp := type of x' in
    eq_fail xpTp T';
    apply inst.(po)
  | [inst: forall (x1:_), @GeneralizedProjection ?T (?T' x1) |- ?x' ?x1 = ?y' ?x1] => 
    let xpTp := type of (x' x1) in
    eq_fail xpTp (T' x1);
    apply (inst x1).(po)
  | [inst: forall (x1:_) (x2:_), @GeneralizedProjection ?T (?T' x1 x2) |- ?x' ?x1 ?x2 = ?y' ?x1 ?x2] => 
    let xpTp := type of (x' x1 x2) in
    eq_fail xpTp (T' x1 x2);
    apply (inst x1 x2).(po)
  | [inst: forall (x1:_) (x2:_) (x3:_), @GeneralizedProjection ?T (?T' x1 x2 x3) |- ?x' ?x1 ?x2 ?x3 = ?y' ?x1 ?x2 ?x3] => 
    let xpTp := type of (x' x1 x2 x3) in
    eq_fail xpTp (T' x1 x2 x3);
    apply (inst x1 x2 x3).(po)
  | |- ?f ?x1 ?x2 ?x3 ?x4 ?x5 = _ =>
    let tp := type of (f x1 x2 x3 x4 x5) in
    match tp with
    | {v: ?T | ?p x1 x2 x3 x4 x5 v} => apply (@refinement_proj T (p x1 x2 x3 x4 x5)).(po); simpl
    end
  | |- ?f ?x1 ?x2 ?x3 ?x4 = _ =>
    let tp := type of (f x1 x2 x3 x4) in
    match tp with
    | {v: ?T | ?p x1 x2 x3 x4 v} => apply (@refinement_proj T (p x1 x2 x3 x4)).(po); simpl
    end
  | |- ?f ?x1 ?x2 ?x3 = _ =>
    let tp := type of (f x1 x2 x3) in
    match tp with
    | {v: ?T | ?p x1 x2 x3 v} => apply (@refinement_proj T (p x1 x2 x3)).(po); simpl
    end
  | |- ?f ?x1 ?x2 = _ =>
    let tp := type of (f x1 x2) in
    match tp with
    | {v: ?T | ?p x1 x2 v} => apply (@refinement_proj T (p x1 x2)).(po); simpl
    end
  | |- ?f ?x = _ =>
    let tp := type of (f x) in
    match tp with
    | {v: ?T | ?p x v} => apply (@refinement_proj T (p x)).(po); simpl
    end
  end.

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
  (f: forall (x:X'), {v:T|p x v}) : @GPack X X' prX T (fun x => {v:T| p x v}) (fun x => refinement_proj) (T -> Prop).
Proof.
  refine ({| f := f; grF := get_relS f; 
             f_rel := get_rel_relS f; funct := get_rel_funct f |}).
Defined.

Definition projPackS {X: Type} {X': Type} {prX: X' ⤖ X} {T:Type} {p: forall (a:X'), T -> Prop}
  (pack: @PackS X X' prX T p)
  : @uPackS X T 
  := {| f_rel_uS := pack.(relS); f_funct_uS := pack.(functS) |}.
#[global] Hint Unfold projPackS:get_rel_db.

Ltac pack_eq_lem :=
  intros xd yd xr yr xl xf yl yf; intros -> ->;
  assert (xl = yl) as Hl by (apply proof_irrelevance);
  assert (xf = yf) as Hf by (apply proof_irrelevance);
  rewrite Hl; rewrite Hf; reflexivity.

(*Lemma packEqLem {X: Type} {X': Type} {prX: X' ⤖ X} {T:Type} {p: forall (a:X'), T -> Prop}:
  forall (xd yd: forall (x:X'), {v:T|p x v}) (xr yr: X -> T -> Prop) 
(xl : forall (x: X') (v : T), ⌊ xd x ⌋ = v <-> xr (proj x) v)
(xf : forall (x : X) (v v': T), xr x v -> xr x v' -> v = v')
(yl : forall (x: X') (v : T), ⌊ yd x ⌋ = v <-> yr (proj x) v)
(yf : forall (x : X) (v v': T), yr x v -> yr x v' -> v = v'), 
xd = yd -> xr = yr ->
{| f := xd; f_rel := xr; f__f_rel := xl; f_funct := xf |} =
{| f := yd; f_rel := yr; f__f_rel := yl; f_funct := yf |}.
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
Qed.*)

#[global] Instance packPrF {X: Type} {X': Type} {prX: X' ⤖ X} {A A' prA B B' prB Yr} {extractRel: (@uPack A B) ⤖ (A -> Yr)}
    {prY: forall (x:X'), (@GPack A A' prA B (B' x) (prB x) Yr) ⤖ (@uPack A B)}: 
    (PackF X X' prX extractRel prY) ⤖ (@uPackF X (@uPack A B) (A -> Yr)).
Proof.
  unshelve refine {| proj:=_ |}.
  - intros [f rel f_rel]. refine {| f_rel_uF:=rel; f_funct_uF:=_ |}.
    intros x v v' -> ->. reflexivity.
  - intros [f rel f_rel] [f' rel' f_rel'] H.
    inversion H.
    revert H1. intros ->.
    enough (fEq: f = f') by (revert fEq; intros ->; 
       now replace f_rel with f_rel' by (apply proof_irrelevance)).
    apply functional_extensionality_dep; intro x.
    specialize (f_rel x). specialize (f_rel' x).
    assert (proj (f x) = proj (f' x)) as K.
    { assert (forall v : uPack A B, proj (f x) = v <-> proj (f' x) = v) as Hp.
      { intro y; now rewrite (f_rel' y). }
      now rewrite Hp. 
    }
    exact ((prY x).(po) _ _ K).
Defined.

#[global] Instance packPr {X: Type} {X': Type} {prX: X' ⤖ X} {Y Y'} {prY Yr}: 
  (@Pack X X' prX Y Y' prY Yr) ⤖ (@uPack X Y).
Proof.
  unshelve refine {| proj:=fun pack => _; po:=_ |}. 
  - destruct pack; [refine (@UPackS _ _ _) | (*refine (@UPackF _ _ _ _ _) *)].
   -- apply (projPackS pack0).
   -- 
      Check UPackF.
      try refine (@UPackF X (uPack A B) (X -> Yr) _). (* universe inconsistency issues: Y in wrong universe *)
      try timeout 5 pose ((packPrF pack0).(proj)) as res.
      (*unshelve refine (let res : @uPackF X (uPack A B) (X -> Yr) := (packPrF pack0).(proj) in _).*)
      try refine (@UPackF X (uPack A B) (X -> Yr) res). (* universe inconsistency error *)
      admit.
Admitted.
(*
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
Qed.
*)