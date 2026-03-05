Load LiquidPreludeInterface.

Ltac lia_shape_based := match goal with  
  | [ h: forall v, ltbZ_rel ?s ?t v -> _ |- _] => 
    specialize (h (s <? t));
    specialize (h (ltac:(constructor)))
  | [ h: forall v, lebZ_rel ?s ?t v -> _ |- _] => 
    specialize (h (s <=? t));
    specialize (h (ltac:(constructor)))
  | [ h: forall v, eqbZ_rel ?s ?t v -> _ |- _] => 
    specialize (h (s =? t));
    specialize (h (ltac:(constructor)))
  end.

Create HintDb lia_unfold.

(* Lemmata for addition on Z *)
Lemma addZ_rel_funct [m n: Z]: (forall x x' (H: addZ_rel m n x) (K: addZ_rel m n x') , x = x'). 
Proof. 
	intros x x'. inversion 1. now inversion 1. 
Qed. 

Theorem addZ_lem (m n: _) (res: _): (addZ_rel m n res) <-> (res = m + n). 
Proof. 
  split; intro H; subst; [now inversion H | constructor].
Qed. 
Theorem addZ_rel_ex (m n: Z) (m_p n_p: True): addZ_rel m n (proj1_sig (addZ (exist _ m m_p) (exist _ n n_p))). 
Proof. 
  autounfold with lia_unfold; constructor.
Qed. 

Theorem addZ__addZ_rel_rw (m n: Z) {m_p n_p: True} {x: Z}: ((proj1_sig (addZ (exist _ m m_p) (exist _ n n_p) )) = x) <-> (addZ_rel m n x). 
Proof. 
	autounfold with lia_unfold; split; repeat first [intros <- | now inversion 1 | constructor]. 
Qed.

Lemma proj_addZ (s t:_): proj1_sig (s +Z t) = proj1_sig s + proj1_sig t.
Proof.
  reflexivity.
Qed.

Lemma addZ_rel_rw (s t u:_): addZ_rel s t u <-> u = s + t.
Proof.
  split; intros H; repeat first [constructor|inversion H|reflexivity].
Qed.

(* Lemmata for <= on Z *)
Lemma lebZ_rel_funct [m n: Z]: (forall x x' (H: lebZ_rel m n x) (K: lebZ_rel m n x') , x = x'). 
Proof. 
	intros x x'. inversion 1. now inversion 1. 
Qed. 

Theorem lebZ_lem_true (m n: _): (lebZ_rel m n true) <-> (m <= n). 
Proof. 
  split; intro H; subst; [inversion H; lia | replace true with (m <=? n) by lia; constructor]. 
Qed. 
Theorem lebZ_lem (m n: _) (res: _): (lebZ_rel m n res) <-> (res = (m <=? n)). 
Proof. 
  split; intro H; subst; [now inversion H | constructor].
Qed. 
Theorem lebZ_rel_ex (m n: Z) (m_p n_p: True): lebZ_rel m n (proj1_sig (lebZ (exist _ m m_p) (exist _ n n_p) )). 
Proof. 
  autounfold with lia_unfold; constructor.
Qed. 

Theorem lebZ__lebZ_rel_rw (m n: Z) {m_p n_p: True} {x: bool}: ((proj1_sig (lebZ (exist _ m m_p) (exist _ n n_p))) = x) <-> (lebZ_rel m n x). 
Proof. 
	autounfold with lia_unfold; split; repeat first [intros <- | now inversion 1 | constructor].
Qed.

Lemma lebZ_rel_rw (s t:Z) (u:bool): lebZ_rel s t u <-> u = (s <=? t).
Proof.
  split; intros H; repeat progress first [constructor|inversion H|reflexivity].
Qed.

(* Lemmata for < on Z *)
Lemma ltbZ_rel_funct [m n: Z]: (forall x x' (H: ltbZ_rel m n x) (K: ltbZ_rel m n x') , x = x'). 
Proof. 
	intros x x'. inversion 1. now inversion 1. 
Qed. 

Theorem ltbZ_lem_true (m n: _): (ltbZ_rel m n true) <-> (m < n). 
Proof. 
  split; intro H; subst; [inversion H; lia | replace true with (m <? n) by lia; constructor]. 
Qed. 
Theorem ltbZ_lem (m n: _) (res: _): (ltbZ_rel m n res) <-> (res = (m <? n)). 
Proof. 
  split; intro H; subst; [now inversion H | constructor].
Qed. 
Theorem ltbZ_rel_ex (m n: Z) (m_p n_p: True): ltbZ_rel m n (proj1_sig (ltbZ (exist _ m m_p) (exist _ n n_p))). 
Proof. 
	autounfold with lia_unfold; constructor.
Qed. 

Theorem ltbZ__ltbZ_rel_rw (m n: Z) {m_p n_p: True} {x: bool}: ((proj1_sig (ltbZ (exist _ m m_p) (exist _ n n_p))) = x) <-> (ltbZ_rel m n x). 
Proof. 
	autounfold with lia_unfold; split; repeat first [intros <- | now inversion 1 | constructor].
Qed.

Lemma ltbZ_rel_rw (s t:Z) (u:bool): ltbZ_rel s t u <-> u = (Z.ltb s t).
Proof.
  split; intros H; repeat progress first [constructor|inversion H|reflexivity].
Qed.

(* Lemmata for =? on Z *)
Lemma eqbZ_rel_funct [m n: Z]: (forall x x' (H: eqbZ_rel m n x) (K: eqbZ_rel m n x') , x = x'). 
Proof. 
	intros x x'. inversion 1. now inversion 1. 
Qed. 

Theorem eqbZ_lem_true (m n: _): (eqbZ_rel m n true) <-> (m = n). 
Proof. 
  split; intro H; subst; [inversion H; lia | replace true with (n =? n) by lia; constructor]. 
Qed. 
Theorem eqbZ_lem (m n: _) (res: _): (eqbZ_rel m n res) <-> (res = (m =? n)). 
Proof. 
  split; intro H; subst; [now inversion H | constructor].
Qed. 
Theorem eqbZ_rel_ex (m n: Z) (m_p n_p: True): eqbZ_rel m n (proj1_sig (eqbZ (exist _ m m_p) (exist _ n n_p))). 
Proof. 
	autounfold with lia_unfold; constructor.
Qed. 

Theorem eqbZ__eqbZ_rel_rw (m n: Z) {m_p n_p: True} {x: bool}: ((proj1_sig (eqbZ (exist _ m m_p) (exist _ n n_p))) = x) <-> (eqbZ_rel m n x). 
Proof. 
	autounfold with lia_unfold; split; repeat first [intros <- | now inversion 1 | constructor].
Qed.

(* Lemmata for >= on Z *)
Lemma gebZ_rel_funct [m n: Z]: (forall x x' (H: gebZ_rel m n x) (K: gebZ_rel m n x') , x = x'). 
Proof. 
	intros x x'. inversion 1. now inversion 1. 
Qed. 

Theorem gebZ_lem_true (m n: _): (gebZ_rel m n true) <-> (m >= n). 
Proof. 
  split; intro H; subst; [inversion H; lia | replace true with (m >=? n) by lia; constructor]. 
Qed. 
Theorem gebZ_lem (m n: _) (res: _): (gebZ_rel m n res) <-> (res = (m >=? n)). 
Proof. 
  split; intro H; subst; [now inversion H | constructor].
Qed. 
Theorem gebZ_rel_ex (m n: Z) (m_p n_p: True): gebZ_rel m n (proj1_sig (gebZ (exist _ m m_p) (exist _ n n_p))). 
Proof. 
  autounfold with lia_unfold; constructor.
Qed. 

Theorem gebZ__gebZ_rel_rw (m n: Z) {m_p n_p: True} {x: bool}: ((proj1_sig (gebZ (exist _ m m_p) (exist _ n n_p))) = x) <-> (gebZ_rel m n x). 
Proof. 
	autounfold with lia_unfold; split; repeat first [intros <- | now inversion 1 | constructor].
Qed.

Lemma gebZ_rel_rw (s t:Z) (u:bool): gebZ_rel s t u <-> u = (s >=? t).
Proof.
  split; intros H; repeat progress first [constructor|inversion H|reflexivity].
Qed.

(* Lemmata for > on Z *)
Lemma gtbZ_rel_funct [m n: Z]: (forall x x' (H: gtbZ_rel m n x) (K: gtbZ_rel m n x') , x = x'). 
Proof. 
	intros x x'. inversion 1. now inversion 1. 
Qed. 

Theorem gtbZ_lem_true (m n: _): (gtbZ_rel m n true) <-> (m > n). 
Proof. 
  split; intro H; subst; [inversion H; lia | replace true with (m >? n) by lia; constructor]. 
Qed. 
Theorem gtbZ_lem (m n: _) (res: _): (gtbZ_rel m n res) <-> (res = (m >? n)). 
Proof. 
  split; intro H; subst; [now inversion H | constructor].
Qed. 
Theorem gtbZ_rel_ex (m n: Z) (m_p n_p: True): gtbZ_rel m n (proj1_sig (gtbZ (exist _ m m_p) (exist _ n n_p))). 
Proof. 
	autounfold with lia_unfold; constructor.
Qed. 

Theorem gtbZ__gtbZ_rel_rw (m n: Z) {m_p n_p: True} {x: bool}: ((proj1_sig (gtbZ (exist _ m m_p) (exist _ n n_p))) = x) <-> (gtbZ_rel m n x). 
Proof. 
	autounfold with lia_unfold; split; repeat first [intros <- | now inversion 1 | constructor].
Qed.

Lemma gtbZ_rel_rw (s t:Z) (u:bool): gtbZ_rel s t u <-> u = (Z.gtb s t).
Proof.
  split; intros H; repeat progress first [constructor|inversion H|reflexivity].
Qed.


(* Lemmata for - on Z *)
Lemma subZ_rel_funct [m n: Z]: (forall x x' (H: subZ_rel m n x) (K: subZ_rel m n x') , x = x'). 
Proof. 
	intros x x'. inversion 1. now inversion 1. 
Qed. 

Theorem subZ_lem (m n: _) (res: _): (subZ_rel m n res) <-> (res = m - n). 
Proof. 
  split; intro H; subst; [now inversion H | constructor].
Qed. 

Theorem subZ_rel_ex (m n: Z) (m_p n_p: _): subZ_rel m n (proj1_sig (subZ (exist _ m m_p) (exist _ n n_p))). 
Proof. 
	autounfold with lia_unfold; constructor.
Qed. 

Theorem subZ__subZ_rel_rw (m n: Z) {m_p n_p: _} {x: Z}: ((proj1_sig (subZ (exist _ m m_p) (exist _ n n_p))) = x) <-> (subZ_rel m n x). 
Proof. 
	autounfold with lia_unfold; split; repeat first [intros <- | now inversion 1 | constructor].
Qed.

Lemma subZ_rel_rw (s t u:_): subZ_rel s t u <-> u = s - t.
Proof.
  split; intros H; repeat first [constructor|inversion H|reflexivity].
Qed.

Lemma proj_subZ (s t:_): proj1_sig (s -Z t) = proj1_sig s - proj1_sig t.
Proof.
  reflexivity.
Qed.


(* Lemmata for * on Z *)
Lemma multZ_rel_funct [m n: Z]: (forall x x' (H: multZ_rel m n x) (K: multZ_rel m n x') , x = x'). 
Proof. 
	intros x x'. inversion 1. now inversion 1. 
Qed. 

Theorem multZ_lem (m n: _) (res: _): (multZ_rel m n res) <-> (res = m * n). 
Proof. 
  split; intro H; subst; [now inversion H | constructor].
Qed. 

Theorem multZ_rel_ex (m n: Z) (m_p n_p: _): multZ_rel m n (proj1_sig (multZ (exist _ m m_p) (exist _ n n_p))). 
Proof. 
	autounfold with lia_unfold; constructor.
Qed. 

Theorem multZ__multZ_rel_rw (m n: Z) {m_p n_p: _} {x: Z}: ((proj1_sig (multZ (exist _ m m_p) (exist _ n n_p))) = x) <-> (multZ_rel m n x). 
Proof. 
	autounfold with lia_unfold; split; repeat first [intros <- | now inversion 1 | constructor].
Qed.

Lemma multZ_rel_rw (s t u:_): multZ_rel s t u <-> u = s * t.
Proof.
  split; intros H; repeat first [constructor|inversion H|reflexivity].
Qed.

Lemma proj_multZ (s t:_): proj1_sig (s *Z t) = proj1_sig s * proj1_sig t.
Proof.
  reflexivity.
Qed.

(* Lemmata for / on Z *)
Lemma divZ_rel_funct [m n: Z]: (forall x x' (H: divZ_rel m n x) (K: divZ_rel m n x') , x = x'). 
Proof. 
	intros x x'. inversion 1. now inversion 1. 
Qed. 

Theorem divZ_lem (m n: _) (res: _): (divZ_rel m n res) <-> (res = m / n). 
Proof. 
  split; intro H; subst; [now inversion H | constructor].
Qed. 

Theorem divZ_rel_ex (m n: Z) (m_p n_p: _): divZ_rel m n (proj1_sig (divZ (exist _ m m_p) (exist _ n n_p))). 
Proof. 
	autounfold with lia_unfold; constructor.
Qed. 

Theorem divZ__divZ_rel_rw (m n: Z) {m_p n_p: _} {x: Z}: ((proj1_sig (divZ (exist _ m m_p) (exist _ n n_p))) = x) <-> (divZ_rel m n x). 
Proof. 
	autounfold with lia_unfold; split; repeat first [intros <- | now inversion 1 | constructor].
Qed.

Lemma divZ_rel_rw (s t u:_): divZ_rel s t u <-> u = s / t.
Proof.
  split; intros H; repeat first [constructor|inversion H|reflexivity].
Qed.

Lemma proj_divZ (s t:_): proj1_sig (s /Z t) = proj1_sig s / proj1_sig t.
Proof.
  reflexivity.
Qed.

#[global] Opaque addZ.
#[global] Opaque subZ.
#[global] Opaque ltbZ.
#[global] Opaque lebZ.
#[global] Opaque eqbZ.
#[global] Hint Unfold negBool : lia_unfold.
#[global] Hint Unfold is_true : lia_unfold.