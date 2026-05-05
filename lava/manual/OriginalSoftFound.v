Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.
Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.
Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity.  Qed.
From Coq Require Export String.
Inductive bool : Type :=
  | true
  | false.
Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.
Example test_orb1:  (orb true  false) = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_orb3:  (orb false true)  = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb4:  (orb true  true)  = true.
Proof. simpl. reflexivity.  Qed.
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
Example test_orb5:  false || false || true = true.
Proof. simpl. reflexivity. Qed.
Definition negb' (b:bool) : bool :=
  if b then false
  else true.
Definition andb' (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.
Definition orb' (b1:bool) (b2:bool) : bool :=
  if b1 then true
  else b2.
Definition nandb (b1:bool) (b2:bool) : bool := negb (b1 && b2).
Example test_nandb1: (nandb true false) = true. Proof. easy. Qed.
Example test_nandb2:               (nandb false false) = true. Proof. easy. Qed.
Example test_nandb3:               (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4:               (nandb true true) = false.
Proof. reflexivity. Qed.
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool := 
  b1 && b2 && b3.
Example test_andb31:                 (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32:                 (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33:                 (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34:                 (andb3 true true false) = false.
Proof. reflexivity. Qed.
Inductive rgb : Type :=
  | red
  | green
  | blue.
Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).
Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.
Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.
Inductive bit : Type :=
  | B1
  | B0.
Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).
Definition all_zero (nb : nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | (bits _ _ _ _) => false
  end.
Module NatPlayground.
Inductive nat : Type :=
  | O
  | S (n : nat).
Inductive otherNat : Type :=
  | stop
  | tick (foo : otherNat).
Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.
End NatPlayground.
Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.
Fixpoint even (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => even n'
  end.
Definition odd (n:nat) : bool :=
  negb (even n).
Example test_odd1:    odd 1 = true.
Proof. simpl. reflexivity.  Qed.
Example test_odd2:    odd 4 = false.
Proof. simpl. reflexivity.  Qed.
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.
Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.
Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity.  Qed.
Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O   , _    => O
  | S _ , O    => n
  | S n', S m' => minus n' m'
  end.
Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.
Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => 1
  | S n => (S n) * factorial n
  end.
Example test_factorial1:          (factorial 3) = 6.
Proof. reflexivity. Qed.
Example test_factorial2:          (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.
Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.
Example test_leb1:                leb 2 2 = true.
Proof. simpl. reflexivity.  Qed.
Example test_leb2:                leb 2 4 = true.
Proof. simpl. reflexivity.  Qed.
Example test_leb3:                leb 4 2 = false.
Proof. simpl. reflexivity.  Qed.
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Example test_leb3': (4 <=? 2) = false.
Proof. reflexivity.  Qed.
Definition ltb (n m : nat) : bool := (n <=? m) && negb (m =? n).
Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
Example test_ltb1:             (ltb 2 2) = false.
  Proof. reflexivity. Qed.
Example test_ltb2:             (ltb 2 4) = true.
Proof. reflexivity. Qed.
Example test_ltb3:             (ltb 4 2) = false.
Proof. reflexivity. Qed.
Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity.  Qed.
Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity.  Qed.
Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity.  Qed.
Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity.  Qed.
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o -> ->. reflexivity. Qed.
Theorem mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. Qed.
Lemma add_succ_r: forall n m : nat, n + S m = S (n + m).
Proof.
  now induction n.
Qed.
Lemma add_assoc: forall n m p : nat, n + (m + p) = n + m + p.
Proof.
  induction n as [|n' IHn']; intros.
  - reflexivity.
  - simpl. f_equal. apply (IHn' m p).
Qed. 
Lemma mult_n_sm : forall n m : nat, n * m + n = n * S m.
Proof.
  induction n as [|n' IHn']; intros.
  - reflexivity.
  - simpl. rewrite <- (IHn' m). 
    rewrite (add_succ_r (m + n' * m) n').
    f_equal. now rewrite <- (add_assoc m (n' * m) n').
Qed.
Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
  intros. pose proof (mult_n_sm p O). 
  pose proof (mult_n_O p).
  symmetry.
  destruct H0 as [<-].
  destruct H as [<-].
  reflexivity.
Qed.
Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity.   Qed.
Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity.  Qed.
Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros. destruct b eqn:D; now destruct c eqn:E.
Qed.
Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  now intros [|n].
Qed.
Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H b.
  pose proof (H b).
  pose proof (H (f b)).
  unshelve (etransitivity; eassumption).
Qed.
Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. f_equal. apply IHn'.  Qed.
Theorem minus_n_n : forall n,
  minus n n = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) simpl. reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.  Qed.
Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  induction n as [|n' IHn'].
  - easy.
  - simpl. apply IHn'.
Qed.
Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros. induction n.
  - easy.
  - simpl. f_equal. apply IHn. 
Qed.
Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros; induction n.
  - easy.
  - simpl. 
    pose proof (plus_n_Sm m n) as H.
    etransitivity; try apply H.
    f_equal.
    easy.
Qed.
Inductive natprod : Type :=
  | pair (n1 n2 : nat).
Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.
Definition swap_pair (p : natprod) : natprod :=
  match p with
  | pair x y => pair y x
  end.
Theorem surjective_pairing' : forall (n m : nat),
  pair n m = pair (fst (pair n m)) (snd (pair n m)).
Proof.
  reflexivity. Qed.
Theorem surjective_pairing : forall (p : natprod),
  p = pair (fst p) (snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.