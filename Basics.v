Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
  | true : bool
  | false : bool.

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

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | false => true
  | true => (negb b2)
  end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  andb b1 (andb b2 b3).

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.

Inductive color : Type :=
  | black : color
  | white : color
  | primary : rgb -> color.

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

Module NatPlayground.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

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

Example test_minustwo: (minustwo 5) = 3.
Proof. simpl. reflexivity. Qed.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.


Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.

Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.

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
Proof. simpl. reflexivity. Qed.

(* You can match two expression at once with a comma *)
Fixpoint minus (n m : nat) : nat :=
  match (n, m) with
  | (O, _) => O
  | (S _, O) => n
  | (S n', S m') => minus n' m'
  end.

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => S O
  | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
  (at level 50, left associativity)
  : nat_scope.

Notation "x - y" := (minus x y)
  (at level 50, left associativity)
  : nat_scope.

Notation "x * y" := (mult x y)
  (at level 40, left associativity)
  : nat_scope.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
        | O => true
        | S m' => false
        end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

(* Function to test whether first argument is leq second *)
Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' => match m with
            | O => false
            | S m' => leb n' m'
            end
  end.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.

Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.

Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Definition blt_nat (n m : nat) : bool :=
  andb (leb n m) (negb (beq_nat n m)).

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.

Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.

Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof. intros n. simpl. reflexivity. Qed.

Theorem plus_id_example : forall n m : nat,
  n = m -> n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite H.
  reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity.
Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.
Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n -> m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  destruct n as [| n'].
  - reflexivity.
  - reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem andb_commutative : forall b c : bool,
  andb b c = andb c b.
Proof.
  intros b c.
  destruct b.
  - destruct c.
    + reflexivity.
    + simpl. reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  destruct c.
  - destruct b.
    + simpl. intros H. exact H.
    + simpl. intros H. reflexivity.
  - destruct b.
    + simpl. intros H. exact H.
    + simpl. intros H. exact H.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros n.
  destruct n as [|n'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* Extra Exercises *)

Theorem identity_fn_applied_twice:
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros x.
  intros b.
  rewrite -> x.
  rewrite -> x.
  reflexivity.
Qed.

Theorem andb_eq_orb : forall b c : bool,
  (andb b c = orb b c) -> b = c.
Proof.
  intros b c.
  destruct c.
  - destruct b.
    + intros H. reflexivity.
    + simpl. intros H. exact H.
  - destruct b.
    + simpl. intros H. symmetry. exact H.
    + simpl. intros H. reflexivity.
Qed.

Inductive binary : Type :=
  | Z : binary
  | T : binary -> binary
  | TPO : binary -> binary.

Fixpoint incr (b : binary) : binary :=
  match b with
  | Z => TPO Z
  | T b' => TPO b'
  | TPO b'' => T (incr b'')
  end.

Fixpoint bin_to_nat (b : binary) : nat :=
  match b with
  | Z => O
  | TPO b' => 1 + (bin_to_nat b') * 2
  | T b' => (bin_to_nat b') * 2
  end.

Example test_bin_incr1: (incr Z) = TPO Z.
Proof. reflexivity. Qed.

Example test_bin_incr2: 
(incr (TPO Z)) = T (TPO Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr3:
(incr (T (TPO Z))) = TPO (TPO Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr4:
(incr (TPO (TPO Z))) = T (T (TPO Z)).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr5:
(incr (T (T (TPO Z)))) = TPO (T (TPO Z)).
Proof. simpl. reflexivity. Qed.

Example test_bin_to_nat1:
bin_to_nat (TPO (T (TPO Z))) = 5.
Proof. simpl. reflexivity. Qed.

Example test_bin_to_nat2:
bin_to_nat (T (T (TPO Z))) = 4.
Proof. simpl. reflexivity. Qed.

Example test_bin_to_nat3:
bin_to_nat (TPO (TPO Z)) = 3.
Proof. simpl. reflexivity. Qed.

Example test_bin_to_nat4:
bin_to_nat (T (TPO (TPO Z))) = 6.
Proof. simpl. reflexivity. Qed.

Example test_bin_to_nat5:
bin_to_nat (T (TPO (T (TPO Z)))) = 10.
Proof. simpl. reflexivity. Qed.