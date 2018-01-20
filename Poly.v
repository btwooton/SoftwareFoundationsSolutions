Add LoadPath "/Users/Troy/Code/Coq/software_foundations/".
Require Export Lists.
Set Warnings "-notation-overridden, -parsing".

Inductive list (X: Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Example test_repeat1:
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.

Example test_repeat2:
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.

Module MumbleGrumble.

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

End MumbleGrumble.

Fixpoint repeat' X x count : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil _ => l2
  | cons _ h t => cons _ h (app t l2)
  end.

Fixpoint rev {X : Type} (l : list X) : list X :=
  match l with
  | nil _ => nil _
  | cons _ h t => app (rev t) (cons _ h (nil _))
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil _ => O
  | cons _ h t => S (length t)
  end.

Arguments nil {X}.
Arguments cons {X} _ _.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.

Example test_rev2 :
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.

Notation "x :: y" := (cons x y)
  (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
  (at level 60, right associativity).

Definition list123''' := [1;2;3].

Theorem app_nil_r : forall (X : Type), forall (l : list X),
  l ++ [] = l.
Proof.
  intros X l.
  induction l as [| h t IHl'].
  - simpl. reflexivity.
  - simpl. rewrite IHl'. reflexivity.
Qed.

Theorem app_assoc : forall (A : Type) (l m n : list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n.
  induction l as [| h t IHl'].
  - simpl. reflexivity.
  - simpl. rewrite IHl'. reflexivity.
Qed.

Lemma app_length : forall (X : Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2.
  induction l1, l2.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite <- plus_n_O.
    rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHl1. simpl.
    rewrite <- Peano.plus_n_Sm. reflexivity.
Qed.

Theorem rev_app_distr: forall (X : Type) (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2.
  induction l1, l2.
  - simpl. reflexivity.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHl1. simpl.
    rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall (X : Type), forall (l : list X),
  rev (rev l) = l.
Proof.
  intros X l.
  induction l as [| h t IHl'].
  - simpl. reflexivity.
  - simpl. rewrite rev_app_distr.
    rewrite IHl'. simpl. reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
  | pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).
Notation " X * Y " := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
  : list (X*Y) :=
  match lx with
  | nil => nil
  | h::t =>
    match ly with
    | nil => nil
    | x::y => (h, x)::(combine t y)
    end
  end.

Fixpoint split {X Y : Type} (l : list (X*Y)) 
  : (list X) * (list Y) :=
  match l with
  | nil => (nil, nil)
  | (x, y) :: rest => 
    (x :: fst (split rest), y :: snd (split rest))
  end. 

Example test_split:
  split [(1,false);(2,false)] = ([1;2], [false;false]).
Proof. simpl. reflexivity. Qed.


