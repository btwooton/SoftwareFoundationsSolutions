Add LoadPath "/Users/Troy/Code/Coq/software_foundations/".
Require Export Basics.
Require Export Induction.
Export Induction.

Module NatList.

Inductive natprod : Type :=
| pair : nat -> nat -> natprod.

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x , y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x , y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x , y) => (y , x)
  end.

Theorem surjective_pairing : forall n m : nat,
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.
Qed.

Theorem surjective_pairing' : forall p : natprod,
  p = (fst p, snd p).
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
  (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => []
  | S c => n :: (repeat n c)
  end.

Fixpoint length (l : natlist) : nat :=
  match l with
  | nil => O
  | cons x rest => S (length rest)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | [] => l2
  | h::t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
  (right associativity, at level 60).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Fixpoint nonzeros (l : natlist) : natlist :=
  match l with
  | nil => nil
  | O :: rest => (nonzeros rest)
  | h :: rest => h :: (nonzeros rest)
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l : natlist) :=
  match l with
  | nil => nil
  | h :: t => match oddb h with
              | true => h :: (oddmembers t)
              | false => oddmembers t
              end
  end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Fixpoint countoddmembers (l : natlist) : nat :=
  match l with
  | nil => O
  | h :: t => match oddb h with
              | true => S (countoddmembers t)
              | false => countoddmembers t
              end
  end.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h::t => match l2 with
            | nil => l1
            | x::rest => h::x::(alternate t rest)
            end
  end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. simpl. reflexivity. Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. simpl. reflexivity. Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. simpl. reflexivity. Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. simpl. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => 0
  | h::t => match beq_nat h v with
            | true => 1 + (count v t)
            | false => (count v t)
            end
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. simpl. reflexivity. Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. simpl. reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag := v::s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool :=
  blt_nat 0 (count v s).

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.

Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h::t => match beq_nat h v with
            | true => t
            | false => h::(remove_one v t)
            end
  end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t => match beq_nat h v with
              | true => (remove_all v t)
              | false => h :: (remove_all v t)
              end
  end.

Example test_remove_all1: 
  count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_all2:
  count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_all3:
  count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.

Example test_remove_all4:
  count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1, s2 with
  | nil, nil => true
  | nil, xs => true
  | xs, nil => false
  | (h::t), xs => match member h xs with
                 | true => subset t (remove_one h xs)
                 | false => false
                  end
  end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.

Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.

Lemma add_to_nil : forall (b : bag) (n : nat),
  b = nil -> (add n b) = [n].
Proof.
  intros b n.
  intros H.
  rewrite H.
  reflexivity.
Qed.

Lemma beq_reflexive : forall (n : nat),
  beq_nat n n = true.
Proof.
  intros n.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Lemma count_elem_singleton : forall (b : bag) (n : nat),
  b = n::nil -> (count n b) = 1.
Proof.
  intros b n.
  intros H.
  rewrite H.
  simpl.
  rewrite beq_reflexive.
  reflexivity.
Qed.

Lemma count_elem_nil : forall (n : nat),
  count n nil = 0.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.
  

Theorem bag_theorem : forall (n : nat),
  count n (add n nil) = 1.
Proof.
  intros n.
  rewrite add_to_nil.
  - rewrite count_elem_singleton. reflexivity. reflexivity.
  - reflexivity.
Qed.

Theorem nil_app : forall (l : natlist),
  [] ++ l = l.
Proof.
  simpl.
  reflexivity.
Qed.

Theorem tsl_length_pred : forall (l : natlist),
  pred (length l) = length (tl l).
Proof.
  intros l.
  destruct l as [| h t].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3.
  induction l1.
  - simpl. reflexivity.
  - simpl. rewrite IHl1. reflexivity.
Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h::t => app (rev t) [h]
  end.

Example test_rev1 : rev [1;2;3] = [3;2;1].
Proof. simpl. reflexivity. Qed.

Example test_rev2 : rev nil = nil.
Proof. reflexivity. Qed.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2.
  induction l1 as [| h l1' IHl1'].
  - simpl. reflexivity.
  - simpl. rewrite IHl1'. reflexivity.
Qed.

Theorem rev_length : forall (l : natlist),
  length (rev l) = length l.
Proof.
  intros l.
  induction l as [| l' t IHl'].
  - simpl. reflexivity.
  - simpl. rewrite app_length, plus_comm.
    simpl. rewrite IHl'. reflexivity.
Qed.

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l.
  induction l as [| l' t IHl'].
  - simpl. reflexivity.
  - simpl. rewrite IHl'. reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2.
  induction l1 as [| l1' t IHl1'].
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHl1'. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l.
  induction l as [| l' t IHl'].
  - simpl. reflexivity.
  - simpl. rewrite rev_app_distr. rewrite IHl'.
    simpl. reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  rewrite app_assoc.
  rewrite app_assoc.
  reflexivity.
Qed.

Lemma nonzeros_nil : forall (l : natlist),
  l = nil -> nonzeros l = l.
Proof.
  intros l.
  intros H.
  rewrite H.
  simpl.
  reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2.
  induction l1 as [| l1' t IHl1'].
  - simpl. reflexivity.
  - induction l1' as [| n].
    + simpl. rewrite IHl1'. reflexivity.
    + simpl. rewrite IHl1'. reflexivity.
Qed.

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1, l2 with
  | nil, nil => true
  | nil, xs => false
  | xs, nil => false
  | (h::t), (x::xs) =>
    match beq_nat h x with
    | true => beq_natlist t xs
    | false => false
    end
  end.

Example test_beq_natlist1 : (beq_natlist nil nil = true).
Proof. reflexivity. Qed.

Example test_beq_natlist2 :
  beq_natlist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.

Example test_beq_natlist3 :
  beq_natlist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem beq_natlist_refl : forall (l : natlist),
  true = beq_natlist l l.
Proof.
  induction l as [| h t IHl].
  - simpl. reflexivity.
  - simpl. rewrite beq_reflexive. exact IHl.
Qed.

Theorem count_member_nonzero : forall (s : bag),
  leb 1 (count 1 (1 :: s)) = true.
Proof.
  intros s.
  simpl.
  reflexivity.
Qed.

Lemma ble_n_Sn : forall n : nat,
  leb n (S n) = true.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem remove_decreaes_count : forall (s : bag),
  leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intros s. induction s as [| x y IHs'].
  - simpl. reflexivity.
  - induction x as [| x' IHx'].
    + simpl. rewrite ble_n_Sn. reflexivity.
    + simpl. exact IHs'.
Qed.

Lemma blt_Sn_SSn : forall n : nat,
  blt_nat (S n) (S (S n)) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - tauto.
Qed.

Theorem bag_count_sum : forall (b : bag),
  blt_nat (count 0 b) (count 0 (sum [0] b)) = true.
Proof.
  intros b.
  induction b as [| h t IHb].
  - simpl. tauto.
  - induction h as [| h' IHh'].
    + simpl. rewrite blt_Sn_SSn. reflexivity.
    + simpl. tauto.
Qed.

Theorem rev_injective : forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2.
  intros H.
  rewrite <- rev_involutive.
  assert (rev l2 = rev l1).
  - symmetry. exact H.
  - rewrite H0. rewrite rev_involutive. reflexivity.
Qed.

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' =>
    match beq_nat n O with
    | true => Some a
    | false => nth_error l' (pred n)
    end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.

Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.

Example test_nt_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Definition hd_error (l : natlist) : natoption :=
  match l with
  | nil => None
  | h::t => Some h
  end.

Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.

Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd : forall (l : natlist) (d : nat),
  hd d l = option_elim d (hd_error l).
Proof.
  intros l d.
  induction l as [| h t IHl'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

Theorem beq_id_refl : forall (x : id),
 true = beq_id x x.
Proof.
  intros x.
  destruct x.
  simpl.
  rewrite beq_reflexive.
  reflexivity.
Qed.

End NatList.

Module PartialMap.
Export NatList.

Inductive partial_map : Type :=
  | empty : partial_map
  | record : id -> nat -> partial_map -> partial_map.

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => if beq_id x y
                     then Some v
                     else (find x d')
  end.

Theorem update_eq :
  forall (d : partial_map) (x : id) (v : nat),
  find x (update d x v) = Some v.
Proof.
  intros d x v.
  induction d as [| x' v' d' IHd'].
  - simpl. destruct x. simpl. rewrite beq_reflexive.
    reflexivity.
  - simpl. destruct x. simpl. rewrite beq_reflexive.
    reflexivity.
Qed.

Theorem update_neq :
  forall (d : partial_map) (x y : id) (o : nat),
  beq_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros d x y o.
  intros H.
  destruct d.
  - simpl. rewrite H. reflexivity.
  - simpl. rewrite H. reflexivity.
Qed.

Inductive baz : Type :=
  | Baz1 : baz -> baz
  | Baz2 : baz -> bool -> baz.

End PartialMap.
  
 
  
 