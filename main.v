Require Import Arith.

Theorem plus_one_to_natural : forall n : nat, 1 + n = S n /\ S n > n.
Proof.
  intros n.
  split.
    - simpl. reflexivity.
    - apply le_n_S. apply le_n.
Qed.
Print plus_one_to_natural.
Eval compute in (plus_one_to_natural 5).
    
Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d: day) : day :=
  match d with
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => monday
    | saturday => monday
    | sunday => monday
  end.

Compute (next_weekday friday).
Compute (next_weekday (next_weekday saturday)).

Inductive bool : Type :=
  | true
  | false.

Definition negb (b: bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

Definition andb (b1 b2: bool) : bool :=
  match b1 with
    | true => b2
    | false => false
  end.

Definition orb (b1 b2: bool) : bool :=
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

Definition negb' (b: bool) : bool :=
  if b then false
    else true.

Definition andb' (b1 b2: bool) : bool :=
  if b1 then b2
    else false.

Definition orb'(b1 b2: bool) : bool :=
  if b1 then true
    else b2.

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type := 
  | black
  | white
  | primary (p: rgb).

Definition monochrome (c: color) : bool :=
  match c with
    | black => true
    | white => true
    | primary p => false
  end.

Definition isred (c: color) : bool :=
  match c with
    | black => false
    | white => false
    | primary red => true
    | primary _ => false
  end.

Module Playground.
  Definition myblue: rgb := blue.
End Playground.

Definition myblue: bool := true.

Check Playground.myblue : rgb.
Check myblue : bool.

Inductive bit : Type := 
  | B0
  | B1.

Inductive nybble : Type :=
  | bits (b0 b1 b2 b3: bit).

Check (bits B1 B0 B1 B0) : nybble.

Definition all_zero (nb: nybble): bool := 
  match nb with
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _) => false
  end.

Compute (all_zero (bits B1 B0 B1 B0)).
Compute (all_zero (bits B0 B0 B0 B0)).

Module NatPlayground.
Inductive nat : Type :=
  | O
  | S (n: nat).

Inductive nat' : Type :=
  | stop
  | tick (foo: nat').

Definition pred (n: nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.
End NatPlayground.

Check (S (S (S (S 1)))) : nat.
Definition minustwo (n: nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Compute (minustwo 4).

Check S : nat -> nat.
Check pred : nat -> nat.
Check minustwo : nat -> nat.

Fixpoint even (n: nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => even n'
  end.

Definition odd (n: nat) : bool :=
  negb (even n).

Example test_odd1: odd 1 = true.
Proof. simpl. reflexivity. Qed.

Example test_odd2: odd 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.
Fixpoint plus (n: nat) (m: nat): nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Compute (plus 2 3).

Fixpoint mult (n m: nat) : nat := 
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.
Print mult.
Compute (mult 3 3).

Print mult.
Print "*".
Print "+".
Print "/".
Compute (10 / 2).