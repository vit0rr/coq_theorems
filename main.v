Theorem plus_one_to_natural : forall n : nat, 1 + n = S n /\ S n > n.
Proof.
  intros n.
  split.
    - simpl. reflexivity.
    - apply le_n_S. apply le_n.
Qed.
Print plus_one_to_natural.
Eval compute in (plus_one_to_natural 5).
    