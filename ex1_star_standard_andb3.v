Definition andb (b1 b2 b3: bool) : bool :=
  match b1 with
    | true => b2 && b3
    | false => false
  end.

Example test_andb1: (andb true true true) = true.
Proof.
    simpl.
    reflexivity.
Qed.

Example test_andb2: (andb false true true) = false.
Proof.
    simpl.
    reflexivity.
Qed.

Example test_andb3: (andb true false true) = false.
Proof.
    simpl.
    reflexivity.
Qed.

Example test_andb4: (andb true true false) = false.
Proof.
    simpl.
    reflexivity.
Qed.
