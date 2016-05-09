Require Export Poly_J.

Definition even (n:nat) : Prop :=
  evenb n = true.

Check even.

Check (even 4).

Check (even 3).
