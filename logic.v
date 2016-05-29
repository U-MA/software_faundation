Require Export Prop_J.

(* ->とforallは同じもの *)

Definition funny_prop1 :=
  forall n, forall (E : ev n), ev (n + 4).
Definition funny_prop1' :=
  forall n, forall (_ : ev n), ev (n + 4).
Definition funny_prop1'' :=
  forall n, ev n -> ev (n + 4).
