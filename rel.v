Require Export Logic_J.

Definition relation (X : Type) := X -> X -> Prop.

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Theorem next_nat_partial_function :
  partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 P Q.
  inversion P.
  inversion Q.
  reflexivity. Qed.

Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
  unfold not.
  unfold partial_function.
  intros H.
  assert (0 = 1) as Nonsense.
  Case "Proof of assertion".
  apply H with O.
    apply le_n.
    apply le_S.
    apply le_n.
  inversion Nonsense. Qed.

Definition reflexive {X: Type} (R: relation X) :=
  forall a: X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive.
  intros n.
  apply le_n. Qed.

Definition transitive {X: Type} (R: relation X) :=
  forall a b c: X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
    apply Hnm.
    apply le_S.
    apply IHHmo. Qed.

Theorem lt_trans :
  transitive lt.
Proof.
  unfold lt.
  unfold transitive.
  intros n m o Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  apply Hnm.
  apply Hmo. Qed.

Theorem lt_trans' :
  transitive lt.
Proof.
  unfold lt.
  unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [|m' Hm' o].
    apply le_S.
    apply Hnm.
    apply le_S.
    apply o. Qed.

Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt.
  unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [|o'].
    inversion Hmo.
    induction Hmo as [|o2].
      apply le_S.
      apply Hnm.
      apply le_S.
      apply IHHmo. Qed.

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H.
  apply le_trans with (S n).
  apply le_S.
  apply le_n.
  apply H. Qed.

Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  intros n m H.
  inversion H.
    apply le_n.
    apply le_Sn_le.
    apply H1. Qed.

Theorem le_Sn_n : forall n,
  ~ (S n <= n).
Proof.
  intros n.
  unfold not.
  intros H.
  induction n as [|n'].
    inversion H.
    apply IHn'.
    apply le_S_n.
    assumption. Qed.

Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
  unfold symmetric.
  intros contra.
  assert (1 <= 0) as NH10.
  apply contra.
  apply le_S.
  apply le_n.
  inversion NH10. Qed.

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  Admitted.

Definition equivalence {X: Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

Definition order {X: Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

Definition preorder {X: Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order :
  order le.
Proof.
  unfold order.
  split.
    apply le_reflexive.
    split.
      apply le_antisymmetric.
      apply le_trans. Qed.
