Require Export Prop_J.

(* ->とforallは同じもの *)

Definition funny_prop1 :=
  forall n, forall (E : ev n), ev (n + 4).
Definition funny_prop1' :=
  forall n, forall (_ : ev n), ev (n + 4).
Definition funny_prop1'' :=
  forall n, ev n -> ev (n + 4).

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q).

Notation "P /\ Q" := (and P Q) : type_scope.

Theorem and_example :
  (ev 0) /\ (ev 4).
Proof.
  apply conj.
  apply ev_0.
  apply ev_SS.
  apply ev_SS.
  apply ev_0. Qed.

Print and_example.

Theorem and_example' :
  (ev 0) /\ (ev 4).
Proof.
  split.
    apply ev_0.
    apply ev_SS.
    apply ev_SS.
    apply ev_0. Qed.

Theorem proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HP. Qed.

Theorem proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HQ. Qed.

Theorem and_commut:forall P Q:Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  split.
  apply HQ.
  apply HP. Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
  split.
  split.
  apply HP.
  apply HQ.
  apply HR. Qed.

Theorem even_ev : forall n : nat,
  (even n -> ev n) /\ (even (S n) -> ev (S n)).
Proof.
  induction n as [|n'].
  split.
  intros ex.
  apply ev_0.
  intros ex.
  inversion ex.
  split.
  apply IHn'.
  intros H.
  apply ev_SS.
  inversion IHn'.
  apply H0.
  apply H. Qed.

Definition conj_fact : forall P Q R,
  P /\ Q -> Q /\ R -> P /\ R :=
  (fun (P Q R : Prop) =>
    (fun (H0 : and P Q) =>
      (fun (H1 : and Q R) =>
        conj P R (proj1 P Q H0) (proj2 Q R H1)))).

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
  (at level 95, no associativity) : type_scope.

Theorem iff_implies : forall P Q : Prop,
  (P <-> Q) -> P -> Q.
Proof.
  intros P Q H H'.
  apply H.
  apply H'. Qed.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q H.
  inversion H.
  split.
  apply H1.
  apply H0. Qed.

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros P.
  split.
  intros H.
  apply H.
  intros H.
  apply H. Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R H0 H1.
  split.
  intros P'.
  apply H1.
  apply H0.
  apply P'.
  intros R'.
  apply H0.
  apply H1.
  apply R'. Qed.
