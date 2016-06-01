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

Definition MyProp_iff_ev : forall n, MyProp n <-> ev n :=
  (fun (n : nat) => conj (MyProp n -> ev n) (ev n-> MyProp n)
    (ev_MyProp n) (MyProp_ev n)).

Inductive or (P Q : Prop) : Prop :=
|or_introl : P -> or P Q
|or_intror : Q -> or P Q.

Notation "P \/ Q" := (or P Q) : type_scope.

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
  apply or_intror.
  apply HP.
  apply or_introl.
  apply HQ. Qed.

Theorem or_commut' : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
  right. apply HP.
  left. apply HQ. Qed.

Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R H.
  inversion H as [HP | [HQ HR]].
  split.
  left. apply HP.
  left. apply HP.
  split.
  right. apply HQ.
  right. apply HR. Qed.

Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros P Q R H.
  inversion H as [[HP | HQ] [HP' | HR]].
  left. apply HP.
  left. apply HP.
  left. apply HP'.
  right.
  split.
  apply HQ.
  apply HR. Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  intros H.
  inversion H.
  split.
  left. apply H0.
  left. apply H0.
  inversion H0 as [HQ HR].
  split.
  right. apply HQ.
  right. apply HR.
  intros H.
  inversion H as [[HP | HQ] [HP' | HR]].
  left. apply HP.
  left. apply HP.
  left. apply HP'.
  right.
  split.
  apply HQ.
  apply HR. Qed.

Theorem andb_true__and : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  intros b c H.
  destruct b.
    destruct c.
      apply conj.
      reflexivity.
      reflexivity.
    inversion H.
    inversion H. Qed.

Theorem and__andb_true : forall b c,
  b = true /\ c = true -> andb b c = true.
Proof.
  intros b c H.
  inversion H.
  rewrite H0.
  rewrite H1.
  reflexivity. Qed.

Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof.
  intros b c H.
  destruct b.
    destruct c.
    inversion H.
    right.
    reflexivity.
    left.
    reflexivity. Qed.

Theorem orb_true : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  intros b c H.
  destruct b.
  left.
  reflexivity.
  destruct c.
  right.
  reflexivity.
  inversion H. Qed.

Theorem orb_false : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof.
  intros b c H.
  destruct b.
    destruct c.
    inversion H.
    inversion H.
  split.
  reflexivity.
  destruct c.
  inversion H.
  reflexivity. Qed.
