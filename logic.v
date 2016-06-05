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

Inductive False : Prop := .

Theorem False_implies_nonsense:
  False -> 2 + 2 = 5.
Proof.
  intros contra.
  inversion contra. Qed.

Theorem nonsense_implies_False:
  2 + 2 = 5 -> False.
Proof.
  intros contra.
  inversion contra. Qed.

Theorem ex_falso_quodlibet : forall P : Prop,
  False -> P.
Proof.
  intros P contra.
  inversion contra. Qed.

Inductive True : Prop :=
|T : True.

Definition not (P : Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Theorem not_False:
  ~ False.
Proof.
  unfold not.
  intros H.
  inversion H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~ P) -> Q.
Proof.
  intros P Q H.
  inversion H as [HP HNA].
  unfold not in HNA.
  apply HNA in HP.
  inversion HP. Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H.
  unfold not.
  intros G.
  apply G.
  apply H. Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~ P).
Proof.
  unfold not.
  intros P H.
  inversion H.
  apply H1 in H0.
  apply H0. Qed.

Theorem five_not_even : ~ ev 5.
Proof.
  unfold not.
  intros Hev5.
  inversion Hev5.
  inversion H0.
  inversion H2. Qed.

Theorem ev_not_ev_S : forall n,
  ev n -> ~ ev (S n).
Proof.
  unfold not.
  intros n H.
  induction H.
  intros H.
  inversion H.
  intros H'.
  inversion H'.
  apply IHev in H1.
  apply H1. Qed.

Theorem classic_double_neg : forall P : Prop,
  ~~P -> P.
Proof.
  intros P H.
  unfold not in H.
Admitted.

Notation "x <> y" := (~ (x = y)) : type_scope.

Theorem not_false_then_true : forall b : bool,
  b <> false -> b = true.
Proof.
  intros b H.
  destruct b.
  reflexivity.
  unfold not in H.
  apply ex_falso_quodlibet.
  apply H.
  reflexivity. Qed.

Theorem not_eq_beq_false : forall n n' : nat,
  n <> n' -> beq_nat n n' = false.
Proof.
  Admitted.

Theorem beq_false_not_eq : forall n m,
  false = beq_nat n m -> n <> m.
Proof.
  Admitted.

Inductive ex (X:Type) (P:X->Prop):Prop:=
  ex_intro:forall(witness:X), P witness -> ex X P.

Definition some_nat_is_even : Prop :=
  ex nat ev.

Definition snie : some_nat_is_even :=
  ex_intro _ ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.

Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness := 2).
  reflexivity. Qed.

Example exists_example_1' : exists n,
  n + (n * n) = 6.
Proof.
  exists 2.
  reflexivity. Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m Hm].
  exists (2 + m).
  apply Hm. Qed.

Theorem dist_not_exists : forall (X:Type) (P:X->Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P PH NH.
  inversion NH as [x NP].
  apply NP.
  apply PH. Qed.

Module MyEqualilty.

Inductive eq (X:Type):X->X->Prop:=
  refl_equal:forall x, eq X x x.

Notation "x = y" := (eq _ x y)
  (at level 70, no associativity) : type_scope.

Inductive eq' (X:Type) (x:X) : X -> Prop :=
  refl_equal' : eq' X x x.

Notation "x =' y" := (eq' _ x y)
  (at level 70, no associativity) : type_scope.

Theorem two_defs_of_eq_coincide : forall (X:Type) (x y:X),
  x = y <-> x =' y.
Proof.
  intros.
  split.
  intros H.
  inversion H as [x' y' T].
  apply refl_equal'.
  intros H.
  inversion H as [T].
  apply refl_equal. Qed.

Definition four : 2 + 2 = 1 + 3 :=
  refl_equal nat 4.
Definition singleton : forall (X:Set) (x:X), []++[x] = x::[] :=
  fun (X:Set) (x:X) => refl_equal (list X) [x].

End MyEqualilty.

Module LeFirstTry.

Inductive le : nat -> nat -> Prop :=
|le_n : forall n, le n n
|le_S : forall n m, (le n m) -> (le n (S m)).

End LeFirstTry.

Inductive le (n : nat) : nat -> Prop :=
|le_n : le n n
|le_S : forall m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Theorem test_le1 : 3 <= 3.
Proof.
  apply le_n. Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  apply le_S.
  apply le_S.
  apply le_S.
  apply le_n. Qed.

Theorem test_le3 :
  ~ (2 <= 1).
Proof.
  intros H.
  inversion H.
  inversion H1. Qed.

Definition lt (n m : nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n : nat, square_of n (n * n).

Inductive next_nat (n : nat) : nat -> Prop :=
|nn : next_nat n (S n).

Inductive next_even (n : nat) : nat -> Prop :=
|ne_1 : ev (S n) -> next_even n (S n)
|ne_2 : ev (S (S n)) -> next_even n (S (S n)).

Theorem O_le_n : forall n,
  O <= n.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    apply le_n.
  Case "n = S n'".
    apply le_S.
    apply IHn'. Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m H.
  induction H.
    apply le_n.
    apply le_S.
    apply IHle. Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m.
  generalize dependent n.
  induction m.
  Case "m = 0".
  intros n H.
  inversion H as [eq|m' L].
    apply le_n.
    inversion L.
  intros n H.
Admitted.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a b.
  induction a as [|a'].
    simpl.
    apply O_le_n.
Admitted.
