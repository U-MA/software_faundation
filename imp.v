Require Export SfLib_J.
Require Export Omega.

Module AExp.

Inductive aexp : Type :=
|ANum : nat -> aexp
|APlus : aexp -> aexp -> aexp
|AMinus : aexp -> aexp -> aexp
|AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
|BTrue : bexp
|BFalse : bexp
|BEq : aexp -> aexp -> bexp
|BLe : aexp -> aexp -> bexp
|BNot : bexp -> bexp
|BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (e: aexp) : nat :=
  match e with
  |ANum n => n
  |APlus a1 a2 => (aeval a1) + (aeval a2)
  |AMinus a1 a2 => (aeval a1) - (aeval a2)
  |AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1 :
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof.
  reflexivity. Qed.

Fixpoint beval (e: bexp) : bool :=
  match e with
  |BTrue => true
  |BFalse => false
  |BEq a1 a2 => beq_nat (aeval a1) (aeval a2)
  |BLe a1 a2 => ble_nat (aeval a1) (aeval a2)
  |BNot b1 => negb (beval b1)
  |BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

Fixpoint optimize_Oplus (e: aexp) : aexp :=
  match e with
  |ANum n => ANum n
  |APlus (ANum O) e2 => optimize_Oplus e2
  |APlus e1 e2 =>
      APlus (optimize_Oplus e1) (optimize_Oplus e2)
  |AMinus e1 e2 =>
      AMinus (optimize_Oplus e1) (optimize_Oplus e2)
  |AMult e1 e2 =>
      AMult (optimize_Oplus e1) (optimize_Oplus e2)
  end.

Example test_optimize_Oplus :
  optimize_Oplus (APlus (ANum 2)
    (APlus (ANum 0)
      (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

Theorem optimize_Oplus_sound : forall e,
  aeval (optimize_Oplus e) = aeval e.
Proof.
  intros e.
  induction e.
  Case "ANum".
    reflexivity.
  Case "APlus".
    destruct e1.
    SCase "e1 = ANum n".
      destruct n.
      SSCase "n = 0".
        simpl.
        apply IHe2.
      SSCase "n <> 0".
        simpl.
        rewrite IHe2.
        reflexivity.
    SCase "e1 = APlus e1_1 e1_2".
      simpl.
      simpl in IHe1.
      rewrite IHe1.
      rewrite IHe2.
      reflexivity.
    SCase "e1 = AMinus e1_1 e1_2".
      simpl.
      simpl in IHe1.
      rewrite IHe1.
      rewrite IHe2.
      reflexivity.
    SCase "e1 = AMult e1_1 e1_2".
      simpl.
      simpl in IHe1.
      rewrite IHe1.
      rewrite IHe2.
      reflexivity.
  Case "AMinus".
    simpl.
    rewrite IHe1.
    rewrite IHe2.
    reflexivity.
  Case "AMult".
    simpl.
    rewrite IHe1.
    rewrite IHe2.
    reflexivity. Qed.

Lemma foo : forall n, ble_nat O n = true.
Proof.
  intros.
  destruct n.
    simpl.
    reflexivity.
    simpl.
    reflexivity. Qed.

Lemma foo' : forall n, ble_nat O n = true.
Proof.
  intros.
  destruct n;
  simpl;
  reflexivity. Qed.

Theorem optimize_Oplus_sound' : forall e,
  aeval (optimize_Oplus e) = aeval e.
Proof.
  intros e.
  induction e;
  try (simpl; rewrite IHe1; rewrite IHe2; reflexivity).
  Case "ANum".
    reflexivity.
  Case "APlus".
    destruct e1;
    try (simpl; simpl in IHe1; rewrite IHe1; rewrite IHe2; reflexivity).
  SCase "e1 = ANum n".
    destruct n;
    simpl;
    rewrite IHe2;
    reflexivity. Qed.

Theorem optimize_Oplus_sound'' : forall e,
  aeval (optimize_Oplus e) = aeval e.
Proof.
  intros e.
  induction e;
  try (simpl; rewrite IHe1; rewrite IHe2; reflexivity);
  try reflexivity.
  Case "APlus".
    destruct e1;
    try (simpl; simpl in IHe1; rewrite IHe1;
      rewrite IHe2; reflexivity).
    SCase "e1 = ANum n".
      destruct n;
      simpl;
      rewrite IHe2;
      reflexivity. Qed.

Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult" ].

Theorem optimize_Oplus_sound''' : forall e,
  aeval (optimize_Oplus e) = aeval e.
Proof.
  intros e.
  aexp_cases (induction e) Case;
    try (
      simpl;
      rewrite IHe1;
      rewrite IHe2;
      reflexivity);
    try reflexivity.
  Case "APlus".
    aexp_cases (destruct e1) SCase;
      try(
      simpl;
      simpl in IHe1;
      rewrite IHe1;
      rewrite IHe2;
      reflexivity).
    SCase "ANum".
      destruct n;
      simpl;
      rewrite IHe2;
      reflexivity. Qed.

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros.
  omega.
Qed.

Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
| E_ANum : forall (n:nat),
    aevalR (ANum n) n
| E_APlus : forall (e1 e2:aexp) (n1 n2:nat),
    aevalR e1 n1 ->
    aevalR e2 n2 ->
    aevalR (AMinus e1 e2) (n1 - n2)
| E_AMult : forall (e1 e2:aexp) (n1 n2:nat),
    aevalR e1 n1 ->
    aevalR e2 n2 ->
    aevalR (AMult e1 e2) (n1 * n2).

Notation "e || n" := (aevalR e n) : type_scope.

End aevalR_first_try.

Reserved Notation "e '||' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
| E_ANum : forall (n:nat),
    (ANum n) || n
| E_APlus : forall (e1 e2:aexp) (n1 n2:nat),
    (e1 || n1) -> (e2 || n2) -> (APlus e1 e2) || (n1 + n2)
| E_AMinus : forall (e1 e2:aexp) (n1 n2:nat),
    (e1 || n1) -> (e2 || n2) -> (AMinus e1 e2) || (n1 - n2)
| E_AMult : forall (e1 e2:aexp) (n1 n2:nat),
    (e1 || n1) -> (e2 || n2) -> (AMult e1 e2) || (n1 * n2)

where "e '||' n" := (aevalR e n) : type_scope.

Tactic Notation "aevalR_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_ANum" | Case_aux c "E_APlus"
  | Case_aux c "E_AMinus" | Case_aux c "E_AMult" ].

Theorem aeval_iff_aevalR : forall a n,
  (a || n) <-> aeval a = n.
Proof.
  split.
  Case "->".
    intros H.
    aevalR_cases (induction H) SCase; simpl.
    SCase "E_ANum".
      reflexivity.
    SCase "E_APlus".
      rewrite IHaevalR1.
      rewrite IHaevalR2.
      reflexivity.
    SCase "E_AMinus".
      rewrite IHaevalR1.
      rewrite IHaevalR2.
      reflexivity.
    SCase "E_AMult".
      rewrite IHaevalR1.
      rewrite IHaevalR2.
      reflexivity.
  Case "<-".
    generalize dependent n.
    aexp_cases (induction a) SCase;
      simpl; intros; subst.
    SCase "ANum".
      apply E_ANum.
    SCase "APlus".
      apply E_APlus.
        apply IHa1.
        reflexivity.
        apply IHa2.
        reflexivity.
    SCase "AMinus".
      apply E_AMinus.
        apply IHa1.
        reflexivity.
        apply IHa2.
        reflexivity.
    SCase "AMult".
      apply E_AMult.
        apply IHa1.
        reflexivity.
        apply IHa2.
        reflexivity. Qed.

Theorem aeval_iff_aevalR' : forall a n,
  (a || n) <-> aeval a = n.
Proof.
  split.
  Case "->".
    intros H;
    induction H;
    subst;
    reflexivity.
  Case "<-".
    generalize dependent n.
    induction a;
    simpl;
    intros;
    subst;
    constructor;
      try apply IHa1;
      try apply IHa2;
      reflexivity. Qed.
End AExp.

Module Id.

Inductive id : Type :=
  Id : nat -> id.

Definition beq_id X1 X2 :=
  match (X1, X2) with
    (Id n1, Id n2) => beq_nat n1 n2
  end.

Theorem beq_id_refl : forall X,
  true = beq_id X X.
Proof.
  intros.
  destruct X.
  apply beq_nat_refl. Qed.

Theorem beq_id_eq : forall i1 i2,
  true = beq_id i1 i2 -> i1 = i2.
Proof.
  intros i1 i2 H.
  destruct i1.
  destruct i2.
  unfold beq_id in H.
  apply beq_nat_eq in H.
  rewrite -> H.
  reflexivity. Qed.

Theorem beq_id_false_not_eq : forall i1 i2,
  beq_id i1 i2 = false -> i1 <> i2.
Proof.
  intros i1 i2 H.
  destruct i1.
  destruct i2.
  unfold beq_id in H.
  apply beq_nat_false in H.
  intro eq.
  apply H.
  inversion eq as [ID].
  reflexivity. Qed.

Theorem not_eq_id_false : forall i1 i2,
  i1 <> i2 -> beq_id i1 i2 = false.
Proof.
  intros.
  destruct i1.
  destruct i2.
  unfold beq_id.
  apply not_eq_beq_false.
  intro eq.
  apply H.
  inversion eq.
  reflexivity. Qed.

Theorem beq_id_sym : forall i1 i2,
  beq_id i1 i2 = beq_id i2 i1.
Proof.
Admitted.

Definition state := id -> nat.

Definition empty_state : state :=
  fun _ => O.

Definition update (st:state) (X:id) (n:nat) : state :=
  fun X' => if beq_id X X' then n else st X'.

Theorem update_eq : forall n X st,
  (update st X n) X = n.
Proof.
  intros.
  unfold update.
  rewrite <- (beq_id_refl X).
  reflexivity. Qed.

Theorem update_neq : forall V2 V1 n st,
  beq_id V2 V1 = false ->
  (update st V2 n) V1 = (st V1).
Proof.
  intros.
  unfold update.
  rewrite -> H.
  reflexivity. Qed.

Theorem update_example : forall (n:nat),
  (update empty_state (Id 2) n) (Id 3) = O.
Proof.
  unfold update.
  intros n.
  simpl.
  unfold empty_state.
  reflexivity. Qed.

Theorem update_shadow : forall x1 x2 k1 k2 (f:state),
  (update (update f k2 x1) k2 x2) k1 = (update f k2 x2) k1.
Proof.
