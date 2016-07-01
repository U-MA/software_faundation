Require Export Imp_J.

(* 定義 *)

Definition aequiv (a1 a2:aexp) : Prop :=
  forall (st:state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2:bexp) : Prop :=
  forall (st:state),
    beval st b1 = beval st b2.

Definition cequiv (c1 c2:com) : Prop :=
  forall (st st':state),
    (c1 / st || st') <-> (c2 / st || st').

(* 練習問題: pairs_equiv
   一旦飛ばす *)

(* 例 *)

Theorem aequiv_example :
  aequiv (AMinus (AId X) (AId X)) (ANum O).
Proof.
  intros st.
  simpl.
  apply minus_diag.
Qed.

Theorem bequiv_example :
  bequiv (BEq (AMinus (AId X) (AId X)) (ANum O)) BTrue.
Proof.
  intros st.
  unfold beval.
  rewrite aequiv_example.
  reflexivity.
Qed.

Theorem skip_left : forall c,
  cequiv (SKIP; c) c.
Proof.
  intros c st st'.
  split; intros H.
  Case "->".
    inversion H. subst.
    inversion H2. subst.
    assumption.
  Case "<-".
    apply E_Seq with st.
    apply E_Skip.
    assumption.
Qed.

Theorem skip_right : forall c,
  cequiv (c; SKIP) c.
Proof.
  Admitted.

Theorem IFB_true_simple : forall c1 c2,
  cequiv
    (IFB BTrue THEN c1 ELSE c2 FI)
    c1.
Proof.
  intros c1 c2.
  split; intros H.
  Case "->".
    inversion H; subst. assumption. inversion H5.
  Case "<-".
    apply E_IfTrue. reflexivity. assumption. Qed.

Theorem IFB_true : forall b c1 c2,
  bequiv b BTrue ->
  cequiv
    (IFB b THEN c1 ELSE c2 FI)
    c1.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  Case "->".
    inversion H; subst.
    SCase "b evaluates to true".
      assumption.
    SCase "b evaluates to false (contradiction)".
      rewrite Hb in H5.
      inversion H5.
  Case "<-".
    apply E_IfTrue; try assumption.
    rewrite Hb. reflexivity. Qed.

(* 練習問題 IFB_false *)
Theorem IFB_false : forall b c1 c2,
  bequiv b BFalse ->
  cequiv
    (IFB b THEN c1 ELSE c2 FI)
    c2.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  Case "->".
    inversion H.
    rewrite Hb in H5.
    inversion H5.
    apply H6.
  Case "<-".
    apply E_IfFalse.
    apply Hb.
    apply H. Qed.

(* 練習問題 swap_if_branches *)
Theorem swap_if_branches : forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  Admitted.

Theorem WHILE_false : forall b c,
  bequiv b BFalse ->
  cequiv
    (WHILE b DO c END)
    SKIP.
Proof.
  intros b c Hb.
  split; intros H.
  Case "->".
    inversion H; subst.
    SCase "E_WhileEnd".
      apply E_Skip.
    SCase "E_WhileLoop".
      rewrite Hb in H2.
      inversion H2.
  Case "<-".
    inversion H; subst.
    apply E_WhileEnd.
    rewrite Hb.
    reflexivity. Qed.

Lemma WHILE_true_nonterm : forall b c st st',
  bequiv b BTrue ->
  ~( (WHILE b DO c END) / st || st').
Proof.
  intros b c st st' Hb.
  intros H.
  remember (WHILE b DO c END) as cw.
  ceval_cases (induction H) Case;
  inversion Heqcw; subst; clear Heqcw.
  Case "E_WhileEnd". rewrite Hb in H. inversion H.
  Case "E_WhileLoop". apply IHceval2. reflexivity. Qed.

(* 練習問題 WHILE_true *)
Theorem WHILE_true : forall b c,
  bequiv b BTrue ->
  cequiv
    (WHILE b DO c END)
    (WHILE BTrue DO SKIP END).
Proof.
  intros b c Hb.
  split; intros H.
  Case "->".
Admitted.

Theorem loop_unrolling : forall b c,
  cequiv
    (WHILE b DO c END)
    (IFB b THEN (c; WHILE b DO c END) ELSE SKIP FI).
Proof.
  intros b c st st'.
  split; intros Hce.
  Case "->".
    inversion Hce; subst.
    SCase "loop doesn't run".
      apply E_IfFalse.
      assumption.
      apply E_Skip.
    SCase "loop runs".
      apply E_IfTrue.
      assumption.
      apply E_Seq with (st' := st'0).
      assumption.
      assumption.
  Case "<-".
    inversion Hce; subst.
    SCase "loop runs".
      inversion H5; subst.
      apply E_WhileLoop with (st' := st'0).
      assumption. assumption. assumption.
    SCase "loop doesn't run".
      inversion H5; subst. apply E_WhileEnd. assumption. Qed.

(* 練習問題 seq_assoc *)

Theorem seq_assoc : forall c1 c2 c3,
  cequiv ((c1;c2);c3) (c1;(c2;c3)).
Proof.
  Admitted.
