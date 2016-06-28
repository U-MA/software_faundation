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
