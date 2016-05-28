Require Export Poly_J.

Check (2 + 2 = 4).

Check (ble_nat 3 2 = false).

Check (2 + 2 = 5).

Theorem plus_2_2_is_4:
  2 + 2 = 4.
Proof.
  reflexivity. Qed.

Definition plus_fact:Prop:= 2 + 2 = 4.
Check plus_fact.

Theorem plus_fact_is_true:
  plus_fact.
Proof.
  reflexivity. Qed.

Definition starnge_prop1:Prop:=
  (2 + 2 = 5) -> (99 + 26 = 42).

Definition starnge_prop2:=
  forall n, (ble_nat n 17 = true) -> (ble_nat n 99 = true).

Definition even (n:nat) : Prop :=
  evenb n = true.

Check even.

Check (even 4).

Check (even 3).

Definition even_n__even_SSn(n:nat):Prop:=
  (even n) -> (even (S (S n))).

Definition between(n m o:nat):Prop:=
  andb (ble_nat n o) (ble_nat o m) = true.

Definition teen:nat -> Prop:=
  between 13 19.

Definition true_for_zero(P:nat->Prop):Prop:=
  P O.

Definition true_for_n__true_for_Sn(P:nat->Prop)(n:nat):Prop:=
  P n -> P (S n).

Definition preserved_by_S(P:nat->Prop):Prop:=
  forall n', P n' -> P (S n').

Definition true_for_all_numbers(P:nat->Prop):Prop:=
  forall n, P n.

Definition our_nat_induction(P:nat->Prop):Prop:=
  (true_for_zero P) ->
  (preserved_by_S P) ->
  (true_for_all_numbers P).

Inductive good_day:day -> Prop :=
| gd_sat:good_day saturday
| gd_sun:good_day sunday.

Theorem gds:good_day sunday.
Proof. apply gd_sun. Qed.

Inductive day_before:day -> day -> Prop :=
| db_tue:day_before tuesday monday
| db_wed:day_before wednesday tuesday
| db_thu:day_before thursday wednesday
| db_fri:day_before friday thursday
| db_sat:day_before saturday friday
| db_sun:day_before sunday saturday
| db_mon:day_before monday sunday.

Inductive fine_day_for_singing:day->Prop:=
| fdfs_any:forall d:day, fine_day_for_singing d.

Theorem fdfs_wed:fine_day_for_singing wednesday.
Proof. apply fdfs_any. Qed.

Definition fdfs_wed':fine_day_for_singing wednesday:=
  fdfs_any wednesday.

Check fdfs_wed.
Check fdfs_wed'.

Inductive ok_day:day->Prop:=
| okd_gd:forall d,
    good_day d ->
    ok_day d
| okd_before:forall d1 d2,
    ok_day d2 ->
    day_before d2 d1 ->
    ok_day d1.

(* ok_day saturday *)
Check okd_gd saturday gd_sat.

(* ok_day saturday -> day_before saturday friday
                   -> ok_day friday *)
Check okd_before friday saturday.

(* ok_day friday -> day_before friday thursday
                 -> ok_day thursday *)
Check okd_before thursday friday.

Definition okdw:ok_day wednesday:=
  okd_before wednesday thursday
    (okd_before thursday friday
      (okd_before friday saturday
        (okd_gd saturday gd_sat)
        db_sat)
      db_fri)
    db_thu.

Theorem okdw':ok_day wednesday.
Proof.
  apply okd_before with (d2:=thursday).
  apply okd_before with (d2:=friday).
  apply okd_before with (d2:=saturday).
  apply okd_gd.
  apply gd_sat.
  apply db_sat.
  apply db_fri.
  apply db_thu. Qed.

Print okdw'.

Definition okd_before2 :=
  forall d1 d2 d3,
  ok_day d3 ->
  day_before d2 d1 ->
  day_before d3 d2 ->
  ok_day d1.

Theorem okd_before2_valid:okd_before2.
Proof.
  unfold okd_before2.
  intros.
  apply okd_before with (d2:=d2).
  apply okd_before with (d2:=d3).
  apply H.
  apply H1.
  apply H0. Qed.

Definition okd_before2_valid' : okd_before2 :=
  fun (d1 d2 d3:day) =>
  fun (H: ok_day d3) =>
  fun (H0: day_before d2 d1) =>
  fun (H1: day_before d3 d2) =>
  okd_before d1 d2 (okd_before d2 d3 H H1) H0.

Print okd_before2_valid.

Check nat_ind.

Theorem mult_0_r':forall n:nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  Case "O".
    reflexivity.
  Case "S".
    simpl.
    intros n IHn.
    rewrite -> IHn.
    reflexivity. Qed.

Theorem plus_one_r':forall n:nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  Case "0".
    reflexivity.
  Case "S".
  intros n IHn.
  simpl.
  rewrite -> IHn.
  reflexivity. Qed.

Inductive yesno:Type:=
|yes:yesno
|no:yesno.

Check yesno_ind.

Inductive rgb:Type:=
|red:rgb
|green:rgb
|blue:rgb.
Check rgb_ind.

Inductive natlist:Type:=
|nnil:natlist
|ncons:nat->natlist->natlist.
Check natlist_ind.

Inductive natlist1:Type:=
|nnil1:natlist1
|nsnoc1:natlist1->nat->natlist1.
Check natlist1_ind.

Inductive ExSet:Type:=
|con1:bool->ExSet
|con2:nat->ExSet->ExSet.

Check ExSet_ind.

Inductive list(X:Type):Type:=
|nil:list X
|cons:X -> list X -> list X.
Check list_ind.

Inductive tree(X:Type):Type:=
|leaf:X -> tree X
|node:tree X -> tree X -> tree X.
Check tree_ind.

Inductive mytype(X:Type):Type:=
|constr1:X -> mytype X
|constr2:nat -> mytype X
|constr3:mytype X -> nat -> mytype X.
Check mytype_ind.

Inductive foo(X Y:Type):Type:=
|bar: X -> foo X Y
|baz: Y -> foo X Y
|quux: (nat -> foo X Y) -> nat -> foo X Y.
Check foo_ind.

Inductive foo'(X:Type):Type:=
|C1:list X -> foo' X -> foo' X
|C2:foo' X.
Check foo'_ind.

Definition P_mOr(n:nat):Prop:=
  n * 0 = 0.

Definition P_mOr':nat->Prop:=
  fun n => n * 0 = 0.

Theorem mult_O_r'':forall n:nat,
  P_mOr n.
Proof.
  apply nat_ind.
  Case "n = 0".
    reflexivity.
  Case "n = S n".
    unfold P_mOr.
    simpl.
    intros n' IHn'.
    apply IHn'.
Qed.

Inductive ev:nat->Prop:=
|ev_O:ev O
|ev_SS:forall n:nat, ev n -> ev (S (S n)).

Theorem four_ev':
  ev 4.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_O.

Definition four_ev: ev 4 :=
  ev_SS 2 (ev_SS 0 ev_O).

Definition ev_plus4:forall n, ev n -> ev (4 + n):=
  fun (n:nat)(H:ev n) => ev_SS (S (S n)) (ev_SS n H).

Print ev_plus4.

Theorem ev_plus4':forall n,
  ev n -> ev (4 + n).
Proof.
  intros n H.
  apply ev_SS.
  apply ev_SS.
  apply H. Qed.

Theorem double_even:forall n,
  ev (double n).
Proof.
  induction n as [|n'].
  (* Case "n = 0". *)
    apply ev_O.
  (* Case "n = n'". *)
    simpl.
    apply ev_SS.
    apply IHn'. Qed.
Print double_even.

Theorem ev_minus2:forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [|n' E'].
  Case "E = ev_O".
    simpl.
    apply ev_O.
  Case "E = ev_SS n' E'".
    simpl.
    apply E'. Qed.

Theorem ev_minus2_n:forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct n as [|n'].
  Case "n = 0".
    simpl.
    apply ev_O.
  Case "n = S n'".
    simpl.
Admitted.
(* たぶん、無理 *)

Theorem ev_even:forall n,
  ev n -> even n.
Proof.
  intros n E.
  induction E as [|n' E'].
  Case "E = ev_O".
    unfold even.
    reflexivity.
  Case "E = ev_SS n' E'".
    unfold even.
    apply IHE'. Qed.

Theorem ev_even_n:forall n,
  ev n -> even n.
Proof.
  intros n E.
  induction n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    destruct n' as [|n''].
    SCase "n' = 0".
      inversion E.
    SCase "n' = S n''".
      inversion E.
      unfold even.
      simpl.
Admitted.

Theorem SSev_ev:forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [|n' E'].
  apply E'. Qed.

Theorem SSSSev_even:forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n E.
  inversion E as [|n' E'].
  inversion E' as [|n'' E''].
  apply E''. Qed.

Theorem even5_nonsense:
  ev 5 -> 2 + 2 = 9.
Proof.
  intros H.
  inversion H as [|n' H'].
  inversion H' as [|n'' H''].
  inversion H''. Qed.

Theorem ev_minus2':forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E as [|n' E'].
  (* E = ev_O *)
    simpl.
    apply ev_O.
  (* E = ev_SS n' E' *)
    simpl.
    apply E'. Qed.

Inductive MyProp:nat->Prop:=
|MyProp1:MyProp 4
|MyProp2:forall n:nat, MyProp n -> MyProp (4 + n)
|MyProp3:forall n:nat, MyProp (2 + n) -> MyProp n.

Theorem MyProp_ten:MyProp 10.
Proof.
  apply MyProp3.
  simpl.
  assert (12 = 4 + 8) as H12.
    reflexivity.
    rewrite -> H12.
    apply MyProp2.
    assert (8 = 4 + 4) as H8.
      reflexivity.
      rewrite -> H8.
      apply MyProp2.
      apply MyProp1. Qed.

Theorem MyProp_0:MyProp 0.
Proof.
  apply MyProp3.
  simpl.
  apply MyProp3.
  simpl.
  apply MyProp1. Qed.

Theorem MyProp_plustwo:
  forall n:nat, MyProp n -> MyProp (S (S n)).
Proof.
  intros n H.
  apply MyProp3.
  simpl.
  apply MyProp2.
  apply H. Qed.

Theorem MyProp_ev:forall n:nat,
  ev n -> MyProp n.
Proof.
  intros n E.
  induction E as [|n' E'].
  Case "E = ev_0".
    apply MyProp_0.
  Case "E = ev_SS n' E'".
    apply MyProp_plustwo.
    apply IHE'. Qed.

Theorem ev_MyProp:forall n:nat,
  MyProp n -> ev n.
Proof.
  intros n E.
  induction n as [|n'].
  Case "n = 0".
    apply ev_O.
  Case "n = S n'".
Admitted.
