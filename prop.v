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

Definition even (n:nat) : Prop :=
  evenb n = true.

Check even.

Check (even 4).

Check (even 3).

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
Check natlist.

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
