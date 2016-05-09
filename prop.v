Require Export Poly_J.

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
