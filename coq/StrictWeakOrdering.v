Require Import Relations Setoid.

Section Sort.

Variable (A : Type).

Section Relation.
  Variable (R : relation A).

  Definition equal := forall x y, ~ R x y -> ~ R y x -> x = y.
  Definition totality := forall x y, R x y \/ R y x.
  Definition irreflexive := forall x, ~ R x x.
  Definition asymmetric := forall x y, R x y -> ~ R y x.

  Theorem asym_imply_irrefl (H : asymmetric) : irreflexive.
  intro x.
  intro H'.
  eapply H; eauto.
  Qed.

  Theorem asym_imply_antisym (H : asymmetric) : antisymmetric _ R.
  intros x y H0 H1.
  contradict H1.
  apply H.
  assumption.
  Qed.

  Theorem antisym_irrefl_assym (Hanti : antisymmetric _ R) (Hirrefl : irreflexive) : asymmetric.
  intros x y Hxy.
  intro Hyx.
  assert (H := Hanti _ _ Hxy Hyx).
  contradict Hxy.
  subst.
  apply Hirrefl.
  Qed.

  Theorem asym_irrefl_antisym : antisymmetric _ R /\ irreflexive <-> asymmetric.
  split.
  intros [ Hanti Hirr ].
  eapply antisym_irrefl_assym; auto.
  intro; split.
  apply asym_imply_antisym; assumption.
  apply asym_imply_irrefl; assumption.
  Qed.
End Relation.

Section Order_Def.
  Record TotalOrder (R : relation A) :=
  { to_antisym : antisymmetric _ R
    ; to_trans : transitive _ R
    ; to_total : totality R
  }.
  Record StrictTotalOrder (R' R : relation A) :=
  { sto_to : TotalOrder R'
    ; sto1 x y : R x y <-> R' x y /\ x <> y
    ; sto_ic x y : R x y <-> ~ R' y x
  }.
End Order_Def.

Section Order_Theorems.

Variable (Le Lt : relation A).

Hypotheses (Le_antisym : antisymmetric _ Le)
           (Le_trans : transitive _ Le)
           (Le_total : totality Le)
           (Lt_sto : StrictTotalOrder Le Lt).
Let Lt_disj := sto1 _ _ Lt_sto.           
Let Lt_ic := sto_ic _ _ Lt_sto.

Theorem Lt_irrefl : irreflexive Lt.
intro x.
intro Hrefl.
destruct (proj1 (Lt_disj _ _) Hrefl) as [ _ H ].
contradict H; reflexivity.
Qed.

Theorem Lt_asymmetric : asymmetric Lt.
assert (Hanti : antisymmetric A Lt).
intros x y Hxy Hyx.
apply Le_antisym; apply Lt_disj; assumption.
apply asym_irrefl_antisym.
split; assumption || apply Lt_irrefl.
Qed.

Theorem Lt_trans : transitive _ Lt.
intros x y z Hxy Hyz.
apply Lt_disj.
split.
eapply Le_trans.
apply Lt_disj.
eauto.
apply Lt_disj.
assumption.
intro.
contradict Hxy.
subst.
apply Lt_asymmetric.
assumption.
Qed.

Theorem Lt_trichotomous_lt x y : x <> y /\ ~ Lt y x <-> Lt x y.
split.
intros [Hneq Hlt].
apply Lt_ic.
contradict Hlt.
apply Lt_ic.
intro H.
contradict Hneq.
apply Le_antisym; assumption.
intro Hlt.
destruct (proj1 (Lt_disj _ _) Hlt) as [ Hneq Hlt' ].
split.
assumption.
intro.
apply Lt_ic in H.
contradiction.
Qed.

Theorem Lt_trichitomous_gt x y : x <> y /\ ~ Lt x y <-> Lt y x.
split.
intros [Hneq Hgt].
apply Lt_ic.
intro.
contradict Hgt.
apply Lt_disj; split; assumption.
intros H.
split.
intro Heq.
contradict H.
subst.
apply Lt_irrefl.
apply Lt_asymmetric.
assumption.
Qed.

Require Import Classical.

Theorem not_lt_le x y : ~ Lt y x -> Le x y.
intro H.
apply NNPP.
intro H'.
eapply Lt_asymmetric.
apply Lt_ic.
eauto.
apply Lt_ic.
intro H''.
elim H.
apply Lt_ic.
assumption.
Qed.

Theorem Lt_trichitomous_eq x y : ~ Lt y x /\ ~ Lt x y <-> x = y.
split.
intro.
destruct H.
apply Le_antisym.
apply not_lt_le.
assumption.
apply not_lt_le.
assumption.
intro Heq.
subst.
split; apply Lt_irrefl.
Qed.