Require Import Arith Omega.

Section Wf_nat.
Variable A:Type.
Variable f:A -> nat.
Definition ltof x y := f x < f y.

Theorem wf_ltof : well_founded ltof.
red in |-*.
cut (forall n a, f a < n -> Acc ltof a).
intros H a.
eapply H.
apply lt_n_Sn.
induction n.
intros a H; contradict H; auto with arith.
intros a ltSma.
split.
unfold ltof.
intros b ltfafb.
apply IHn.
eapply lt_le_trans.
eassumption.
auto with arith.

Theorem well_founded_ltof : well_founded ltof.
Proof.
  red in |- *.
  cut (forall n (a:A), f a < n -> Acc ltof a).
  intros H a; apply (H (S (f a))); auto with arith.
  induction n.
  intros; absurd (f a < 0); auto with arith.
  intros a ltSma.
  apply Acc_intro.
  unfold ltof in |- *; intros b ltfafb.
  apply IHn.
  apply lt_le_trans with (f a); auto with arith.
Defined.
