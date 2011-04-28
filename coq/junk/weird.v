Require Import Arith.
Section weird_induc_proof.

Variable (P:nat->Prop)
         (f:nat->nat).
Hypothesis (f_strict_mono:forall n p:nat, n<p -> f n < f p)
           (f_0 : 0 < f 0)

           (P0 : P 0)
           (P_Sn_n : forall n:nat, P (S n) -> P n)
           (f_P : forall n:nat, P n -> P (f n)).

Theorem P_le_n : forall m n:nat, n <= m -> P m -> P n.
intros m n H.
elim H.
trivial.
intros.
eapply H1.
apply P_Sn_n.
assumption.
Qed.

Fixpoint iterate n x :=
  match n with
    | 0 => x
    | S p => f (iterate p x)
  end.

Theorem iterate_lt n : n <= iterate n 0.
induction n.
trivial.
cut (iterate n 0 < iterate (S n) 0).
  simpl.
  intro H.
  apply lt_le_S.
  case (le_lt_eq_dec _ _ IHn).
    intros H'.
    eapply lt_trans.
    eassumption.
    assumption.
    intro.
    rewrite e at  1.
    assumption.
elim n.
simpl.
assumption.
simpl.
intros.
apply f_strict_mono.
assumption.
Qed.

Theorem P_iter : forall n, P (iterate n 0).
induction n.
assumption.
simpl.
apply f_P.
assumption.
Qed.

Theorem weird_induc : forall n:nat, P n.
intro n.
eapply P_le_n.
apply iterate_lt.
apply P_iter.
Qed.