Require Import Logic.
Section Hoge.

Goal forall A P (Q:Prop), ((exists x:A, P x) -> Q) <-> forall x:A, P x -> Q.
split.
  intros H x H0.
  apply H.
  eauto.

  intros H [x H0].
  eapply H.
  eauto.
Qed.

Section iff_imp_eq.

Hypothesis iff_imp_eq : forall P Q, (P<->Q)->P=Q.

Theorem hoge : forall (P:Type->Prop) (Q:Prop), (forall x, P x -> Q) -> (forall x, ~ Q -> ~P x).
intros.
contradict H0.
eapply H.
eauto.