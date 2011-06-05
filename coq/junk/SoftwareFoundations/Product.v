Require Import Ensembles.

Section Product.
Variable U V:Type.

Inductive Prod (A:Ensemble U) (B:Ensemble V) : Ensemble (U*V) :=
  Prod_intro a b : In _ A a -> In _ B b -> Prod A B (pair a b).

Theorem In_Prod A B a b : In _ A a -> In _ B b -> In _ (Prod A B) (pair a b).
intros.
split.
auto.
auto.
Qed.
