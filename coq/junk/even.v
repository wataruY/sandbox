Require Import Arith.

Inductive even : nat -> Prop :=
  | even0 : even 0
  | evenSS p : even p -> even (S (S p)).

Fixpoint test_even n : {even n}+{even (pred n)}.
induction n.
left; constructor.
case IHn.
tauto.
simpl.
case n.
auto.
simpl.
left.
constructor.
assumption.
Defined.

Theorem even_absurd n : even n -> ~ even (S n).
induction n.
intros.
intro H'.
inversion H'.
intros.
intro H''.
apply IHn.
inversion H''.
assumption.
assumption.
Qed.

Theorem neq_sym (A:Type) (x y : A) : x <> y -> y <> x.
intro H.
contradict H.
auto.
Qed.

Definition eq_dec (A:Type) := forall x y:A, {x=y}+{x<>y}.

Theorem nat_eq_dec : eq_dec nat.
intro x.
induction x; induction y.
left; auto.
case IHy.
intro; subst.
right; auto.
right; apply neq_sym; auto.
right; apply neq_sym; auto.
case IHy.
intro; subst.
right.
apply n_Sn.
intro H.
ecase (IHx y).
intro;subst;auto.
intro H'.
right.
auto.
Qed.

Definition pred_strong (n:nat) : {p | n = S p}+{n = 0}.
case n.
right;reflexivity.
intros p.
left.
exists p.
reflexivity.
Defined.

Definition pred_partial : forall n:nat, n<>0 -> nat.
intro n; case n.
intro h; elim h.
reflexivity.
intros p h'.
exact p.
Defined.

Theorem le_2_n_not_zero : forall n:nat, 2 <= n -> n <> 0.
intros n Hle; elim Hle; intros; discriminate.
Qed.
Theorem le_2_n_pred' :
    forall n:nat, 2<=n -> forall h:n<>0, pred_partial n h <> 0.
intros n Hle.
elim Hle.
intros; discriminate.
simpl.
intros.
apply le_2_n_not_zero.
assumption.
Qed.

Definition pred_partial_2' n : 2 <= n -> nat.
refine (fun h => (fun h':n<>0 => pred_partial (pred_partial n h') _) _).
apply le_2_n_pred'.
assumption.
apply le_2_n_not_zero.
assumption.
Defined.
