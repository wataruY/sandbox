Require Import Arith.

Fixpoint div2 (n:nat) : nat :=
  match n with
    | 0 => 0
    | 1 => 0
    | (S (S p)) => S (div2 p)
  end.

Theorem div2_le n : div2 n <= n.
cut (div2 n <= n /\ div2 (S n) <= S n).
tauto.
induction n.
auto.
split.
apply IHn.
simpl.
apply le_n_S.
apply le_S.
apply IHn.
Qed.

Fixpoint div3 (n:nat) : nat :=
  match n with
    | 0 => 0
    | 1 => 0
    | 2 => 0
    | (S (S (S p))) => S (div3 p)
  end.

Theorem div3_le n : div3 n <= n.
cut (div3 n <= n /\ div3 (S n) <= S n /\ div3 (S (S n)) <= S (S n)).
tauto.
induction n.
simpl.
auto.
split.
apply IHn.
split.
apply IHn.
simpl.
apply le_n_S.
apply le_S.
apply le_S.
apply IHn.
Qed.

Fixpoint mod2 n : nat :=
  match n with
    | 0 => 0
    | 1 => 1
    | S (S p) => mod2 p
  end.

Definition mod2_prop := fun n => n = 2 * div2 n + mod2 n.

Theorem mod2_prop_pr n : mod2_prop n.
cut (mod2_prop n /\ mod2_prop (S n)).
tauto.
unfold mod2_prop.
induction n.
auto.
split.
destruct IHn.
pattern (S n) at 1.
rewrite H0.
reflexivity.
simpl.
f_equal.
rewrite plus_0_r.
rewrite <- plus_n_Sm.
rewrite  plus_Sn_m.
f_equal.
rewrite mult_succ_l in *|-.
rewrite mult_1_l in *|-.
apply IHn.
Qed.

Fixpoint fib n : nat :=
  match n with
     | 0 => 1
     | 1 => 1
     | S (S p as q) => fib p + fib q
  end.

Fixpoint fib' n : nat*nat :=
  match n with
    | 0 => pair 1 1
    | S p => match fib' p with
               | (x,y) => (y,x+y)
             end
  end.

Definition fib_prop := fun n => fib n = snd (fib' n).

Theorem fib_red n : fib (S (S n)) =  fib n + fib (S n).
case n.
reflexivity.
auto.
Qed.


Theorem fib_corr n : fib' n = (fib n, fib (S n)).
elim n.
reflexivity.
intros m H.
apply injective_projections.
simpl.
rewrite H.
simpl; auto.
simpl.
rewrite H.
simpl.
auto.
Qed.

Theorem nat_2_ind : forall P:nat -> Prop, P 0 -> P 1 -> (forall n, P n -> P (S (S n))) -> forall n, P n.
intros P H0 H1 Hrec n.
cut (P n /\ P (S n)).
tauto.
induction n.
auto.
destruct IHn as [Hn HSn].
split.
assumption.
apply Hrec.
assumption.
Qed.

Theorem div2_le' n : div2 n <= n.
induction n using nat_2_ind.
auto.
auto.
simpl.
apply le_n_S.
apply le_S.
assumption.
Qed.

Theorem nat_3_ind : forall P:nat -> Prop,
                    P 0 -> P 1 -> P 2 ->
                    (forall n, P n -> P (S (S (S n)))) ->
                    forall n, P n.
intros P H0 H1 H2 Hrec n.
cut (P n /\ P (S n) /\ P (S (S n))).
tauto.
induction n; auto.
destruct IHn as [Hp [Hp1 Hp2]].
split; auto.
Qed.

Theorem nat_4_ind : forall P:nat -> Prop,
                    P 0 -> P 1 -> P 2 -> P 3 ->
                    (forall n, P n -> P (S (S (S (S n))))) ->
                    forall n, P n.
intros P H0 H1 H2 H3 Hrec n.
cut (P n /\ P (S n) /\ P (S (S n)) /\ P (S (S (S n)))).
tauto.
induction n; auto.
repeat match goal with
  | [ H : _ /\ _ |- _ ] => destruct H
  | [  |- _ /\ _ ] => split
end; auto.
Qed.

Fixpoint div2'_aux n : nat*nat :=
  match n with
    | 0 => (0, 0)
    | S p => let (x,y) := div2'_aux p in (y, S x)
  end.

Definition mult2 n := n+n.

Theorem zero_one_dec n : n <= 1 -> {n=0}+{n=1}.
induction n.
left; auto.
intro H.
rewrite (eq_S n 0).
auto.
apply le_S_n in H.
apply le_lt_eq_dec in H.
destruct H.
contradict l.
auto with arith.
assumption.
Qed.

Definition div2_mod2 : forall n, {q:nat & {r | n = (mult2 q) + r /\ r <= 1}}.
induction n.
exists 0; exists 0; eauto.
destruct IHn as [q' [r' [H1 H2]]].
case (zero_one_dec r' H2).
intro Hr.
subst.
esplit.
esplit.
split.
eauto.
auto with arith.
intro.
subst.
clear.
esplit; esplit; split.
rewrite plus_n_Sm.
unfold mult2 at 1.
cutrewrite (q' + q' + 2 = mult2 (S q')).
eauto.
unfold mult2.
ring.
auto with arith.
Defined.

(* Extraction div2_mod2. *)

Fixpoint plus'' n m {struct m} : nat :=
  match m with 0 => n | S p => plus'' (S n) p end.

Require Import Relations.

Theorem plus''_Sn_m : forall n m, S (plus'' n m)= plus'' (S n) m.
intros n m.
generalize n; clear n; elim m; simpl.
reflexivity.
intros p Hrec n0.
rewrite Hrec.
reflexivity.
Qed.

Fixpoint plus' n m : nat :=
  match m with 0 => n | S p => S (plus' n p) end.

Definition BinOp (A : Type) := A -> A -> A.

Definition Associative (A : Type) (f : BinOp A) := forall x y z, f x (f y z) = f (f x y) z.

Theorem plus'_assoc : Associative _ plus'.
unfold Associative.
induction z.
auto.
simpl.
f_equal.
rewrite IHz.
auto.
Qed.

Theorem plus''_assoc : Associative _ plus''.
intros x y z.
generalize x y; clear x y.
induction z.
auto.
intros x y.
simpl.
rewrite IHz.
revert IHz.
generalize x z; clear x z.
induction y.
auto.
intros.
simpl.
rewrite <- IHy.
reflexivity.
intros x0 y0.
rewrite <- IHz.
reflexivity.
Qed.

Fixpoint fib_gen (a b n : nat) : nat :=
  match n with
    | O => a
    | S p => fib_gen b (a+b) p
  end.

Theorem fib_gen_S a b n : fib_gen a b (S n) = fib_gen b (a+b) n.
auto.
Qed.

Theorem fib_ind : forall (P:nat -> Prop), P 0 -> P 1 -> (forall n, P n -> P (S n) -> P (S (S n))) -> forall n, P n.
intros P H0 H1 Hrec n.
cut (P n /\ P (S n)).
tauto.
induction n.
auto.
split.
apply IHn.
apply Hrec; apply IHn.
Qed.

Theorem fib_gen_SS a b n : fib_gen a b (S (S n)) = fib_gen a b (S n) + fib_gen a b n.
generalize a,b; clear a b.
induction n.
simpl.
auto with arith.
intros a b.
rewrite fib_gen_S at 1.
pattern (fib_gen a b (S (S n))).
rewrite fib_gen_S.
pattern (fib_gen a b (S n)).
rewrite fib_gen_S.
set (c := a+b).
apply IHn.
Qed.

Definition fib_tail : nat -> nat := fib_gen 1 1.

Theorem fib_tail_fib n : fib_tail n = fib n.
induction n using fib_ind; auto.
unfold fib_tail.
rewrite fib_gen_SS.
fold fib_tail.
rewrite fib_red.
rewrite IHn0.
rewrite IHn.
auto with arith.
Qed.