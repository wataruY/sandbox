Require Import Arith List Omega.


Fixpoint duplicate {A:Type} n (x:A) : list A :=
  match n with
     | 0 => nil
     | S p => x :: duplicate p x
  end.
Theorem duplicate_length {A:Type} n (a:A) : length (duplicate n a) = n.
induction n.
auto.
simpl.
rewrite IHn.
auto.
Qed.


Section Pigeonhole.

Variable A:Type.


Inductive Any {A:Type} (P:A -> Prop) : list A -> Prop :=
  | AnyCons x xs : P x \/ Any P xs -> Any P (x :: xs).

Let singleton {A:Type} (x:A) := cons x nil.
Implicit Arguments singleton [A].

Inductive Split : nat -> list A -> list (list A) -> Prop := 
  | SplitNil n : Split n nil (duplicate n nil)
  | Split1 xs : Split 1 xs (singleton xs)
  | SplitCons1 n x xs xss :
    Split n xs xss -> Any (In x) xss ->
    Split n (x::xs) xss
  | SplitCons2 n x xs xss :
    Split n xs xss ->
    Split (S n) (x::xs) (singleton x::xss).
 
Theorem Split_0_nil : Split 0 nil nil.
apply SplitNil.
Qed.

Theorem Split_0_eq_nil xs : Split 0 xs nil -> xs = nil.
intro H.
inversion H.
trivial.
inversion H1.
Qed.

Theorem Split_nil n xs : Split n xs nil -> xs = nil /\ n = 0.
intro H; inversion H.
induction n.
auto.
split.
trivial.
simpl in H3.
discriminate.
inversion H1.
Qed.

Theorem Split_length n xs xss : Split n xs xss -> length xss = n.
intro H; induction H.
rewrite duplicate_length.
auto.
auto.
assumption.
simpl.
f_equal; auto.
Qed.

Theorem Split_cons_inv_length n xs ys yss : Split n xs (ys :: yss) -> n > 0.
intro H.
assert (H0 := Split_length _ _ _ H).
simpl in H0.
rewrite <- H0.
auto with arith.
Qed.

Theorem pred_exists n m : m > 0 -> m = S n -> exists p, S p = m /\ p = n.
intros.
subst.
eauto.
Qed.

Theorem lt_case m n : n < S m -> n = m \/ n < m.
intros.
induction n.
induction m.
auto.
right.
auto with arith.
cut (n < S m).
intro H'.
destruct (IHn H').
subst.
contradict H.
auto with arith.
assert (H1 := lt_le_S _ _ H0).
case (le_lt_eq_dec _ _ H1); auto with arith.
omega.
Qed.

Theorem pigeonhole n xs xss : Split n xs xss -> length xss < length xs ->
                                Any (fun xs => length xs >= 2) xss.
intro H.
induction H.
simpl.
rewrite duplicate_length.
intro H; contradict H; auto with arith.
simpl.
intro Hlen.
constructor.
left; omega.
simpl.
intro Hlen.
case (lt_case _ _ Hlen).
intro Heq.
destruct H0.
destruct H0.
constructor.
