
Definition nandb (b c:bool) : bool :=
  match b,c with
    | true,true => false
    | _,_ => true
  end.

Definition andb3 (a b c:bool) : bool :=
  match a,b,c with
    | true,true,true => true
    | _,_,_ => false
  end.

Inductive even : nat -> Prop :=
  | even0 : even 0
  | evenS n : odd n -> even (S n)
with 
  odd : nat -> Prop :=
  | oddS n : even n -> odd (S n)
.

Theorem even_odd_disj n : even n -> ~ odd n.
induction n.
intros H H0.
inversion H0.
intro H; inversion_clear H.
intro H.
inversion_clear H.
apply IHn; auto.
Qed.

Theorem odd_even_disj n : odd n -> ~ even n.
induction n.
intros H H0; inversion H.
intro H; inversion_clear H; intro H.
inversion_clear H.
apply IHn; auto.
Qed.

Theorem even_odd_dec n : {even n}+{odd n}.
induction n.
left; constructor.
destruct IHn.
right; constructor; auto.
left; constructor; auto.
Qed.

Theorem even_nat_ind : forall (P : nat -> Prop),
                       (forall n, even n -> P n) -> (forall n, odd n -> P n) ->
                   forall n, P n.
intros P He Ho n.
case (even_odd_dec n); auto.
Qed.

Definition dec_bool (A:Type) (P:A -> Prop)
                    (Hdec:forall a, {P a}+{~ P a}) :
           forall a:A, bool.
intro a.
destruct (Hdec a).
exact true.
exact false.
Defined.

Lemma even_nat_dec n : {even n}+{~ even n}.
destruct (even_odd_dec n).
auto.
right; apply odd_even_disj; auto.
Qed.

Definition evenb : nat -> bool := dec_bool _ even even_nat_dec.

Inductive FactorialP : nat -> nat -> Prop :=
  | Fact0 : FactorialP 0 1
  | FactN n m : FactorialP n m -> FactorialP (S n) ((S n) * m).

Definition factorial_strong n : {m|FactorialP n m}.
induction n.
econstructor.
constructor.
destruct IHn.
eapply exist.
constructor.
eauto.
Defined.

Inductive FibP : nat -> nat -> Prop :=
  | Fib0 : FibP 0 0
  | Fib1 : FibP 1 1
  | FibS n m p: FibP n m -> FibP (S n) p -> FibP (S (S n)) (m + p).

Theorem Fib3 : FibP 3 2.
change (FibP (S (S 1)) (1 + 1)).
apply FibS.
constructor.
change (FibP (S (S 0)) (0 + 1)).
apply FibS.
constructor.
constructor.
Qed.

Theorem fib_nat_rec (P:nat->Set) (P0:P 0) (P1:P 1) (IP:forall n, P n -> P (S n) -> P (S (S n))) n : P n.
induction n.
assumption.
induction n.
assumption.
apply IP.


Definition fib x : {n|FibP x n}.
induction x using fib_nat_rec.
exists 0; constructor.
exists 1; constructor.
destruct IHx as [y Hy].
