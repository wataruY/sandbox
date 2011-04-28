Require Import Arith ssreflect Relations.

Definition pred_partial : forall n:nat, n <> 0 -> nat.
induction n.
  done.
  intro;exact n.
Defined.

Section minimal_specification_strengthening.

Variable prime : nat -> Prop.
Definition divides (n p:nat) : Prop := exists q:_, q*p = n.
Definition prime_divisor (n p:nat) := prime p /\ divides p n.

Variable prime_test : nat -> bool.
Hypothesis (prime_test_t : forall n:nat, prime_test n = true -> prime n)
           (prime_test_f : forall n:nat, prime_test n = false -> ~ prime n).

Variable get_primediv_weak : forall n:nat, ~ prime n -> nat.
Hypothesis get_primediv_weak_ok
: forall (n:nat) (H:~prime n),
  1 < n -> prime_divisor n (get_primediv_weak n H).

Theorem divides_refl : reflexive _ divides.
move=> n.
exists 1.
ring.
Qed.
Hint Resolve divides_refl.

Definition bad_get_prime : nat -> nat.
move=> n.
case_eq (prime_test n).
  exact (fun _ => n).
  move=> Hfalse; apply (get_primediv_weak n).
  auto.
Defined.

Theorem bad_get_prime_ok 
: forall n:nat, 1 < n -> prime_divisor n (bad_get_prime n).
move=> n H.
unfold bad_get_prime.
(* case (prime_test n).
   Error: second-order unification problem
 *)
Abort.

Definition stronger_prime_test n : {prime_test n=true}+{prime_test n=false}.
case (prime_test n); eauto.
Defined.

Definition get_prime n : nat :=
  match stronger_prime_test n with
    | left H => n
    | right H => get_primediv_weak n (prime_test_f n H)
  end.

Theorem get_primediv_ok n
: 1 < n -> prime_divisor n (get_prime n).
move=> H.
unfold get_prime.
case (stronger_prime_test n); auto.
split; auto.
Qed.

End minimal_specification_strengthening.