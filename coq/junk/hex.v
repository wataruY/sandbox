Require Import Arith Omega.

Inductive Hex :=
  | Dec (n:nat)
  | Xn (n:nat) : 0<=n<6 -> Hex.

Definition Hex2N : Hex -> nat.
intro x.
induction x.
apply n.
apply (10 + n).
Defined.

Inductive DivModP (m n:nat) (Hn:n<>0) : nat -> nat -> Prop :=
  | divMod1 : m < n -> DivModP m n Hn 0 m
  | divMod2 : m = n -> DivModP m n Hn 1 0
  | divModN m' b r : m > n -> m = m' + n -> DivModP m' n Hn b r -> DivModP m n Hn (S b) r.

Theorem DivModP_inv m n b r Hn : DivModP m n Hn b r -> m = n*b+r.
induction m.
inversion_clear 1.
ring.
omega.
generalize dependent b0.
generalize dependent r.
induction n.
contradict H0.
auto with arith.
intros.
simpl.
Definition divMod_strong m n (Hn:n <> 0) : {b:nat & {r| DivModP m n Hn b r}}.
assert (H:=lt_eq_lt_dec m n).
destruct H as [[H|H]|H].
exists 0.
exists m.
apply divMod1; auto.
rewrite H.
exists 1; exists 0; apply divMod2; auto.
induction m.
contradict H; auto with arith.
apply lt_n_Sm_le in H.
apply le_lt_eq_dec in H as [H|H].
assert (H' := IHm H).
destruct H' as [b [r H']].
