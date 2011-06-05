Require Import Zdiv Arith.

Functional Scheme Zdiv_eucl_ind := Induction for Zdiv_eucl Sort Prop.

Theorem verif_divide (m p:nat) :
0 < m -> 0 < p ->
(exists q:nat, m= q*p) -> (Z_of_nat m mod Z_of_nat p = 0)%Z.
intros Hltm Hltp [q Heq].
rewrite Heq.
rewrite inj_mult.
apply Z_mod_mult.
Qed.

Theorem prod_gt_O_inv m n : 0 < m * n <-> 0 < m /\ 0 < n.
split.
  intro H.
  split.
    induction m; omega.
    induction n; omega.
  intros [H1 H2].
  induction m; simpl.
  auto with arith.
  clear H1.
  induction n.
  auto with arith.
  auto with arith.
Qed.

Theorem divisor_smaller (m p:nat) 
: 0 < m -> forall q:nat, m = q*p -> q <= m.
intros H0 q Heq.
rewrite Heq.
  assert (Hg0 : 0 < q /\ 0 < p).
    apply prod_gt_O_inv.
    rewrite Heq in H0; auto.
  rewrite mult_comm.
  case (mult_O_le q p).
    intro H'.
    subst.
    rewrite mult_comm in H0; simpl in H0.
    contradict H0; auto with arith.
    trivial.
Qed.

Fixpoint check_range (v:Z) (r:nat) (sr:Z) : bool :=
  match r with
     | 0 => true
     | S r' =>
         match (v mod sr)%Z with
            | Z0 => false
            | _ => check_range v r' (Zpred sr)
         end
  end.

Definition check_primality (n:nat) :=
  check_range (Z_of_nat n) (pred (pred n)) (Z_of_nat (pred n)).

