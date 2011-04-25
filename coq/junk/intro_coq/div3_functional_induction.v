Require Import Arith.

Fixpoint div3 (n:nat) : nat :=
  match n with
    | S (S (S p)) => S (div3 p)
    | _ => 0
  end.

Functional Scheme div3_ind := Induction for div3 Sort Prop.

Definition mod3 n := n - (div3 n * 3).

Theorem div3_mod3 n : div3 n * 3 + mod3 n = n.
functional induction (div3 n); try reflexivity.
simpl.
repeat f_equal||rewrite <- plus_n_Sm.
assumption.
Qed.