Require Import Arith.

Definition sub (m n:nat) (H:n<=m) : {x:nat|x+n=m}.
generalize dependent m.
induction n as [|n'].
  intros m H.
  eapply exist.
  apply plus_0_r.
  induction m as [|m']; intro H.
  (* m = 0 *)
  contradict H.
  auto with arith.
  (* m = S m' *)
  assert (H' : n' <= m'); [auto with arith|].
  destruct (IHn' _ H') as [y Hy].
  eapply exist.
  rewrite <- plus_n_Sm.
  f_equal.
  rewrite <- Hy.
  reflexivity.
Defined.
(* Extraction sub. *)

Definition sub' (m n:nat) (H:n<=m) : {x:nat|x+n=m}.
  exists (m - n).
  rewrite plus_comm.
  eapply (le_plus_minus_r _ _ H).
Defined.
