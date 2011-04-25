Require Import Arith.

Theorem plus_comm' m n : m + n = n + m.
induction m.
rewrite <- plus_n_O.
reflexivity.
rewrite <- plus_n_Sm.
simpl.
rewrite IHm.
reflexivity.
Qed.