Require Import Ensembles.

Theorem singleton_in_included (U:Type) (A:Ensemble U) (a:U) :
In _ A a <-> Included _ (Singleton _ a) A.
unfold Included, In.
split.
intro Ha.
intros x Hs.
elim Hs.
assumption.
intros.
apply H.
change (In _ (Singleton _ a) a).
apply In_singleton.
Qed.

Section Represented.
Require Import QArith.

Variable Sqrt2 : Q.

Definition Hoge := {x:Q & {a:Q & {b:Q | x == a + b * Sqrt2 }}}.

Definition addA (x y:Hoge) : Hoge.
destruct x.
destruct y.
destruct s.
destruct s.
destruct s0.
destruct s.
exists (x + x0).
exists (x1 + x3).
exists (x2 + x4).
setoid_rewrite q.
setoid_rewrite q0.
ring.
Qed.