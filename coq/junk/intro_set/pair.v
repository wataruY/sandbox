Require Import Arith.

Goal forall (n:nat), (exists m:nat, n=m*4) -> exists k:nat, n=k*2.
intros n [m Hm].
eapply ex_intro.
rewrite Hm.
cutrewrite (4 =(2*2)); auto.
rewrite mult_assoc.
reflexivity.
Save hoge.

Theorem lt_Snm_nm n m : S n < m -> n < m.
apply lt_trans.
apply lt_n_Sn.
Qed.

Require Import List.
Infix "∈" := (In) (at level 30).

Notation "♯" := length.

Definition sums := fold_right plus 0.

Theorem pigeonhole (xs:list nat) : ♯ xs < sums xs -> exists x:nat, ((S (S x)) ∈ xs).
induction xs.
simpl.
intro H; contradict H; auto with arith.
simpl.
case a.
intro H.
apply lt_Snm_nm in H.
apply IHxs in H.
destruct H as [x H].
eapply ex_intro.
right; eassumption.
intro n; case n.
simpl.
intro H; apply lt_S_n in H.
apply IHxs in H.
destruct H as [x H].
eapply ex_intro; right; eassumption.
intros.
eapply ex_intro.
left; reflexivity.
Qed.