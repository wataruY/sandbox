
Theorem sample_exists
(P Q : nat -> Prop)
(H:forall n, P n)
(H0:exists n, Q n)
: exists n, P n /\ Q n.
Proof.
  destruct H0.
  eapply ex_intro.
  split.
  apply H.
  eassumption.
Qed.

Theorem ex5_1 (A:Set) (P:A->Prop) (H:~ exists a, P a) : forall a, ~ P a.
intro.
contradict H.
eapply ex_intro.
eassumption.
Qed.

Theorem ex5_2 (A:Set) (P Q:A->Prop) (H:exists a, P a\/Q a) : (exists a, P a) \/ (exists a, Q a).
destruct H as [b [H|H]]; [left|right]; eapply ex_intro; eassumption.
Qed.

Theorem ex5_3 (A:Set) (P Q:A->Prop) (H:(exists a, P a) \/ (exists a, Q a)) : exists a, P a \/ Q a.
destruct H as [H|H]; destruct H; eapply ex_intro; [left|right]; eassumption.
Qed.

Require Import Relations.

Theorem ex5_4 (A:Set) (R:relation A) (Hsurj:exists x, forall y, R x y) (y:A) : exists x, R x y.
destruct Hsurj as [x H].
eapply ex_intro.
apply H.
Qed.

Theorem ex5_5
        (A:Set)
        (R:relation A)
        (H0:symmetric _ R)
        (H1:transitive _ R)
        (Htotal:forall x, exists y, R x y)
        (x:A)
: R x x.
destruct (Htotal x).
eapply H1.
eassumption.
apply H0.
eassumption.
Qed.
