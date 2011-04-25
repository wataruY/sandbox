
Goal forall (A : Prop), A -> A.
Proof.
  intros A x.
  assumption.
Qed.

Goal forall (P Q : Prop), (forall P:Prop, (P -> Q) -> Q) -> ((P -> Q) -> P) -> P.
Proof.
  intros P Q H0 H1.
  apply H1.
  intro.
  eapply H0.
  intro.
  eassumption.
Qed.  

Goal forall P Q R, (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H0 H1 p.
  apply H1.
  apply H0.
  assumption.
Qed.

Goal forall P : Prop, P -> ~~P.
Proof.
  intros P p.
  contradict p.
  assumption.
Qed.

Goal forall P Q, P \/ Q -> Q \/ P.
Proof with assumption.
  intros P Q H.
  destruct H.
    right...
    left...
Qed.

Goal forall P Q, P /\ Q -> Q /\ P.
Proof.
  intros P Q [p q].
  split; assumption.
Qed.

Goal forall P, ~(P /\ ~P).
Proof.
  intros P [H H'].
  contradiction.
Qed.

Goal forall P Q, ~P \/ ~Q -> ~(P /\ Q).
Proof.
  intros P Q H [p q].
  destruct H; contradiction.
Qed.  

Goal forall P, (forall P, ~~P -> P) -> P \/ ~P.
Proof.
  intros P Hcl.
  apply Hcl.
  intro H.
  apply H.
  right.
  contradict H.
  tauto.
Qed.
