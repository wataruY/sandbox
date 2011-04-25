Section PropLogic.

Variables A B C D:Prop.

Theorem ex4_1 : (A -> C) /\ (B -> D) /\ A /\ B -> C /\ D.
intros [H1 [H2 [a b]]].
split; [apply H1 | apply H2]; assumption.
Qed.

Theorem ex4_2 : ~~~A -> ~A.
intro H.
do 2 contradict H.
assumption.
Qed.

Theorem ex4_3 : (A -> B) -> ~ B -> ~ A.
intros H H1.
contradict H1.
apply H; assumption.
Qed.

Theorem ex4_4 : ((((A -> B) -> A) -> A) -> B) -> B.
repeat match goal with
          | [ H:?X |- ?X ] => assumption
          | [ |- _ -> _] => intro
          | [ H: _ -> ?Y |- ?Y ] => apply H
       end.
Qed.

Theorem ex4_5 : ~~(A \/ ~A).
intro H.
elim H.
right.
contradict H.
left; assumption.
Qed.