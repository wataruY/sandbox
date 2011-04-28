Require Import ZArith_base.

Section little_semantics.

Variables Var aExp bExp : Set.

Inductive inst : Set :=
| Skip : inst
| Assign : Var->aExp->inst
| Sequence : inst->inst->inst
| WhileDo : bExp->inst->inst.

Variables
  (state : Set)
  (update : state->Var->Z -> option state)
  (evalA : state->aExp -> option Z)
  (evalB : state->bExp -> option bool).

Inductive exec : state->inst->state->Prop :=
| execSkip : forall s:state, exec s Skip s
| execAssign :
   forall (s s1:state)(v:Var)(n:Z)(a:aExp),
     evalA s a = Some n -> update s v n = Some s1 ->
     exec s (Assign v a) s1
| execSequence :
   forall (s s1 s2:state)(i1 i2:inst),
    exec s i1 s1 -> exec s1 i2 s2 ->
    exec s (Sequence i1 i2) s2
| execWhileFalse :
   forall (s:state)(i:inst)(e:bExp),
    evalB s e = Some false -> exec s (WhileDo e i) s
| execWhileTrue :
   forall (s s1 s2:state)(i:inst)(e:bExp),
    evalB s e = Some true ->
    exec s i s1 ->
    exec s1 (WhileDo e i) s2 ->
    exec s (WhileDo e i) s2.


Theorem HoareWhileRule :
 forall (P:state->Prop)(b:bExp)(i:inst)(s s':state),
   (forall s1 s2:state,
      P s1 -> evalB s1 b = Some true -> exec s1 i s2 -> P s2)->
   P s -> exec s (WhileDo b i) s' ->
   P s' /\ evalB s' b = Some false.
intros P b i s s' H.
cut (forall i':inst,
     exec s i' s' ->
     i' = WhileDo b i -> P s -> P s' /\ evalB s' b = Some false).
intros.
eauto.
intros i' Hexec.
elim Hexec; try (intros;discriminate).
intros s0 i0 e Heval Heq.
injection Heq; intros Heq1 Heq2; subst.
auto.
intros.
match goal with
  | [ H:_ = _ |- _ ] => injection H; intros; subst
end.
eapply H4.
trivial.
eapply H.
eassumption.
assumption.
assumption.
Qed.

Theorem skip_inv (pre post:state)
: exec pre Skip post -> pre = post.
inversion 1.
auto.
Qed.

Theorem hoare_empty (P:state->Prop) (pre post:state)
: P pre -> exec pre Skip post -> P post.
intros Hpre Hexec.
erewrite <- skip_inv; eauto.
Qed.

Theorem hoare_assign (P:state->Prop)

Definition get_test_from_while (b:bExp) (i:inst) :=
  match i with
     | WhileDo b' i' => b'
     | _ => b
  end.

Definition get_body_from_while (i:inst) :=
  match i with
     | WhileDo b' i' => i'
     | _ => i
  end.

Definition is_while (i:inst) :=
  match i with WhileDo b' i' => True | _ => False end.

Lemma HoareWhile_aux :
      forall (P:state->Prop) (b:bExp) (i:inst) (s s':state),
      exec s (WhileDo b i) s' ->
      (forall s1 s2:state,
      P s1 -> evalB s1 (get_test_from_while b (WhileDo b i)) = Some true ->
      exec s1 (get_body_from_while (WhileDo b i)) s2 -> P s2) ->
      P s -> P s' /\ evalB s' (get_test_from_while b (WhileDo b i)) = Some false.
intros P b i s s' Hexec.
generalize (I:is_while (WhileDo b i)).
elim Hexec;try (simpl;intros;contradiction).
simpl.
intros.
split.
auto.
auto.
simpl.
intros.
apply H3.
trivial.
trivial.
eapply H5.
eassumption.
assumption.
assumption.
Qed.

Theorem infinite_loop_aux 
: forall s s' i,
  exec s i s' ->
  forall b, i= WhileDo b Skip -> evalB s b = Some true -> False.
intros s s' i Hexec.
elim Hexec; try (intros; discriminate).
intros s0 i0 e Heval b Heq; injection Heq; intros Heq1 Heq2; subst.
rewrite Heval.
discriminate.

intros.
injection H4.
intros; subst.
eapply H3.
eassumption.
inversion H0; subst.
assumption.