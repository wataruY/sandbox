Require Import ssreflect.
Require Import List Arith Omega Program.
Require Import Recdef.

Section EachCons.
  Generalizable Variables A B C.
  (* NthElemOf x n l <-> n < length l /\ x ∈ l /\ l[n] = x *)
  Inductive NthElemOf `(x:A) : nat -> list A -> Prop :=
  | neo_hd l : NthElemOf x 0 (x :: l)
  | neo_k n l y : NthElemOf x n l -> NthElemOf x (S n) (y :: l).
  
  Functional Scheme nth_error_ind := Induction for nth_error Sort Prop.
  Theorem NthElemOf_nth_error `(x:A) n l : nth_error l n = value x <-> NthElemOf x n l.
    functional induction (nth_error l n); simpl; split => H.
    done.
    inversion H.
    injection H; move => *; subst; by apply neo_hd.
    by inversion_clear H.
    done.
    inversion H.
    by intuition constructor.
    inversion_clear H; by intuition.
  Qed.
  
  Lemma NthElem_IN `(x:A) n l : NthElemOf x n l -> In x l.
  elim.
  by constructor.
  simpl;tauto.
  Qed.
  
  Theorem NthElem_length `(x:A) n l : NthElemOf x n l -> n < length l.
  elim; simpl; by intuition.
  Qed.
  
  (* ys[i] = xs[i] `f` xs[i+1] *)
  Definition adj_prop `(f:A -> A -> B) (xs:list A) `(ys:list B) :=
    forall (x y:A) (z:B) (n:nat),
      NthElemOf x n xs -> NthElemOf y (S n) xs -> f x y = z ->
      NthElemOf z n ys.
  
  Lemma NthElemOf_nil `(x:A) n : ~ NthElemOf x n [].
  move => H; inversion H.
  Qed.
  Hint Resolve @NthElemOf_nil.

  (* zipWith *)
  Fixpoint combine_with `(f:A->B->C) (xs:list A) (ys:list B) : list C :=
  match xs,ys with
    | nil, _ => nil
    | _, nil => nil
    | a :: xs', b :: ys' => f a b :: combine_with f xs' ys'
  end.  
  
  Definition adj_with `(f:A->A->B) (xs:list A) := combine_with f xs (tl xs).
  
  Lemma NthElemOf_S `(x:A) y n l : NthElemOf x (S n) (y :: l) <-> NthElemOf x n l.
  split => H.
  by inversion H.
  by constructor.
  Qed.
  
  Lemma NthElemOf_hd `(x:A) y l : NthElemOf x 0 (y :: l) <-> x = y.
  split => H.
    by inversion_clear H.
    subst; constructor.
  Qed.
  
  Theorem adj_with_prop `(f:A->A->B) (xs:list A) : adj_prop f xs (adj_with f xs).
  unfold adj_prop, adj_with.
  move => x y z n H.
  revert z y.
  induction H.
  revert x.
  induction l; simpl.
  move => ? ? ? H.
  apply NthElemOf_S in H; by contradict H.
  move => ? ? ? H *.
  apply NthElemOf_hd.
  apply NthElemOf_S ,NthElemOf_hd in H.
  congruence.
  move => ? ? H0 Hf.
  apply NthElemOf_S in H0.
  destruct l; simpl in *.
  by contradict H0.
  eapply NthElemOf_S, IHNthElemOf; eassumption.
  Show Script.
  Qed.
  
  Definition adj_with_strong `(f:A->A->B) (xs:list A) : {ys:list B | adj_prop f xs ys}.
  induction xs.
  eexists => ? ? ? ? H.
  by contradict H.
  destruct xs.
  eexists => ? ? ? ? ? H.
  by apply NthElemOf_S, NthElemOf_nil in H.
  rename a0 into b.
  destruct (IHxs) as [ys Hys].
  exists (f a b :: ys).
  intros x y z n H0 H1 Hf.
  induction n.
  apply NthElemOf_hd in H0.
  apply NthElemOf_S,NthElemOf_hd in H1.
  subst.
  by constructor.
  apply NthElemOf_S.
  eapply Hys.
    apply NthElemOf_S in H0; eassumption.
    apply NthElemOf_S in H1; eassumption.
    assumption.
  Existential 1 := [].
  Existential 1 := [].
  Defined.

  Theorem adj_with_strong_zipwith `(f:A -> A -> B) (xs:list A) :
    adj_with f xs = proj1_sig (adj_with_strong f xs).
  induction xs.
  reflexivity.
  simpl in *.
  destruct ((adj_with_strong f xs)).
  destruct xs.
  reflexivity.
  simpl in *.
  unfold adj_with in *.
  simpl.
  f_equal.
  destruct xs; assumption.
  Qed.
  
End EachCons.