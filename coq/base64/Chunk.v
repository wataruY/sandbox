Require Import ssreflect Program. 
Require Export Bvector.
Require Import Arith List.
Require Import EqdepFacts.
Require Import Setoid SetoidClass.

Set Implicit Arguments.

Section Chunk.
  Generalizable Variable A B n m.
  
  Fixpoint list_to_vec {A} `(xs:list A) : vector A (length xs).
  destruct xs as [| x xs] => /=.
    exact Vnil.
    constructor; first exact x.
    destruct (list_to_vec _ xs) as [|y n ys].
        exact Vnil.
        constructor; first exact y.
        exact ys.
  Defined.
  Fixpoint vec_to_list `(xs:vector A n) : list A.
  destruct xs as [| x n xs].
    exact [].
    refine (x :: _).
    eapply vec_to_list.
      apply xs.
  Defined.

  Lemma list_to_vec_red `(a:A) (xs: list A) : (list_to_vec (a :: xs)) = Vcons a (list_to_vec xs).
  destruct xs; done.
  Qed.
  
  Lemma vec_to_list_red `(a:A) `(v:vector A n) : vec_to_list (Vcons a v) = a :: vec_to_list v.
  destruct v; done.
  Qed.

  Theorem list_vec_inv `(xs:list A) : (vec_to_list (list_to_vec xs)) = xs.
  induction xs.
    done.
    rewrite list_to_vec_red vec_to_list_red.
    rewrite IHxs.
    done.
  Qed.
  
  Lemma vec_to_list_length_preserve `(v:vector A n) : length (vec_to_list v) = n.
  induction v => /=.
    done.
    congruence.
  Qed.

  Lemma Vcons_heq `(a:A) `(xs:vector A n) `(ys:vector A m) :  n = m -> xs ~= ys -> Vcons a xs ~= Vcons a ys.
  move => ?; subst.
  move => H.
  apply JMeq_eq_dep_id in H.
  by dependent induction H.
  Qed.

  Theorem vec_list_inv `(xs:vector A n) : list_to_vec (vec_to_list xs) ~= xs.
  induction xs.
    done.
    assert (Hlen:length (vec_to_list xs) = n).
      apply vec_to_list_length_preserve.
    rewrite vec_to_list_red list_to_vec_red.
    by apply Vcons_heq.
  Qed.

  Definition Vapp_strong `(xs:vector A n) `(ys:vector A m) :
    {zs:vector A (n + m) | vec_to_list zs ~= vec_to_list xs ++ vec_to_list ys}.
  induction xs as [| x n xs].
    by exists ys.
    destruct IHxs as [zs Hzs].
    exists (Vcons x zs).
    simpl.
    dependent destruction Hzs.
    match goal with
      | [ H: vec_to_list zs = _ |- _] => rewrite H
    end.
    reflexivity.
  Defined.
  Lemma vec_to_list_eq_length `(xs:vector A n) `(ys:vector A m) : vec_to_list xs = vec_to_list ys -> n = m.
  move => H.
  pose (p := length (vec_to_list xs)).
  assert (n = p).
    symmetry.
    etransitivity.
    unfold p.
    apply vec_to_list_length_preserve.
    done.
  pose (q := length (vec_to_list ys)).
  assert (m = q).
    symmetry; etransitivity.
    by apply vec_to_list_length_preserve.
    done.
  assert (p = q).
    unfold p,q.
    congruence.
  congruence.
  Qed.


  Theorem vec_to_list_inj `(xs:vector A n) `(ys:vector A m) : vec_to_list xs = vec_to_list ys -> xs ~= ys.
  move => H.
  pattern xs.
  rewrite <- (vec_list_inv xs).
  rewrite <- (vec_list_inv ys).
  rewrite H.
  done.
  Qed.
  Definition Vlen `(xs:vector A n) : nat.
  exact n.
  Defined.

  Theorem JMeq_eq_dep_type
     : forall (U : Type) (P : U -> Type) (p q : U) (x : P p) (y : P q),
       p = q -> x ~= y -> eq_dep U P p x q y.
  intros.
  destruct H.
  apply JMeq_eq in H0 as ->.
        reflexivity.
  Qed.
  Fixpoint compare_length {A} (xs ys:list A) : comparison.
  destruct xs as [|x xs]; destruct ys as [|y ys].
  exact Eq.
  exact Lt.
  exact Gt.
  exact (compare_length _ xs ys).
  Defined.
  Functional Scheme compare_length_ind := Induction for compare_length Sort Prop.

    
  Fixpoint Vapp_weak `(xs:vector A n) `(ys:vector A m) : vector A (n + m) :=
    match xs with
      | Vnil => ys
      | Vcons a _ xs' => Vcons a (Vapp_weak xs' ys)
    end.
  Functional Scheme Vapp_weak_ind := Induction for Vapp_weak Sort Prop.
  Theorem Vapp_weaken `(xs:vector A n) `(ys:vector A m) : proj1_sig (Vapp_strong xs ys) = Vapp_weak xs ys.
  functional induction (Vapp_weak xs ys) => /=.
    done.
    destruct (Vapp_strong xs' ys); simpl in *.
    by f_equal.
  Qed.

End Chunk.