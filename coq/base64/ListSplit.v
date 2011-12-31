Require Import ssreflect.
Require Import Program List Arith Omega Bvector.
Require Import Min.
Require Import Relations RelationClasses Setoid SetoidClass.

Infix ":::" := Vcons (at level 30).

Section list_split.
  Generalizable Variables A.

  Lemma min_plus_reg l m n : 0 < n -> min l (m + n) = m -> m = l.
  move => H Hmin.
  destruct (min_dec l (m+n)) as [Hmin0|Hmin1].
    by congruence.
    rewrite Hmin1 in Hmin.
    omega.
  Qed.
  
  
  Fixpoint take_strong {A} n (xs:list A) :
    {ys:list A & { zs:list A |
                   length ys = min n (length xs) /\ xs = ys ++ zs }}.
  destruct n as [|n]; simpl.
  eexists []; eexists; split.
    done.
    reflexivity.
  destruct xs as [| a xs]; simpl.
    eexists []; eexists []; by split.
  destruct (take_strong _ n xs) as [ys [zs [Hlen Hsub]]].
  rewrite <- Hlen.
  rewrite Hsub.
  exists (a :: ys).
  eexists.
  split; first reflexivity.
  reflexivity.
  Defined.

  Lemma eq_length {A} (xs ys:list A) : Proper eq length. 
  congruence.
  Qed.
  
  Theorem sublis_length_eq {A} (xs:list A) ys zs :
    length xs = length ys -> xs = ys ++ zs -> xs = ys.
  move => Hlen Happ.
  rewrite Happ in Hlen|-*.
  rewrite app_length in Hlen.
  destruct zs.
  by rewrite app_nil_r.
  contradict Hlen.
  clear.
  revert dependent ys.
  induction zs.
  revert a; induction ys.
    by auto with arith.
    move => H; injection H.
    by auto with arith.
    move => ys; simpl in *.
    move => H.
    eapply (IHzs (a::zs)).
    omega.
  Qed.

  Fixpoint drop_strong {A} n (xs:list A) :
    {ys:list A & {zs: list A |
                  length zs = min n (length xs) /\ xs = zs ++ ys}}.
  destruct n as [|p].
    exists xs; eexists []; by eauto.
  destruct xs as [|x xs].
    do 2 eexists []; by eauto.
  destruct (drop_strong _ p xs) as [ys [zs [H0 H1]]]; simpl.
  pose (H:= min_dec p (length xs)); destruct or H;
    rewrite H in H0|-*; rewrite H1; rewrite app_comm_cons.
    exists ys; eexists.
    split; last reflexivity.
    simpl; by intuition.
    rewrite app_length.
    assert (Heq : xs = zs).
      eapply sublis_length_eq; by eauto.
    subst.
    eexists; eexists.
    split; last reflexivity.
    simpl.
    assert (Hys : ys = []).
      clear H H0.
      induction zs.
        done.
        apply IHzs.
        by injection Heq.
    rewrite Hys; by intuition.
  Defined.
  Fixpoint take {A} (n:nat) (xs:list A) : list A :=
    match n with
      | 0 => []
      | S p => match xs with
                 | [] => []
                 | a :: l => a :: take p l
               end
    end.

  Functional Scheme take_ind := Induction for take Sort Prop. 
  Lemma length0_nil `(xs:list A) : length xs = 0 <-> xs = [].
  destruct xs; simpl.
    done.
    split; discriminate.
  Qed.
  Functional Scheme length_ind :=Induction for length Sort Prop.

  Lemma length_app_nil {A} (ys zs:list A) : length ys = length ys + length zs -> zs = [].
  revert ys.
  destruct zs as [|z zs].
    done.
    revert zs; induction ys.
      discriminate.
      move => /= H.
      apply IHys.
      by injection H => *.
  Qed.
  Lemma take_length_idemp n `(xs:list A) (H:length xs <= n) : xs = take n xs.
  functional induction (take n xs); simpl in *.
    destruct xs.
      done.
      contradict H; simpl; by auto with arith.
    done.
    f_equal; apply IHl; omega.
  Qed.
  Lemma take_nil A n : take n [] = @nil A.
  by destruct n.
  Qed.
  Lemma take_app {A} n (xs ys:list A) : take n (xs ++ ys) = take n xs ++ take (n - length xs) ys.
  revert ys.
  functional induction (take n xs) => /=.
    done.
    done.
    move => ys.
    by f_equal; intuition.
  Qed.

   

  Theorem take_weaken n `(xs:list A) : (projT1 (take_strong n xs)) = take n xs.
  destruct (take_strong n xs) as [ys [zs H]].
  destruct H as [Hlen Happ].
  simpl.
  rewrite Happ in Hlen.
  rewrite app_length in Hlen.
  rewrite Happ.
  rewrite take_app.
  symmetry in Hlen.
  destruct zs.
    simpl in *.
    rewrite take_nil.
    rewrite app_nil_r in Happ.
    rewrite app_nil_r.
    rewrite plus_0_r in Hlen.
    apply min_r_iff in Hlen.
    by apply take_length_idemp.
    apply min_plus_reg in Hlen => /=; last by auto with arith.
    rewrite Hlen minus_diag.
    rewrite <- take_length_idemp; last omega.
    simpl.
    by auto with datatypes.
  Qed.

  Fixpoint drop {A} n (xs:list A) : list A :=
    match n with
      | 0 => xs
      | S p => match xs with
                 | [] => []
                 | _ :: l => drop p l
               end
    end.
  Functional Scheme drop_ind := Induction for drop Sort Prop.
  Lemma drop_nil {A} n : drop n [] = @nil A.
  by destruct n.
  Qed.
  Lemma minus0 n : 0 - n = 0.
  by destruct n.
  Qed.
  Lemma drop_app {A} n (xs ys:list A) : drop n (xs ++ ys) = drop n xs ++ drop (n - length xs) ys.
  destruct n as [|p].
    done.
    revert p ys.
    induction xs.
      done.
      simpl.
      move => p ys.
      assert (H := IHxs (pred p) ys).
  destruct (dec_lt 0 p) as [H0|H1].
    assert (Hpred:=  eq_sym (S_pred p 0 H0)).
    by rewrite Hpred in H.
    assert (Hp : p = 0).
      apply not_lt in H1.
      by inversion H1.
    subst.
    by rewrite minus0.
  Qed.
   
  Lemma drop_length n `(xs:list A) (Hlen:length xs <= n) :  drop n xs = [].
  induction Hlen.
    by induction xs.
    clear Hlen.
    revert dependent m.
      induction xs.
        done.
        move => m H.
        assert (Hm : 0 < m).
          clear IHxs.
          destruct m.
            discriminate.
            auto with arith.
        assert (IH := IHxs (pred m)).
        assert (Hpred := eq_sym (S_pred _ _ Hm)).
        rewrite Hpred in IH.
        simpl; apply IH.
        move: H; clear.
        revert a xs.
        induction m.
          discriminate.
          done.
     Qed.


  Theorem drop_weaken n `(xs:list A) : (projT1 (drop_strong n xs)) = drop n xs.
  destruct (drop_strong n xs) as [ys [zs H]]; simpl.
  destruct H as [Hlen Happ].
  subst.
  rewrite app_length in Hlen.
  symmetry in Hlen.
  destruct ys.
    simpl in *.
    rewrite plus_0_r in Hlen.
    apply min_r_iff in Hlen.
    rewrite app_nil_r.
    symmetry.
    by apply drop_length.
    simpl in *.
    assert (length zs = n).
      eapply min_plus_reg.
      2:eassumption.
      by auto with arith.
    clear Hlen.
    rewrite <- H.
    rewrite drop_app.
    rewrite drop_length; last done.
    rewrite minus_diag.
    done.
  Qed.

  Theorem drop_strong_as_take n `(xs:list A) :
    take n xs = projT1 (projT2 (drop_strong n xs)).
  destruct (drop_strong n xs) as [ys [zs H]] => /=.
  destruct H as [Hlen Happ].
  rewrite Happ in Hlen |- *.
  rewrite take_app.
  rewrite app_length in Hlen.
  clear Happ.
  symmetry in Hlen.
  destruct ys as [|y ys]; simpl in *.
    rewrite take_nil.
    rewrite plus_0_r in Hlen.
    rewrite app_nil_r.
    apply min_r_iff in Hlen.
    symmetry.
    by apply take_length_idemp.
    apply min_plus_reg in Hlen; last by auto with arith.
    rewrite <- Hlen.
    rewrite <- take_length_idemp; last done.
    rewrite minus_diag.
    by simpl;auto with datatypes.
  Qed.
  
  Theorem take_strong_as_drop n `(xs:list A) : drop n xs = projT1 (projT2 (take_strong n xs)).
  destruct (take_strong n xs) as [ys [zs H]] => /=.
  destruct H as [Hlen Happ].                                                
  rewrite Happ in Hlen|-*; clear Happ.
  rewrite app_length in Hlen.
  rewrite drop_app.
  symmetry in Hlen.
  destruct zs; simpl in *.
    rewrite drop_nil app_nil_r.
    rewrite plus_0_r in Hlen.    
    apply min_r_iff in Hlen.
    by apply drop_length.
    apply min_plus_reg in Hlen; last auto with arith; subst.
    rewrite drop_length; last auto with datatypes.
    rewrite minus_diag.
    done.
  Qed.
     
  Fixpoint split_at {A} n (xs:list A) : list A * list A :=
    match n with
      | 0 => ([],xs)
      | S p => match xs with
                 | [] => ([],[])
                 | a :: l => let (ys,zs) := split_at p l
                             in (a::ys,zs)
               end
    end.

  Functional Scheme split_at_ind := Induction for split_at Sort Prop.

  Lemma pair_equiv_proper A B : Proper (eq ==> eq ==> eq) (@pair A B).
  lazy => *; by subst.
  Qed.

  Theorem split_at_take_drop n `(xs:list A) : split_at n xs = (take n xs,drop n xs).
  functional induction (split_at n xs).
    done.
    done.
    simpl.
    match goal with
      | [ H0: split_at ?N ?L = (take ?N ?L, drop ?N ?L) ,
          H1: split_at ?N ?L = (?XS, ?YS) |- _ ]
        => let H := fresh in assert (H:(XS,YS) = (take N L, drop N L)); [congruence|injection H]
    end.
    congruence.
  Qed.

  Theorem take_strong_as_split_at n `(xs:list A) :
    let l := take_strong n xs in (projT1 l, projT1 (projT2 l)) = split_at n xs.
  simpl.
  rewrite split_at_take_drop.
  rewrite <- take_strong_as_drop.
  apply pair_equiv_proper; last done.
  by rewrite take_weaken.
  Qed.

End list_split.

