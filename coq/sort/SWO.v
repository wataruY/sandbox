Require Import ssreflect.
Require Import Relations.
Require Import Program.Tactics.
Require Import RelationClasses.
Require Import Relation_Operators.
Require Import Setoid.
Require Import SetoidClass.
Require Import Classical.

Set Implicit Arguments.

Generalizable Variables A R.

Section Incomparable.
  Context `(R:relation A).
  Definition incomp `(R:relation A ) : relation A := fun x y => ~ R x y /\ ~ R y x.
  Instance incomp_symm  : Symmetric (incomp R).
  autounfold.
  unfold incomp.
  move =>*; destruct_conjs; split; by auto.
  Qed.
End Incomparable.
  
Section SWO_aux.
  Context `(R:relation A ).
  Variable irrefl : Irreflexive R.
  Variable trans : Transitive R.
  Definition Rcase := forall x y z , R x y -> R x z \/ R z y.
  Instance irrefl_trans_asymm : Asymmetric R.
  move=> x y *.
  eapply irrefl.
  etransitivity; eauto.
  Qed.
  Theorem incomp_trans_imp_rcase : Transitive (incomp R) -> Rcase.
  unfold Transitive, incomp.
  intros Htrans x y z H.
  pose proof (irrefl_trans_asymm H) as H0.
  apply NNPP.
  intro H1.
  elim H0.
  apply not_or_and in H1.
  destruct_conjs.
  destruct (classic (R y z)).
   absurd (R x z).
    assumption.
    
    etransitivity; eauto   .
    
   destruct (classic (R z x)).
    absurd (R z y).
     assumption.
     
     etransitivity; eauto   .
     
    assert (incomp R y z) as H5.
     split; assumption.
     
     assert (incomp R z x) as H6.
      split; assumption.
      
      absurd (R x y).
       eapply proj2.
       eapply Htrans.
        apply H5.
        
        apply H6.
        
       assumption.       
  Qed.
  Instance rcase_incomp_trans (H:Rcase) : Transitive (incomp R).
  unfold incomp.
  move => x y z *; simpl in*.
  destruct_conjs; split; intro H'; destruct (H _ _ y H'); contradiction.
  Qed.
End SWO_aux.

Section SWO.
  Class StrictWeakOrder `(R:relation A) :=
    { swo_irrefl : Irreflexive R
    ; swo_trans : Transitive R
    ; swo_incomp_trans : Transitive (incomp R)
    }.
  Hint Unfold incomp.
  Context `(SWO:StrictWeakOrder A R).
  Hint Resolve swo_irrefl : swo.
  Instance swo_asym : Asymmetric R := irrefl_trans_asymm swo_irrefl swo_trans.
  Instance swo_incomp_equiv : Equivalence (incomp R).
  split.
  move=>* /=; split; apply swo_irrefl.
  apply incomp_symm.
  apply swo_incomp_trans.
  Qed.
  Instance swo_incomp_oid : Setoid A := {| equiv := incomp R |}.
  Theorem swo_case : Rcase R.
  apply incomp_trans_imp_rcase; apply SWO.
  Qed.
  Theorem incomp_Proper_on_SWO : Proper (equiv ==> equiv ==> iff) R.
  intros x y Hxy z w Hzw; split; intro H.
  destruct (swo_case y H).
  destruct Hxy; contradiction.
  destruct (swo_case w H0).
  assumption.
  destruct Hzw; contradiction.

  destruct (swo_case x H).
  destruct Hxy; contradiction.
  destruct (swo_case z H0).
  assumption.
  destruct Hzw; contradiction.
  Qed.
  Theorem swo_not_inv_or_incomp x y : ~ R x y -> incomp R x y \/ R y x.
  intro H.
  apply NNPP.
  contradict H.
  apply not_or_and in H.
  unfold incomp in H.
  destruct H as [H0 H1].
  apply not_and_or in H0.
  destruct H0 as [H0|H0]; apply NNPP in H0.
    assumption.
    contradiction.
  Qed.
End SWO.

Section TotalPreorder.
  Class TotalPreorder `(R:relation A) :=
    { topo_refl : Reflexive R ;
      topo_trans : Transitive R ;
      topo_total x y : R x y \/ R y x
    }.
  
  Instance swo_compl_topo `(SWO:StrictWeakOrder A R) : TotalPreorder (complement R).
  unfold complement; simpl.
  split.
    move => x /=.
    apply swo_irrefl.

    pose swo_trans.
    move => x y z H0 H1; simpl in *.
    apply swo_not_inv_or_incomp in H0; apply swo_not_inv_or_incomp in H1.
  destruct H0; destruct H1.
  eapply proj1.
  eapply swo_incomp_trans; eauto.
  intro H1.
  destruct H.
  elim H.
  etransitivity; eauto.
  intro H1.
  unfold incomp in *; destruct_conjs.
  absurd (R y z); first assumption.
  etransitivity; eauto.
  intros.
  apply swo_irrefl with y.
  transitivity x; first assumption.
  etransitivity; eauto.

  move => x y.
  destruct (classic (R x y)).
  right; apply swo_asym; by eauto.
  apply swo_not_inv_or_incomp in H; destruct H.
    destruct H; tauto.
    left; apply swo_asym; by eauto.
  Qed.
  Instance swo_inv_comp_topo `(SWO:StrictWeakOrder A R) : TotalPreorder (inverse (complement R)).
  split.
    move => x.
    apply swo_irrefl.

    unfold complement, Basics.flip.
    pose swo_trans.
    move => x y z Hxy Hyz; simpl in *.
    apply swo_not_inv_or_incomp in Hxy.
    apply swo_not_inv_or_incomp in Hyz.
    move => H.
    destruct or Hxy; destruct or Hyz.
      move: H.
      eapply proj1.
      eapply swo_incomp_trans; eassumption.

      absurd (R y x).
        apply Hxy.
        etransitivity; eassumption.
      
      absurd (R z y).
        apply Hyz.
        etransitivity; eassumption.
      
      eapply swo_irrefl with x.
        transitivity y; first assumption.
        etransitivity; eassumption.

    unfold complement, Basics.flip.
    move => x y.
    destruct (classic (R x y)).
      apply swo_asym in H; tauto.
      apply swo_not_inv_or_incomp in H; destruct H.
        destruct H; tauto.
        apply swo_asym in H; tauto.
  Qed.
End TotalPreorder.









