Require Import List Sorted.
Require Import SetoidClass.
Require Import Setoid.
Require Import SWO.
Require Import Relation_Operators.
Require Import span.
Require Import Program.Tactics.
Require Import Permutation.

Set Implicit Arguments.
Unset Strict Implicit.
Generalizable Variables A R.

Local Notation "[ ]" := nil (at level 0).
Local Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..) (at level 0).

Section Insert.
  Context `(SWO: StrictWeakOrder A R).
  Let incomp_equiv := swo_incomp_equiv SWO.
  Let lt := R.
  Let le := (union _ R (incomp R)).
  Infix "<=" := le.
  
  Infix "<" := lt.
  Let gt := inverse R.
  Theorem le_not_lt x y : x <= y -> ~ y < x.
  intros H.
  destruct H.
  intro.
  eapply swo_asym; eauto.
  destruct H; assumption.
  Qed.
  Theorem lt_not_le x y : x < y -> ~ y <= x.
  intro H.
  intros [H0|H1].
  eapply swo_asym; eauto.
  destruct H1; contradiction.
  Qed.
  
  Hypothesis swo_total : forall x y, {R x y}+{~R x y}.
  
  Definition insert_prop (a:A) (xs l:list A) : Prop.
  pose (H:=span_weak (fun (x:A) => swo_total x a) xs).
  destruct H as [ys zs].
  exact (l = ys ++ [a] ++ zs).
  Defined.
  Fixpoint insert_strong a xs : {l:list A|insert_prop a xs l}.
  unfold insert_prop.
  induction xs as [| b xs].
   exists [a].
   destruct (span (fun x : A => swo_total x a) []).
   destruct_exists.
   unfold span_prop in *.
   destruct_conjs.
   symmetry  in H.
   apply app_eq_nil in H; destruct H; subst.
   reflexivity.
   
   destruct_exists.
   simpl in *.
   destruct (span_weak (P:=fun x : A => R x a) (fun x : A => swo_total x a) xs).
   destruct (swo_total b a).
    simpl.
    rewrite <- H.
    eexists; reflexivity.
    
    simpl.
    eauto.
  Defined.
  Fixpoint insert_weak (a:A) (xs:list A) : list A :=
    match xs with
      | [] => [a]
      | x :: ys => if swo_total x a then x :: insert_weak a ys else a :: xs
    end.
  Theorem insert_correct a xs : insert_weak a xs = proj1_sig (insert_strong a xs).
  destruct (insert_strong a xs).
  simpl in *.
  revert dependent a (* Generic printer *).
  revert x.
  induction xs.
   simpl.
   intros.
   unfold insert_prop in *.
   simpl in *.
   congruence.
   
   intros ys b.
   simpl.
   case_eq (swo_total a b).
    intros.
    unfold insert_prop in *.
    simpl in *.
    rewrite H in i.
    remember
     (span_weak (P:=fun x : A => R x b) (fun x : A => swo_total x b) xs) as zs.
    destruct zs.
    rewrite i.
    simpl; f_equal.
    apply IHxs.
    rewrite <- Heqzs.
    reflexivity.
    
    intros.
    unfold insert_prop in i.
    simpl in *.
    rewrite H in i.
    simpl in *.
    subst.
    reflexivity.
  Qed.
  Theorem insert_preserve_sorted a l : Sorted le l -> Sorted le (insert_weak a l).
  revert a.
  induction l.
   constructor; constructor.
   
   intros b Hsorted.
   simpl.
   case_eq (swo_total a b); intros r Hle.
    constructor.
     apply IHl.
     apply Sorted_inv in Hsorted; destruct_conjs.
     assumption.
     
     clear IHl.
     inversion_clear Hsorted.
     destruct l.
      simpl.
      constructor; left; assumption.
      
      simpl in *.
      destruct (swo_total a0 b).
       constructor.
       inversion_clear H0.
       assumption.
       
       constructor.
       left; assumption.
       
    constructor.
     assumption.
     
     constructor.
     destruct (swo_not_inv_or_incomp _ _ r).
      right.
      rewrite H.
      reflexivity.
      
      left; assumption.
  Qed.
  Instance Perm_oid : Setoid (list A) := {| equiv := @Permutation _ |}.
  Theorem insert_perm a l : proj1_sig (insert_strong a l) == (a :: l).
    rewrite <- insert_correct.
    revert a; induction l as [|x xs].
    reflexivity.
    simpl insert_weak.
    intro a; destruct (swo_total x a).
    rewrite IHxs.
    rewrite perm_swap.
    reflexivity.
    reflexivity.
  Qed.
  Definition isort_strong xs : {l:list A|Sorted le l /\ xs == l}.
  induction xs.
   eexists.
   (split ; last  reflexivity).
   constructor.
   
   destruct_exists; destruct_conjs.
   eexists; split.
    apply insert_preserve_sorted.
    eassumption.
    
    rewrite H0.
    rewrite <- insert_perm.
    rewrite <- insert_correct.
    reflexivity.
  Defined.
End Insert.

Recursive Extraction isort_strong.