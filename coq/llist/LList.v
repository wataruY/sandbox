Require Import ssreflect Program  Relations RelationClasses Setoid SetoidClass.
Require Import LList_defs.

Set Implicit Arguments.

Section Aux.
  Instance neq_sym A : Symmetric (fun x y : A => not (eq x y)).
  by firstorder.
  Qed.
End Aux.

Section LList.
  Generalizable Variables A.
  Open Scope llist_scope.
  Theorem listToLList_inj A : forall (xs ys:list A), listToLList xs = listToLList ys -> xs = ys.
  induction xs as [| x xs].
    by move => /= [?|?].
    move => /= [|? ?].
      discriminate.
      move => /= H.
      injection H => ? ->.
      f_equal; by intuition.
  Qed.

  Theorem llist_decomposition_lemma A (l:llist A) : l = llist_decompose l.
  by destruct l.
  Qed.

  Functional Scheme llist_decompose_n_ind := Induction for llist_decompose_n Sort Prop.
  Theorem llist_decompose_n_lemma (n:nat) `(l:llist A) : l = llist_decompose_n n l.
  functional induction (llist_decompose_n n l); try done.
  congruence.
  Qed.
  
  Definition llist_decomposition_lemma' := fun `(l:llist A) => eq_sym (llist_decomposition_lemma l).

  Hint Rewrite (@llist_decomposition_lemma' ) : llist.

  Ltac unfoldllist term :=
    apply trans_equal with (1 := llist_decomposition_lemma term).
  Ltac lhs H :=
    match goal with
      | [ |- ?X = _ ] => H X
    end.
  Ltac rhs H :=
    match goal with
      | [ |- _ = ?Y ] => H Y
    end.
  Ltac unfoldLl := lhs unfoldllist.
  Ltac unfoldLr := rhs unfoldllist.

  Theorem append_nil_l A (xs:llist A) : [] ++ xs = xs.
  unfoldLl; by case xs.
  Qed.

  Theorem append_cons_l A a (xs ys:llist A) : (a :: xs) ++ ys = a :: xs ++ ys.
  unfoldLl; unfoldLr.
  by autorewrite with llist.
  Qed.
  Hint Rewrite append_cons_l append_nil_l : llists.

  CoFixpoint from (n:nat) : llist nat := n :: from (S n).

  Lemma from_unfold n : from n = n :: from (S n).
  by unfoldLl.
  Qed.

  Lemma repeatL_unfold A (a:A) : repeat a = a :: repeat a.
  by unfoldLl.
  Qed.

  Lemma omega_nil A : omega [] = lnil A.
  by unfoldLl.
  Qed.
  Hint Rewrite omega_nil : llists.

  Lemma g_omega_nil A (u:llist A) : u +!+ [] = u.
  unfoldLl; unfoldLl.
  by case u.
  Qed.
  Hint Rewrite g_omega_nil : llists.
  Lemma g_omega_cons A (a:A) u v : g_omega (a :: u) v = a :: (g_omega u v).
  unfoldLl.
  case v => /=; by autorewrite with llists.
  Qed.
  Hint Rewrite g_omega_cons : llists.
  Lemma g_omega_nil_cons A (a:A) u : [] +!+ a :: u = a :: u +!+ a :: u.
  by unfoldLl; unfoldLr.
  Qed.
  Hint Rewrite g_omega_nil_cons : llists.
  Lemma g_omega_shoot_again A (v:llist A) : [] +!+ v = v +!+ v.
  unfoldLl; simpl.
  case v.
    by autorewrite with llists.
    move => b l.
    by autorewrite with llists.
  Qed.
  Hint Rewrite g_omega_shoot_again : llists.

  Lemma append_nil_r A (xs:llist A) (H:finite xs) : xs ++ [] = xs.
  induction H.
    by autorewrite with llists.
    autorewrite with llists.
    by f_equal.
  Qed.
  Hint Rewrite append_nil_r : llists.

  Definition F_from (H:forall n, infinite (from n)) n : infinite (from n).
  rewrite from_unfold.
  constructor.
  by trivial.
  Defined.

  Theorem from_infinite : forall n, infinite (from n).
    cofix H.
    intro n.
    by rewrite from_unfold.
  Qed.

  Lemma repeat_infinite A (x:A) : infinite (repeat x).
  cofix H.
  rewrite repeatL_unfold.
  by constructor.
  Qed.

  Lemma gomega_infinite A (a:A) : forall u v, infinite (v +!+ a :: u).
  cofix H.
  move => u v.
  destruct v; autorewrite with llists; by constructor.
  Qed.

  Lemma omega_infinite A (a:A) : forall l, infinite (omega (a :: l)).
  unfold omega.
  destruct l; by apply gomega_infinite.
  Qed.

  Theorem nil_not_infinite A : ~ infinite (lnil A).
  move => H.
  inversion H.
  Qed.

  Theorem infinite_cons_inv A (a:A) l : infinite (a :: l) -> infinite l.
  move => H.
  by inversion H.
  Qed.

  Lemma append_infinite A (u:llist A) : infinite u -> forall v, infinite (u ++ v).
  move => H v.
  revert dependent u.
  cofix IH => u H.
  inversion_clear H.
  autorewrite with llists.
  constructor; by intuition.
  Qed.

  Lemma finite_not_infinite A (u:llist A) : finite u -> ~ infinite u.
  move => Hf Hinf.
  induction Hf.
    inversion Hinf.
    apply IHHf.
    eapply infinite_cons_inv.
    eassumption.
  Qed.
              
  Lemma infinite_not_finite A (u:llist A) : infinite u -> ~ finite u.
  move => Hinf Hf.
  induction Hf.
    by inversion Hinf.
    apply IHHf.
    eapply infinite_cons_inv.
    by eassumption.
  Qed.

  Lemma not_finite_infinite A : forall (l:llist A), ~ finite l -> infinite l.
  cofix H.
  destruct l as [| a l] => H0.
    absurd (finite (lnil A)); first done.
    by constructor.
    constructor.
    apply H => H1.
    apply H0.
    by constructor.
  Qed.
  Hint Resolve not_finite_infinite infinite_not_finite finite_not_infinite append_infinite nil_not_infinite omega_infinite gomega_infinite repeat_infinite from_infinite : llists. 

  Section Classical.
    Require Import Classical.
    Lemma not_infinite_finite A (l:llist A) : ~infinite l -> finite l.
    move => H.
    apply NNPP.
    contradict H.
    by auto with llists.
    Qed.
    Lemma finite_or_infinite A (l:llist A) : finite l \/ infinite l.
    case (classic (finite l)) => H; by auto with llists.
    Qed.
  End Classical.

  Theorem infinite_infinite1 A (l:llist A) : infinite l -> infinite1 l.
  rewrite /infinite1 /infinite_ok => H.
  inversion_clear H.
  exists (@infinite A).
  split; last by constructor.
  move => ? H.
  inversion_clear H.
  do 2 eexists.
  by split.
  Qed.

  Theorem infinite1_nil A : ~ infinite1 (@lnil A).
  rewrite /infinite1 /infinite_ok.
  move => H.
  destruct H as [X [H Xnil]].
  destruct (H _ Xnil).
  by destruct_conjs.
  Qed.

  Theorem infinite1_cons_inv A (a:A) l : infinite1 (a :: l) -> infinite1 l.
  rewrite /infinite1 /infinite_ok.
  move => H.
  destruct H as [X [H Xal]].
  exists X.
  assert (Xl : X l).
    destruct (H _ Xal) as [? [? [H0 ?]]].
    injection H0; congruence.
  tauto.
  Qed.

  Theorem infinite1_infinite A  : forall (l:llist A), infinite1 l -> infinite l.
  cofix IH.
  destruct l => H.
    by absurd (infinite1 (@lnil A)); first apply infinite1_nil.
    apply infinite1_cons_inv, IH in H.
    by constructor.
  Qed.
  Program Instance llist_oid A : Setoid (llist A) := { equiv := @bisimilar A }.
  Next Obligation.
  split; cofix IH.
    move => l; destruct l.
      by constructor.
      by constructor; apply IH.
    move => ? ? H.
    inversion_clear H.
      by constructor.
      by constructor; apply IH.
    move => ? y ? H0 H1.
    destruct y; inversion_clear H0; inversion_clear H1.
      by constructor.
      constructor.
      eapply IH; by eassumption.
  Qed.

  Instance bisim_cons_proper A : Proper (eq ==> equiv ==> equiv) (@lcons A).
  move => ? ? H0 ? ? H1; rewrite H0.
    by constructor.
  Qed.

  Instance bisimilar_Nth_morph (A:Type) : forall n, Proper (equiv ==> eq) (@nth n A).
  induction n as [| p] => /= ? ? Heq; inversion_clear Heq; try done.
  by intuition.
  Qed.

  Theorem Nth_bisimilar_morph (A:Type) : forall (l:llist A) l', (forall n, l !! n = l' !! n ) -> l == l'.
  cofix IH => l l' H.
  destruct l as [| a ?]; destruct l' as [| b ?];
    reflexivity || (assert (H' := H 0); discriminate) || idtac.
  replace a with b.
      constructor.
      apply IH.
      move => m.
      by assert (H' := H (S m)).
    assert (H' := H 0).
    by injection H'.
  Qed.
              
  Theorem bisimilar_finite (A:Type) (l:llist A) l' : l == l' -> finite l -> finite l'.
  move => H Hf.
  revert dependent l'.
  induction Hf => l H; inversion_clear H.
    by constructor.
    constructor; by intuition.
  Qed.

  Theorem infinite_ex_cons (A:Type) (l:llist A) (H:infinite l) : exists a l', l = a :: l'.
  inversion_clear H.
  eauto.
  Qed.

  Theorem bisimilar_infinite (A:Type) : forall (l:llist A) l', l == l' -> infinite l -> infinite l'.
  cofix IH => l l' Heq Hinf.
  destruct l'.
    inversion Heq.
    by replace l with (lnil A) in Hinf.
    constructor.
    pose (H:=infinite_ex_cons Hinf).
    destruct_exists; subst.
    apply infinite_cons_inv in Hinf.
    inversion_clear Heq.
    eapply IH; eassumption.
  Qed.
              
  Theorem finite_bisim_eq (A:Type) (l:llist A) l' : finite l -> l == l' -> l = l'.
  move => Hf.
  move: l'.
  induction Hf => l.
    by inversion 1.
    inversion_clear 1.
    f_equal.
    by intuition.
  Qed.
  Delimit Scope llist_scope with llist.
  Infix "++" := append.
  Theorem append_assoc A  : forall (u v w:llist A), u ++ v ++ w == u ++(v ++ w).
  Proof with by intuition.
  cofix IH.
  move => u *.
  destruct u.
    rewrite append_nil_l...
    rewrite append_cons_l...
  Qed.

  Theorem append_infinite_id_r A : forall (u v:llist A), infinite u -> (u ++ v == u)%llist.
  cofix IH.
  destruct u => v Hv.
    by inversion Hv.
    rewrite append_cons_l.
    constructor.
    apply IH.
    by apply infinite_cons_inv in Hv.
  Qed.

  Theorem bisim_g_omega_proper A : Proper (equiv ==> equiv ==> equiv) (@g_omega A).
  cofix IH.
  move => ? ? H0 ? ? H1.
  inversion_clear H1.
    by do 2 rewrite g_omega_nil.
    inversion_clear H0.
      do 2 rewrite g_omega_nil_cons.
      constructor.
      apply IH; first done.
      by apply bisim_cons_proper.
      do 2 rewrite g_omega_cons.
      constructor.
      apply IH; first done.
      by apply bisim_cons_proper.
  Qed.

  Instance bisim_append_proper A : Proper (equiv ==> equiv ==> equiv) (@append A).
  cofix IH.
  move => ? ? H0 ? ? H1.
  inversion_clear H0.
    by do 2 rewrite append_nil_l.
    do 2 rewrite append_cons_l.
    constructor.
    by apply IH.
  Qed.

  Theorem g_omega_append A : forall (u v:llist A), g_omega u v == u ++ g_omega v v.
  cofix IH.
  destruct u => v.
    rewrite g_omega_shoot_again append_nil_l.
    reflexivity.
    rewrite g_omega_cons append_cons_l.
    constructor.
    by apply IH.
  Qed.

  Theorem g_omega_append_fix A : forall (u v:llist A), u == v -> g_omega u v == u ++ g_omega u v.
  move => *.
  etransitivity;first apply g_omega_append.
  apply bisim_append_proper; first reflexivity.
  apply bisim_g_omega_proper ; last reflexivity.
  by symmetry.
  Qed.

  Theorem omega_append A (u:llist A) : omega u == u ++ omega u.
  unfold omega.
  apply g_omega_append_fix; reflexivity.
  Qed.

  Theorem park_principal A (R:relation (llist A)) :
    bisimulation R -> forall t u, R t u -> t == u.
  cofix IH => Hr t u H.
  assert (H' := Hr _ _ H).
  destruct t; first by (subst; reflexivity).
  destruct u; first contradiction.
  destruct_conjs; subst.
  constructor.
  by apply IH.
  Qed.

  Section Alter.
    CoFixpoint alter : llist bool := true :: false :: alter.
    Let alter2 : llist bool := omega (true :: false :: []).

    Let R : relation (llist bool) :=
      fun t u => t = alter /\ u = alter2 \/
                    t = false :: alter /\ u = false :: alter2.

    Lemma alter_infinite : infinite alter.
    unfold alter.
    cofix IH.
    erewrite llist_decomposition_lemma; simpl.
    by do 2 constructor.
    Qed.

    Lemma finite_neq_infinite A (t u:llist A): finite t -> infinite u -> t <> u.
    move => H.
    move: u.
    induction H.
    move => ?; by inversion 1.
    move => u Hu.
    move => H0.
    destruct u; first discriminate.
    injection H0 => *.
    eapply IHfinite; last eassumption.
    by inversion Hu.
    Qed.

    Lemma alter_neq_nil : alter <> [].
    apply neq_sym.
    apply finite_neq_infinite.
      by constructor.
      by apply alter_infinite.
    Qed.

    Lemma alter2_neq_nil : alter2 <> [].
    apply neq_sym.
    apply finite_neq_infinite;first by constructor.
    apply omega_infinite.
    Qed.

    Theorem R_bisimulation : bisimulation R.
    move => t u Hr.
    destruct t; destruct u.
      done.
      destruct or Hr.
        destruct Hr as [H].
        contradict H.
        apply neq_sym.
        by apply alter_neq_nil.
        by destruct_conjs.
      destruct or Hr.
        destruct Hr as [_ H].
        contradict H.
        apply neq_sym.
        apply alter2_neq_nil.
        by destruct_conjs.
      destruct or Hr;(
      destruct Hr as [H0 H1];
      erewrite llist_decomposition_lemma in H0,H1; simpl in *;
      injection H0 => -> ->; injection H1 => -> ->; split; first done).
        right.
        split; first done.
        rewrite g_omega_cons.
        f_equal.
        by rewrite g_omega_shoot_again.
        left.
        by split.
    Qed.

    Theorem alter_alter2_bisimilar : alter == alter2.
    apply (park_principal R_bisimulation).
    by left.
    Qed.
  End Alter.
End LList.

Section LTL.
  Open Scope llist_scope.
  Variable (A:Type) (a b c:A).

  Definition satisfies (l:llist A) (P:llist A -> Prop) : Prop := P l.
  Hint Unfold satisfies : llists.

