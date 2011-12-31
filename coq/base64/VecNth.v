Require Import ssreflect.
Require Import Arith Omega Setoid EqdepFacts.
Require Import Bvector.
Require Import MinMax.
Require Import Setoid SetoidClass.
Require Import NthElemOf.
Require Import Program.

Require ListSplit.

Set Implicit Arguments.

Section VectorNth.
  Generalizable Variable A B m n xs ys.

  (* Fixpoint iterate `(f:A->A) (n:nat) (e:A) := *)
  (*   match n with *)
  (*     | 0 => e *)
  (*     | S p => f (iterate f p e) *)
  (*   end. *)
  (* Definition Viterate {A} (g:nat -> nat) (f:forall n:nat, vector A n -> vector A (g n)) m `(v:vector A n) : *)
  (*   vector A (iterate g m n). *)
  (* induction m => /=. *)
  (*   exact v. *)
  (*   apply f. *)
  (*   exact IHm. *)
  (* Defined. *)

  Inductive In `(a:A) : forall n, vector A n -> Prop :=
  | In1 `(v:vector A n) : In a (Vcons a v)
  | In2 b `(v:vector A n) : In a v -> In a (Vcons b v).
  Definition Included `(xs:vector A n) `(ys:vector A m) := forall x, In x xs -> In x ys.
  Theorem In_inv `(x:A) `(xs:vector A n)  : forall y, In x (Vcons y xs) -> x = y \/ In x xs.
  move => y H.
  dependent destruction H; tauto.
  Qed.
  Definition Vapp_strong `(xs:vector A n) `(ys:vector A m) :
    {zs:vector A (n + m) | forall x:A, In x xs \/ In x ys -> In x zs}.
  induction xs as [|x ? xs].
    exists ys.
    move => ? [x_in_Vnil|?].
      by inversion x_in_Vnil.
      done.
    destruct IHxs as [zs Hzs].
    exists (Vcons x zs) => y [y_in_xs | y_in_ys].
    apply In_inv in y_in_xs.
    destruct y_in_xs as [y_eq_x | y_in_xs].
      subst; by constructor.
      apply In2, Hzs; tauto.
      apply In2, Hzs; tauto.
  Defined.

  Definition Vapp `(xs:vector A n) `(ys:vector A m) : vector A (n + m).
  induction xs as [|x n xs].
    exact ys.
    constructor; first exact x.
    apply IHxs.
  Defined.

  Lemma Vcons_heq `(a:A) `(xs:vector A n) `(ys:vector A m) :  n = m -> xs ~= ys -> Vcons a xs ~= Vcons a ys.
  move => ?; subst.
  move => H.
  apply JMeq_eq_dep_id in H.
  by dependent induction H.
  Qed.

  Theorem vector_0_nil `(v:vector A n) : n = 0 -> v ~= Vnil A.
  move => H.
  by dependent induction v.
  Qed.

  Theorem vector_s_uncons `(v:vector A (S n)) : {a:A & {w:vector A n | v = Vcons a w}}.
    dependent destruction v.
    eauto.
  Qed.

  Inductive NthP `(a:A) : nat -> forall n, vector A n -> Prop :=
  | NthP_hd `(v:vector A n) : NthP a 0 (Vcons a v)
  | NthP_tl b i `(v:vector A n) : NthP a i v -> NthP a (S i) (Vcons b v).

  Definition vector_equiv A n : relation (vector A n) :=
    fun xs ys => forall (a:A) i, i < n -> (NthP a i xs <-> NthP a i ys).
  Program Instance VectorOid `(Aoid:Setoid A) n : Setoid (vector A n) :=
    { equiv := @vector_equiv A n}.
  Next Obligation.
    unfold vector_equiv.
    split; autounfold.
      tauto.
      firstorder.
      move => ? ? ? H0 *.
      etransitivity.
      by apply H0.
      by firstorder.
  Qed.

  Fixpoint nth m `(v:vector A n)  : {a:A | NthP a m v}+{n < S m}.
  dependent destruction v.
    right; by auto with arith.
    destruct m as [|m].
      left; eexists; by constructor.
      destruct (nth m _ _ v) as [[b H]|H].
        left; eexists; constructor.
        eassumption.
        right; omega.
  Defined.

  Definition list_to_vec `(xs:list A) :
    {v:vector A (length xs) | forall a i, NthElemOf a i xs -> NthP a i v}.
  induction xs as [|x xs].
  eexists Vnil.
    move => ? ? H.
    inversion H.
  destruct IHxs as [v Hv].
  simpl.
  exists (Vcons x v).
  move => a i H.
  inversion_clear H.
    by constructor.
    constructor.
    by apply Hv.
  Defined.

  Definition vec_to_list `(v:vector A n) :
    {l:list A | forall a i, NthP a i v -> NthElemOf a i l}.
  induction v as [|x n xs].
    eexists nil => ? ? H.
    by inversion H.
    destruct IHxs as [l Hl].
    exists (cons x l).
    move => a i H.
    dependent destruction H.
      by constructor.
      constructor.
      by apply Hl.
  Defined.

  Fixpoint list_to_vec_weak {A} `(xs:list A) : vector A (length xs) :=
    match xs with
      | nil => Vnil
      | cons a l => Vcons a (list_to_vec_weak l)
    end.

  Functional Scheme list_to_vec_weak_ind := Induction for list_to_vec_weak Sort Prop.
  Theorem list_to_vec_weaken {A} `(xs:list A) : proj1_sig (list_to_vec xs) = list_to_vec_weak xs.
  destruct (list_to_vec xs) as [ys]; simpl.
  induction xs as [|x xs].
  by dependent destruction ys.
  dependent destruction ys.
  match goal with
    | [ YS: vector _ (length xs) ,
        X: A, A: A,
        H: forall _ _, NthElemOf _ _ (?X :: xs)-> NthP _ _ (Vcons a ?YS) |- _]  =>
        rename A into y; rename YS into ys; rename H into Hys
  end.
  rewrite (IHxs ys).
  assert (H0 : NthElemOf x 0 (x :: xs)).
    by constructor.
  assert (H1 := Hys _ _ H0).
  dependent destruction H1.
  by apply JMeq_eq,Vcons_heq.
  move => b i H.
  eapply neo_k in H.
  instantiate (1:= x) in H.
  assert (H0 :=Hys _ _ H).
  by dependent destruction H0.
  Qed.

  Open Scope list_scope.
  Fixpoint vec_to_list_weak `(xs:vector A n) : list A.
  destruct xs as [| x n xs].
    exact []%list.
    refine (x :: _).
    eapply vec_to_list_weak.
      apply xs.
  Defined.
  
  Functional Scheme vec_to_list_weak_ind := Induction for vec_to_list_weak Sort Prop.

  Lemma vec_to_list_red `(xs:vector A n) : forall a, proj1_sig (vec_to_list (Vcons a xs)) = a :: proj1_sig (vec_to_list xs).
  induction xs.
    done.
    simpl in *.
    destruct (vec_to_list xs); simpl in *.
    by intuition.
  Qed.
  Lemma vec_to_list_weak_red `(xs:vector A n) : forall a, vec_to_list_weak (Vcons a xs) = a :: vec_to_list_weak xs.
  by destruct xs.
  Qed.

  Theorem vec_to_list_weaken `(xs:vector A n) : proj1_sig (vec_to_list xs) = vec_to_list_weak xs.
  remember (vec_to_list xs) as zs.
  induction xs.
  destruct zs.
  simpl.
  by inversion Heqzs.
  rewrite vec_to_list_weak_red.
  rewrite Heqzs.
  rewrite vec_to_list_red.
  f_equal.
  by apply IHxs.
  Qed.

  Theorem list_to_vec_proper A (xs ys:list A) (Hlength:xs = ys) :
    let ws := (proj1_sig (list_to_vec xs))
    in let vs := (proj1_sig (list_to_vec ys))
       in forall a i, i < length xs -> (NthP a i ws <-> NthP a i vs).
  do 2 rewrite  list_to_vec_weaken; simpl.
  by destruct Hlength.
  Qed.

  Definition Vapp_strong2 `(xs:vector A m) `(ys:vector A n) :
    {zs:vector A (m + n) | vec_to_list_weak zs = vec_to_list_weak xs ++ vec_to_list_weak ys}.
  induction xs as [|x m xs] => /=.
  by exists ys.
  destruct IHxs as [zs Hzs].
  exists (Vcons x zs).
  simpl; by congruence.
  Defined.

  Goal forall `(xs:vector A m) `(ys:vector A n), proj1_sig (Vapp_strong xs ys) = proj1_sig (Vapp_strong2 xs ys).
  move => ? ? xs ? ys.
  induction xs.
    done.
    simpl in *.
    destruct (Vapp_strong xs ys); destruct (Vapp_strong2 xs ys).
    simpl in *.
    by congruence.
  Qed.

  Fixpoint replicate `(a:A) n : {v:vector A n | forall i, i < n -> NthP a i v}.
  destruct n as [|n].
  eexists Vnil.
  move => ? H; contradict H; by auto with arith.
  destruct (replicate _ a n) as [v Hv].
  exists (Vcons a v).
  induction i.
    constructor.
    move => H.
    constructor.
    apply Hv.
    omega.
  Defined.

  Fixpoint replicate_weak `(a:A) m : vector A m.
  induction m.
    exact Vnil.
    constructor.
    apply a.
    apply replicate_weak.
    apply a.
  Defined.

  Theorem replicate_weaken `(a:A) m : proj1_sig (replicate a m) = replicate_weak a m.
  induction m => /=.
    by apply JMeq_eq,vector_0_nil.
    destruct (replicate a m) as [x Hx]; simpl in *.
    congruence.
  Qed.

  Theorem Vapp_nil `(xs:vector A m) : Vapp xs Vnil ~= xs.
  dependent induction xs => /=.
    reflexivity.
    apply Vcons_heq.
      by auto with arith.
      done.
  Qed.

  Fixpoint take m `(xs:vector A n) :
    {ys:vector A (min m n) | vec_to_list_weak ys = ListSplit.take m (vec_to_list_weak xs)}.
  destruct m as [|m]; [rewrite min_0_l; by eexists Vnil|].
  destruct xs as [|x n xs].
    rewrite min_0_r; by eexists Vnil.
  destruct (take m _ _ xs) as [ys Hys].
  rewrite <- succ_min_distr.
  exists (Vcons x ys).
  simpl; by f_equal.
  Defined.

  Fixpoint take_weak m `(xs:vector A n) : vector A (min m n) :=
    match m with
      | 0 => Vnil
      | S p => match xs with
                 | Vnil => Vnil
                 | Vcons a _ v => Vcons a (take_weak p v)
               end
    end.
  
  Functional Scheme take_weak_ind := Induction for take_weak Sort Prop.
  
  Theorem take_weaken m `(xs:vector A n) : proj1_sig (take m xs) = take_weak m xs.
  destruct (take m xs).
  functional induction (take_weak m xs); simpl in *; try by apply JMeq_eq, vector_0_nil.
    match goal with
      | [V:vector A (S (min ?P ?N)) |- _] => rename P into q; rename N into r; rename V into w
    end.
    dependent destruction w; simpl in *|-.
    match goal with
      | [H:_ :: _ = _ :: _ |- _] => injection H
    end.
  move => H ->.
  apply IHv in H.
  congruence.
  Qed.

  Fixpoint list_to_vec_with_padding n `(a:A) (xs:list A) :
    {v:vector A n | vec_to_list_weak v = ListSplit.take n xs ++ vec_to_list_weak (replicate_weak a (n - length xs))}.
  destruct xs as [|x xs].
  eexists (replicate_weak a n).
  simpl.
  rewrite <- minus_n_O.
  by rewrite (ListSplit.take_nil).
  destruct n as [|p].
  by eexists Vnil.
  simpl.
  destruct (list_to_vec_with_padding p _ a xs) as [ v Hv].
  exists (Vcons x v).
  simpl; f_equal.
    congruence.
  Defined.

  Fixpoint take m `(xs:vector A n) :
    {ys:vector A (min m n) & {zs:vector A (n - m) | xs ~= Vapp ys zs}}.
  destruct m as [|m].
    rewrite <- minus_n_O; rewrite min_0_l.
    eexists Vnil; exists xs.
    done.
    destruct xs as [|x n v].
    by eexists Vnil; eexists Vnil.
    destruct (take m _ _ v) as [ys [zs H]].
    rewrite <- succ_min_distr.
    simpl minus.
    exists (Vcons x ys); exists zs; simpl.
    apply Vcons_heq; last done.
    change (n = min m n + (n - m)).
    destruct (min_dec m n) as [Hm | Hn].
      rewrite Hm.
      apply le_plus_minus.
      by apply min_l_iff.
      rewrite Hn.
      apply min_r_iff in Hn.
      apply le_lt_eq_dec in Hn.
      destruct or Hn.
        rewrite not_le_minus_0; first auto with arith.
        by apply lt_not_le.
        by subst; auto with arith.
  Defined.

  Fixpoint drop m `(xs:vector A n) :
    {ys:vector A (n - m) & {zs:vector A (min m n) | xs ~= Vapp zs ys}}.
  destruct m as [|m].
    rewrite <- minus_n_O.
    exists xs; eexists Vnil.
    reflexivity.
  destruct xs as [|x n xs].
    do 2 eexists Vnil.
    reflexivity.
  destruct(drop m _ _ xs) as [ys [zs H]].
  apply JMeq_eq_dep_id in H.
  dependent destruction H.
  exists ys.
  match goal with
    | [ X:A |- _ ] => revert X
  end.
  move => a.
  exists (Vcons a zs).
  simpl.
  apply Vcons_heq.
  change (n = min m n + (n - m)).
  destruct (min_dec m n) as [H0|H1].
    rewrite H0.
    apply le_plus_minus.
    by apply min_l_iff.
    assert (Hnm : n - m = 0).
      apply min_r_iff in H1.
      apply le_lt_eq_dec in H1.
      destruct or H1.
        apply not_le_minus_0.
        by apply lt_not_le.
        subst; apply minus_diag.
    by rewrite Hnm plus_0_r.
    done.
  Defined.
