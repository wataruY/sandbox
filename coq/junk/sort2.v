Require Import List.
Require Import Setoid.
Require Import Permutation.
Require Import SetoidClass.
Require Import Relations.
Require Import Program.

Program Instance perm_setoid {A:Type} : Setoid (list A) :=
{ equiv := Permutation (A:=A) }.


Section Sorting.

Variable A:Type.
Variable Le Gt:relation A.

Inductive sorted : list A -> Prop :=
  | sort0 : sorted nil
  | sort1 : forall x, sorted (x :: nil)
  | sort2 : forall x y l, Le x y -> sorted (y :: l) -> sorted (x :: y :: l).

Theorem sorted_inv x l : sorted (x :: l) -> sorted l.
inversion 1;[constructor|assumption].
Qed.

Hypothesis Le_Gt_dec : forall x y:A, {Le x y}+{Gt x y}.
Hypothesis Gt_Le : forall x y, Gt y x -> Le x y.
Hypothesis Le_asym : forall x y, Le x y -> ~ Le y x.

Hypothesis Le_not_Gt : forall x y, Le x y -> ~ Gt x y.
Hypothesis Le_trans : Transitive Le.

Theorem sorted_sw a b l : Le a b -> sorted (b::l) -> sorted (a::l).
intros Hle Hsort.
induction l.
constructor.
inversion_clear Hsort.
constructor.
transitivity b;assumption.
assumption.
Qed.

Fixpoint insert x l :=
  match l with 
     | nil => x :: nil
     | a :: l' => if Le_Gt_dec x a then x :: l else a :: insert x l'
  end.


Theorem insert_equiv x l : insert x l == x :: l.
induction l.
reflexivity.
simpl.
case (Le_Gt_dec x a).
reflexivity.
intro.
rewrite IHl.
constructor.
Qed.

Theorem insert_sorted x l : sorted l -> sorted (insert x l).
intros H; elim H.
constructor.
simpl.
intro y.
case (Le_Gt_dec x y).
  intros Hle.
  constructor;[assumption|constructor].
  intro H0.
  apply Gt_Le in H0.
  constructor.
  assumption.
  constructor.
  intros y z l' Hyz Hzl Hins.
  simpl.
  case (Le_Gt_dec x y).
  intro Hxy.
  constructor.
  assumption.
  constructor.
  assumption.
  assumption.
  intro H0.
  revert Hins.
  simpl.
  case (Le_Gt_dec x z); intros H1 Hsort.
  constructor.
  apply Gt_Le; assumption.
  assumption.
  constructor.
  assumption.
  assumption.
Qed.

Definition ins_sort (xs:list A) : {l|l == xs /\ sorted l}.
induction xs.
exists (nil (A:=A)).
split.
reflexivity.
constructor.

destruct IHxs as [ys [Heq Hsort]].
eapply exist.
split.
rewrite <- Heq.
rewrite <- insert_equiv.
reflexivity.
apply insert_sorted; assumption.
Defined.

Definition ins_sort' l := proj1_sig (ins_sort l).

Section QuickSort.


Definition Leb (x y:A) : bool :=
  if Le_Gt_dec x y then true else false.
  
Hypothesis Le_refl : Reflexive Le.
Variable EQ : relation A.
Hypothesis EQ_dec : forall x y:A, {x=y}+{x<>y}.


Section EveryP.


Section Minimum.

Inductive everyP (P:A->Prop) : list A -> Prop :=
  | every0 : everyP P nil
  | every1 a l : P a -> everyP P l -> everyP P (a::l).

Theorem everyP_inv (P:A->Prop) a l : everyP P (a::l) -> (forall x, In x (a::l) -> P x).
intros Hp x.
induction Hp.
intro H; contradict H; auto with datatypes.
intro Hx.
case (in_inv Hx).
intro; subst; assumption.
trivial.
Qed.

Theorem everyP_intro (P:A->Prop) l : (forall x, In x l -> P x) -> everyP P l.
intro H.
induction l.
constructor.
constructor.
apply H.
left; auto.
apply IHl.
intros x Hin.
apply (H x (in_cons a x l Hin)).
Qed.

Definition minimumP (a:A) : list A -> Prop :=
  everyP (Le a).

Theorem sorted_minimum a l :
sorted (a::l) -> minimumP a l.
induction l.
constructor.
intro H.
constructor.
inversion H.
assumption.
apply IHl.
inversion_clear H.
eapply sorted_sw.
eassumption.
assumption.
Qed.

Theorem incl_con (a:A) l : incl l (a::l).
eapply incl_tl.
apply incl_refl.
Qed.

Theorem cons_incl_nil (a:A) l : ~ incl (a :: l) nil.
unfold incl.
intro H.
assert (H':=H a (in_eq _ _)).
inversion H'.
Qed.

Theorem nil_incl (l:list A) : incl l nil <-> l = nil.
induction l.
split.
reflexivity.
intro;apply incl_refl.
split.
intro.
apply cons_incl_nil in H.
contradiction.
discriminate.
Qed.

(* ∀x:l, P x ∧  b:l -> P b*)
Theorem incl_cons_case (a b:A) l l' :
incl (a :: l) (b :: l') ->  a = b \/ In a l'. 
unfold incl.
intro H.
assert (H':=H a (in_eq _ _)).
destruct (in_inv H') as [H0|H0].
auto.
tauto.
Qed.

Theorem in_everyP a l P : everyP P l -> In a l -> P a.
intros Hevery Hin.
induction Hevery.
inversion Hin.
destruct (in_inv Hin) as [H0|H0].
rewrite <- H0; assumption.
apply IHHevery.
assumption.
Qed.

Theorem incl_red_l (a:A) l l' : incl (a::l) l' -> incl l l'.
unfold incl.
intros H x Hx.
apply H.
right; auto.
Qed.

Theorem incl_cons_red (a b:A) l l' :
incl (a::l) (b::l') -> incl l (b::l').
intro.
eapply incl_tran.
2:apply H.
auto with datatypes.
Qed.

Theorem incl_inv (a b:A) l l' :
incl (a::l) (b::l') -> a = b \/ In a l'.
intro H.
induction l.
assert (H':In a [a]).
auto with datatypes.
destruct (in_inv (H a H')).
left.
auto.
tauto.
apply IHl.
unfold incl in H.
unfold incl.
intros x Hx.
apply (H x).
simpl.
case (in_inv Hx);tauto.
Qed.

Theorem app_red l1 l2 (a:A) : l1 ++ a :: l2 == a :: (l1++l2).
induction l1.
auto.
reflexivity.
simpl app.
rewrite IHl1.
simpl.
constructor.
Qed.

Theorem incl_nil (l:list A) : incl [] l.
unfold incl.
intros x H.
inversion H.
Qed.

(* Theorem perm_incl_mut (l:list A) l' : Permutation l l' -> incl l l' /\ incl l' l. *)
(* intros H. *)
(* induction H. *)
(* split;apply incl_nil. *)



(* Instance incl_proper : Proper (equiv ==> (Permutation (A:=A))  ==> flip impl) (incl (A:=A)). *)
(* intros xs ys Heq. *)
(* intros zs ws Hperm. *)
(* intro H. *)


(* Theorem incl_perm_preserv_l (l:list A) l' l'' : l == l' -> incl l l'' -> incl l' l''. *)
(* intros Heq Hinc. *)
(* rewrite <- Heq. *)
 

Section hoge.
Implicit Arguments incl.
Variable c:A.
Hypothesis incl_cons_same : forall (x:A) (l l':list A), incl (x::l) (x::l') -> incl l l'.

Let l0:= c :: nil.
Let l1:= nil(A:=A).


Goal False.
assert (H:incl (c::l0) (c::l1)).
unfold incl.
intros.
case (in_inv H).
intro.
rewrite H0.
auto with datatypes.
unfold l0.
unfold l1.
trivial.
assert (H' := incl_cons_same c l0 l1 H).
unfold incl in H'.
assert (cInl0:In c l0).
unfold l0.
auto with datatypes.
assert (cInl1':~In c l1).
unfold l1.
auto with datatypes.
contradict cInl1'.
apply (H' c cInl0).
Qed.

End hoge.

Theorem incl_cons_nin_weak (a:A) l l' : incl l (a::l') -> ~ In a l -> incl l l'.
unfold incl.
intros Hincl Hnin x Hin.
case (EQ_dec x a).
intros.
subst.
contradiction.
intro Hneq.
case (in_inv (Hincl x Hin)).
intro H; symmetry in H.
contradiction.
trivial.
Qed.

Theorem incl_preserve_min P l l' :
everyP P l /\ incl l' l -> everyP P l'.
intros [Hp Hinc].
induction Hp.
apply nil_incl in Hinc.
rewrite Hinc.
constructor.
case (in_dec EQ_dec a l').
Focus 2.
intro Hnin.
apply IHHp.
apply (incl_cons_nin_weak a l' l Hinc Hnin).
assert (Hevery:= everyP_inv P a l (every1 P a l H Hp)).
intro Hin.
apply everyP_intro.
intros x Hx.
apply Hevery.
unfold incl in Hinc.
apply Hinc.
assumption.
Qed.

End Minimum.

Fixpoint filter_split (p:A->bool) (xs:list A) : (list A * list A) :=
  match xs with
     | nil => (nil,nil)
     | a :: l => let (ys,zs) := filter_split p l
              in if p a then (a::ys,zs) else (ys,a::zs)
  end.

Theorem bool_pred_has_rel {T:Type} (p:T->bool) : {P: T -> Prop|
forall x:T, (p x = true <-> P x ) /\ (p x = false <-> ~P x)}.
exists ((fun x:T => p x = true)).
intros x.
split.
tauto.
split.
intro;subst.
rewrite H.
discriminate.
intro H.
destruct (p x).
contradict H; tauto.
reflexivity.
Qed.

Theorem filter_incl (p:A->bool) xs : incl (filter p xs) xs.
induction xs.
simpl.
auto with datatypes.
simpl.
case (p a).
apply incl_cons.
apply in_eq.
apply incl_tl.
assumption.
apply incl_tl.
assumption.
Qed.

Theorem filter_p_np_perm (p:A->bool) xs : filter p xs ++ filter (negb ∘ p) xs == xs.
induction xs.
constructor.
simpl filter.
unfold compose.
unfold negb.
case (p a).
simpl app.
rewrite perm_skip;[reflexivity|].
apply IHxs.
rewrite Permutation_app_comm.
simpl app.
rewrite perm_skip;[reflexivity|].
rewrite Permutation_app_comm.
apply IHxs.
Qed.

Theorem filter_p_np_perm' (p:A->bool) a xs : filter p xs ++ [a] ++ filter (negb ∘ p) xs == a :: xs.
rewrite Permutation_app_comm.
rewrite <- app_assoc.
simpl app.
rewrite perm_skip.
apply reflexivity.
rewrite Permutation_app_comm.
apply filter_p_np_perm.
Qed.

Definition dec2b {R:relation A} (Hdec:forall x y:A, {R x y}+{~R x y}) : forall x y:A, bool.
intros x y.
case (Hdec x y);intro;[exact true|exact false].
Defined.

Hypothesis Gt_not_Le : forall x y:A, Gt x y -> ~Le x y.

Theorem Le_dec x y : {Le x y}+{~ Le x y}.
case (Le_Gt_dec x y).
left; assumption.
intro H; right.
apply Gt_not_Le.
assumption.
Qed.

Definition gtb :A -> A -> bool := flip (dec2b Le_dec).

Theorem filter_fold (p:A->bool) a l : (if p a then a :: filter p l else filter p l) = filter p (a::l).
induction l.
simpl.
case (p a);auto.
simpl.
destruct (p a);reflexivity.
Qed.

Theorem filter_undo_true (p:A->bool) a l : p a = true -> a :: filter p l = filter p (a::l).
intro Hp.
simpl.
destruct (p a); reflexivity || discriminate.
Qed.

Theorem filter_undo_false (p:A->bool) a l : p a = false -> filter p l = filter p (a :: l).
intro.
simpl; destruct (p a); discriminate || reflexivity.
Qed.

Theorem sorted_le_intro (b a:A) l : Le b a -> sorted (a::l) -> sorted (b::l).
intros Hle Hsort.
inversion Hsort.
constructor.
constructor.
transitivity a.
assumption.
assumption.
assumption.
Qed.

Theorem everyP_tl P (a:A) l : everyP P (a::l) -> everyP P l.
intro H.
inversion_clear H; assumption.
Qed.

Theorem minimum_le_intro (b a:A) l : Le b a -> minimumP a l -> minimumP b l.
intros Hle Hmin.
induction Hmin.
constructor.
constructor.
transitivity a; assumption.
induction l.
constructor.
constructor.
transitivity a.
assumption.
inversion_clear Hmin.
assumption.
apply IHl.
eapply everyP_tl.
eassumption.
eapply everyP_tl;eassumption.
Qed.

Theorem filter_preserv_minimum (p:A->bool) a xs : minimumP a xs -> minimumP a (filter p xs).
intros Hmin.
induction xs.
constructor.
simpl filter.
case (p a0).
constructor.
apply (everyP_inv _ _ _ Hmin a0 (in_eq _ _)).
apply IHxs.
inversion_clear Hmin.
assumption.
apply IHxs.
inversion_clear Hmin.
assumption.
Qed.

Theorem minimum_sorted a l : sorted l -> minimumP a l -> sorted (a::l).
revert dependent a.
induction l.
constructor.
intros b Hsorted Hmin.
constructor.
inversion_clear Hmin.
assumption.
assumption.
Qed.

Theorem filter_sorted_skip_hd (p:A->bool) a l : sorted (filter p (a :: l)) -> sorted (filter p l).
generalize dependent a.
induction l.
constructor.
intros b Hsort.
simpl filter in Hsort|-*. 
destruct (p a);destruct (p b).
apply (sorted_inv _ _ Hsort).
assumption.
eapply sorted_inv.
eassumption.
assumption.
Qed.

Theorem filter_preserv_sorted (p:A->bool) (xs:list A) : sorted xs -> sorted (filter p xs).
intro H.
induction H.
constructor.
simpl.
case (p x).
constructor.
constructor.
simpl.
case (Bool.bool_dec (p x) true);intro Hx;[|apply Bool.not_true_is_false in Hx];
(case (Bool.bool_dec (p y) true);intro Hy;[|apply Bool.not_true_is_false in Hy]);
try rewrite Hx;try rewrite Hy.
  constructor.
  assumption.
  simpl in IHsorted.
  rewrite Hy in IHsorted.
  assumption.
  rewrite (filter_undo_false _ _ _ Hy).
  simpl filter.
  rewrite Hy.
  assert (y_min_l:=sorted_minimum _ _ H0).
  eapply sorted_le_intro;[apply H|].
  eapply minimum_sorted.
  eapply filter_sorted_skip_hd.
  eassumption.
  apply filter_preserv_minimum.
  assumption.
  simpl filter in IHsorted.
  rewrite Hy in IHsorted.
  assumption.
  eapply filter_sorted_skip_hd.
  eassumption.
Qed.
(* TODO: Proper (Permutation ==> flip impl) (everyP P) *)

Instance incl_proper : forall l:list A, ProperProxy (Permutation (A:=A)) l.
induction l.
constructor.
constructor.
assumption.
Qed.

Instance incl_perm_proper : Proper (equiv ==> Permutation (A:=A) ==> flip impl) (incl (A:=A)).
intros xs ys Hperm ws zs Hperm1 H.
intros x Hin.
symmetry in Hperm1.
eapply Permutation_in.
eassumption.
eapply H.
eapply Permutation_in.
eassumption.
assumption.
Qed.

Instance incl_Refl : Reflexive( incl (A:=A)).
intro x.
apply incl_refl.
Qed.

Theorem perm_incl_r (l l':list A) : l == l' -> incl l l'.
intro H.
rewrite H.
reflexivity.
Qed.

Instance everyP_proper (P:A->Prop) : Proper (Permutation (A:=A) ==> flip impl) (everyP P).
intros xs ys Hperm H.
inversion H.
subst.
induction xs.
constructor.
symmetry in Hperm.
contradict Hperm.
apply Permutation_nil_cons.
subst.
assert (xs_incl_al := perm_incl_r _ _ Hperm).
eapply incl_preserve_min;split;eassumption.
Qed.

Theorem everyP_app_preserv P (l l':list A) : everyP P l -> everyP P l' -> everyP P (l++l').
intros H0 H1.
inversion_clear H0; inversion_clear H1.
constructor.
constructor;assumption.
rewrite app_nil_r.
constructor;assumption.
simpl.
constructor.
assumption.
induction l0.
constructor;assumption.
simpl.
constructor.
inversion_clear H2.
assumption.
apply IHl0.
inversion_clear H2; auto.
Qed.

Theorem sort_app l l' (a:A) : sorted l -> sorted l' -> minimumP a l' -> everyP (flip Le a) l -> sorted (l++l').
intros Hsort0 Hsort1 Hmin Hevery.
induction Hmin.
rewrite app_nil_r.
assumption.
assert (Hsort3:=IHHmin (sorted_inv _ _ Hsort1)).
induction l.
simpl.
assumption.
simpl.
assert (a1_le_a0:Le a1 a0).
assert (a1_le_a:Le a1 a).
inversion Hevery.
assumption.
transitivity a; assumption.
assert (a1_minimum_l0:minimumP a1 l0).
eapply sorted_minimum.
apply minimum_sorted.
eapply sorted_inv.
eassumption.
eapply minimum_le_intro.
eassumption.
apply sorted_minimum.
assumption.
apply minimum_sorted.
apply IHl.
eapply sorted_inv;eassumption.
inversion_clear Hevery.
assumption.
intro Hll0.
simpl in Hsort3.
eapply (sorted_inv a1).
apply Hsort3.
simpl in Hsort3.
eapply sorted_inv.
eassumption.
simpl in Hsort3.
rewrite Permutation_app_comm.
simpl.
eapply every1.
assumption.
rewrite Permutation_app_comm.
apply (sorted_minimum _ _ Hsort3).
Qed.

Program Fixpoint quicksort (xs:list A) :
{ l:list A | sorted l /\ l == xs }
:= match xs with
      | nil => nil
      | a :: l => let (l',H) := quicksort l
                  in filter (gtb a) l' ++ a :: filter (negb ∘ gtb a) l'
   end.
Next Obligation.
split.
constructor.
reflexivity.
Qed.
Next Obligation.
split.
eapply (sort_app _ _ a).
apply filter_preserv_sorted;assumption.
induction l'.
constructor.
simpl filter.
case (Bool.bool_dec ((negb ∘ gtb a) a0) true);intro Hcond.
rewrite Hcond.
constructor.
unfold negb,gtb,flip,compose,dec2b in Hcond.
destruct (Le_dec a0 a).
discriminate.
apply Gt_Le.

Abort.
End QuickSort.


End Sorting.


Section nat_sort.
Require Import Arith.
Theorem gt_le : (forall x y : nat, x > y -> y <= x).
auto with arith.
Qed.

Theorem not_gt : (forall x y : nat, x <= y -> ~ x > y).
auto with arith.
Qed.

Theorem gt_weak_le : forall x y : nat, y > x -> x <= y.
auto with arith.
Qed.

Definition nat_sort := ins_sort' nat le gt le_lt_dec gt_weak_le.

End nat_sort.

Eval vm_compute  in (nat_sort [5;2;1]).