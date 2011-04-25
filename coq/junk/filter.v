Require Import List.

Section filter_strong.
Variable A : Type.

Definition Predicate  := A -> Prop.
Definition Decidable  (P : Predicate) := forall x:A, {P x}+{~ P x}.

Definition All  (p : A -> Prop) (l : list A) := forall x, In x l -> p x.

Theorem All_nil  : forall p, All p nil.
unfold All.
intros p x H.
contradiction.
Qed.

Theorem All_split  (p : A -> Prop) (x : A) (l : list A) :
 All p (x :: l) ->  p x /\ All p l .
unfold All.
intro Hcons.
split.
apply Hcons.
simpl.
left; trivial.
intros y H'.
apply Hcons.
simpl; right; assumption.
Qed.

Ltac case_in H := case (in_inv H); clear H.



Theorem All_swap  (p : A -> Prop) (x y : A) (l : list A) :
  p x -> p y -> All p (x :: y :: l) -> All p (y :: x :: l).
intros Hx Hy Hcons.
intro z.
intro Hin; case_in Hin.
intro; subst; assumption.
intro Hin; case_in Hin.
intro; subst; assumption.
intro Hin.
apply Hcons.
simpl.
right; right; assumption.
Qed.

Theorem All_cons  (p : A -> Prop) (x : A) (l : list A) :
  p x -> All p l -> All p (x :: l).
intros Hhd Htl z Hin.
case_in Hin.
intro; subst; assumption.
intro Hin.
apply Htl.
assumption.
Qed.

Theorem All_l  (p : A -> Prop) (l : list A) :
  l = nil \/ (exists y, exists ys, p y /\ All p ys /\ l = (y :: ys)) -> All p l.
intro H; case H; clear H.
intro; subst; apply All_nil.
intro H; destruct H as [y H].
destruct H as [ys H].
destruct H as [Hy [Hys Heq]].
subst.
apply All_cons; assumption.
Qed.


Definition filter_strong  {p : Predicate} (f : Decidable p ) (l : list A) :
           {l'| All p l' /\ forall x, In x l' -> In x l}.
induction l as [| x xs].
esplit.
split.
apply All_nil.
trivial.
destruct IHxs as [ ys [ Hl IH]].
case (f x).
intro Hp.
esplit.
split.
apply All_cons.
eauto.
apply Hl.
intros z Hin.
simpl.
case (in_inv Hin); auto.
intro H'.
esplit.
split.
apply Hl.
intros z Hin.
simpl.
right.
apply IH; assumption.
Defined.

Definition dec2bool  {P : Predicate} (p : Decidable P) : A -> bool := fun x => if p x then true else false.

Lemma filter_keep  (p : A -> bool) a l : p a = true -> filter p (a :: l) = a :: filter p l.
intro H.
induction l.
simpl.
rewrite H.
reflexivity.
simpl.
rewrite H.
reflexivity.
Qed.

Lemma filter_skip (p : A -> bool) a l : p a = false -> filter p (a :: l) = filter p l.
intro H.
induction l.
simpl.
rewrite H.
reflexivity.
simpl.
rewrite H.
reflexivity.
Qed.

Section filter_props.

Variables (P : Predicate) (p : Decidable P).

Theorem filter_all l : All P (filter (dec2bool p) l).
induction l.
simpl.
apply All_nil.
case (p a).
intro H.
assert (Hb : dec2bool p a = true).
unfold dec2bool.
case (p a); auto.
simpl.
rewrite Hb.
apply All_cons; assumption.
intro H.
simpl.
assert (Hb : dec2bool p a = false).
unfold dec2bool.
case (p a); trivial || contradiction.
rewrite Hb.
assumption.
Qed.

Theorem filter_subset l : forall x, In x (filter (dec2bool p) l) -> In x l.
induction l.
contradiction.
intros z Hin.
case (p a).
intro H.
assert (Hb : dec2bool p a = true).
unfold dec2bool.
case (p a); trivial || contradiction.
rewrite (filter_keep _ _ l Hb) in *|-.
case_in Hin.
intro;subst.
simpl;auto.
intro Hin.
simpl.
right; apply IHl.
assumption.
intro H.
assert (Hb : dec2bool p a = false).
unfold dec2bool.
case (p a); trivial || contradiction.
rewrite (filter_skip _ _ l Hb) in *|-.
simpl; auto.
Qed.

Extraction filter_strong.