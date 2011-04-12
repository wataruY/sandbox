Require Import List.

Definition All {A : Type} (p : A -> Prop) (l : list A) := forall x, In x l -> p x.

Theorem All_nil {A : Type} : forall p, All (A := A) p nil.
unfold All.
intros p x H.
contradiction.
Qed.

Theorem All_split {A : Type} (p : A -> Prop) (x : A) (l : list A) :
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



Theorem All_swap {A : Type} (p : A -> Prop) (x y : A) (l : list A) :
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

Theorem All_cons {A : Type} (p : A -> Prop) (x : A) (l : list A) :
  p x -> All p l -> All p (x :: l).
intros Hhd Htl z Hin.
case_in Hin.
intro; subst; assumption.
intro Hin.
apply Htl.
assumption.
Qed.

Theorem All_l {A : Type} (p : A -> Prop) (l : list A) :
  l = nil \/ (exists y, exists ys, p y /\ All p ys /\ l = (y :: ys)) -> All p l.
intro H; case H; clear H.
intro; subst; apply All_nil.
intro H; destruct H as [y H].
destruct H as [ys H].
destruct H as [Hy [Hys Heq]].
subst.
apply All_cons; assumption.
Qed.

Definition filter_strong {A : Type} (p : A -> Prop) (f : forall x, {p x}+{~ p x} ) (l : list A) :
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
case (in_inv Hin).
intro; subst; trivial.
left; reflexivity.
intro; right; apply IH; assumption.
intro H'.
esplit.
split.
apply Hl.
intros z Hin.
simpl.
right.
apply IH; assumption.
Defined.

Extraction filter_strong.