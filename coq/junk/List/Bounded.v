Require Import List Notations Relations.



Section Bounded.

Variable A : Type.
Let List := list A.

Inductive SubList (l : List) : List -> Prop :=
  | subl_nil : SubList l []
  | subl_cons a l' : In a l -> SubList l' l -> SubList l (a :: l').

Notation "l' ⊆ l" := (SubList l l') (at level 50) : list_scope.

Variable Lt : relation A.
Let Lt_order := order _ Lt.

Bind Scope x_scope with A.
Notation "x < y" := (Lt x y) (at level 70)  : x_scope.
Open Scope x_scope.
Inductive Bounded (n : A) : List -> Prop :=
  | bound_single a : n < a -> Bounded n [a]
  | bound_cons a l : n < a -> Bounded n l -> Bounded n (a :: l).

Require Import All.

Theorem Bounded_All n l : Bounded n l -> All _ (fun x => n < x) l.
induction l.
inversion 1.
inversion 1.
constructor.
assumption.
constructor.
constructor.
assumption.
apply IHl.
assumption.
Qed.


Theorem Minimum_swap a b c l : Lt c a -> Lt c b -> Bounded c (a :: l) -> Bounded c (b :: l).
intros Hlt0 Hlt1 H.
inversion H.
constructor.
assumption.
constructor.
assumption.
assumption.
Qed.

Inductive Minimum a l :=
  min : In a l -> Bounded a l -> Minimum a l.

Theorem Minimum_cons (Hrefl : forall x, Lt x x) a b l : Lt b a -> Minimum b (b :: l) -> Minimum b (b :: a :: l).
intro Hlt.
inversion 1.
constructor.
auto with datatypes.
constructor.
apply Hrefl.
eapply Minimum_swap.
apply Hrefl.
assumption.
assumption.
Qed.

End Bounded.