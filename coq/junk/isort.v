Require Import List.
Require Import Relations.

Section Insertion_Sort.

Variable (A : Type) (Le Gt : relation A).
Hypothesis (R_total : forall x y, {Le x y} + {Gt x y}) (R_inv : forall x y, Le x y <-> Gt y x).

Hypothesis (Le_refl : reflexive _ Le) (Le_trans : transitive _ Le).

Let List := list A.

Inductive Sorted : List -> Prop :=
  | sorted0 : Sorted nil
  | sorted1 a : Sorted (a :: nil)
  | sorted2 a b l : Le a b -> Sorted (b :: l) -> Sorted (a :: b :: l).

Theorem sorted_trans a b l : Le a b -> Sorted (b :: l) -> Sorted (a :: l).
intros Hle Hsorted.
inversion Hsorted.
constructor.
constructor.
eapply Le_trans;eauto.
assumption.
Qed.

Notation "[]" := nil : list_scope.
Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..) : list_scope.
Inductive Transposed : relation List :=
  | trans_hd x y l : Transposed (x :: y :: l) (y :: x :: l)
  | trans_tl x l l' : Transposed l l' -> Transposed (x :: l) (x :: l').

Inductive Permuted (l : List) : List -> Prop :=
  | perm_id : Permuted l l
  | perm_tr : forall l' l'', Permuted l l' -> Transposed l' l'' -> Permuted l l''.

Theorem perm_intro_r l l' l'' : Transposed l l' -> Permuted l' l'' -> Permuted l l''.
intros Htr Hperm; elim Hperm.
eapply perm_tr; eauto.
constructor.
intros l0 l1; intros.
econstructor.
eauto.
auto.
Qed.

Theorem perm_trans : transitive _ Permuted.
intros l l' l'' H0.
generalize l''.
elim H0.
trivial.
do 2 intro.
intros Hp Htrans1 Ht.
intro.
intro Htrans2.
apply Htrans1.
eapply perm_intro_r.
eauto.
assumption.
Qed.

Theorem transpose_sym : symmetric _ Transposed.
intros l l' H.
elim H.
constructor.
constructor.
assumption.
Qed.

Theorem perm_sym : symmetric _ Permuted.
intros l l'' H.
elim H.
constructor.
intros.
eapply perm_intro_r.
apply transpose_sym.
eauto.
assumption.
Qed.

Theorem sorted_inv a l : Sorted (a :: l) -> Sorted l.
inversion_clear 1.
constructor.
assumption.
Qed.

Theorem perm_cons a l l' : Permuted l l' -> Permuted (a :: l) (a :: l').
intro H; elim H.
constructor.
intros xs ys Hperm.
inversion_clear Hperm.
intros.
econstructor.
eauto.
constructor.
assumption.
intros Hperm Htr.
econstructor.
eauto.
econstructor.
assumption.
Qed.

Theorem perm_perm a b l l' : Permuted l l' -> Permuted (a :: b :: l) (b :: a :: l').
intro H.
elim H.
repeat econstructor.
intros xs ys Hp0 Hp1.
generalize Hp0; clear Hp0.
generalize ys.; clear ys.
elim Hp1.
intros.
econstructor.
eauto.
repeat constructor.
assumption.
intros vs ws Hperm H0;
intros.
apply H0.
assumption.
assumption.
Qed.

Theorem perm_swap (a b: A) l l' : Permuted (a :: b :: l) l' -> Permuted (b :: a :: l) l'.
intro H.
elim H.
apply perm_perm.
constructor.
intros.
eapply perm_tr.
eauto.
auto.
Qed.

Section ForallElement.

Inductive All (P : A -> Prop) : List -> Prop :=
  | All_nil : All P []
  | All_cons a l : P a -> All P l -> All P (a :: l).

End ForallElement.

Require Import List.Bounded.

Theorem perm_nil_single a : ~ Permuted [] [a].
intro H.
inversion_clear H as [ | l l' _ H1] .
inversion_clear H1 as [|  l' l'' H2 H3].
inversion H3.
Qed.

Theorem perm_min c l l' : Minimum c l -> Permuted l l' -> Minimum c l'.
generalize l c; clear l c.
induction l'.
intros.
apply All_nil.
apply 

Fixpoint aux (c : A)  (l : List) : {l'| Permuted l' (c :: l) /\ (Sorted l -> Sorted l')}.
induction l.
esplit.
split.
econstructor.
constructor.
destruct IHl as [l' [Hperm Hsort]].
case (R_total c a); intro H.
esplit.
split.
econstructor.
intro.
constructor.
assumption.
assumption.
destruct (aux c l) as [l0 [Hperm0 Hsort0]].
esplit.
apply R_inv in H.
split.
assert (Hperm1 : Permuted (a :: l0) (c :: a :: l)).
apply perm_sym.
apply perm_swap.
apply perm_cons.
apply perm_sym.
assumption.
eauto.
intro sorted_a_l.
assert (H_l_sorted := sorted_inv _ _ sorted_a_l).
assert (H_l0_sorted := Hsort0 H_l_sorted).
eapply prepend_minimum_sorted.
assumption.
