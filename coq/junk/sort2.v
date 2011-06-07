Require Import List.
Require Import Setoid.
Require Import Permutation.
Require Import SetoidClass.
Require Import Relations.
Require Import Program.


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

Hypothesis Tricho : forall x y:A, {Le x y}+{Gt x y}.
Hypothesis Gt_Le : forall x y, Gt y x -> Le x y.

Hypothesis Le_not_Gt : forall x y, Le x y -> ~ Gt x y.
Hypothesis Le_trans : Transitive Le.

Fixpoint insert x l :=
  match l with 
     | nil => x :: nil
     | a :: l' => if Tricho x a then x :: l else a :: insert x l'
  end.

Program Instance perm_setoid : Setoid (list A) :=
{ equiv := Permutation (A:=A) }.

Theorem insert_equiv x l : insert x l == x :: l.
induction l.
reflexivity.
simpl.
case (Tricho x a).
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
case (Tricho x y).
  intros Hle.
  constructor;[assumption|constructor].
  intro H0.
  apply Gt_Le in H0.
  constructor.
  assumption.
  constructor.
  intros y z l' Hyz Hzl Hins.
  simpl.
  case (Tricho x y).
  intro Hxy.
  constructor.
  assumption.
  constructor.
  assumption.
  assumption.
  intro H0.
  revert Hins.
  simpl.
  case (Tricho x z); intros H1 Hsort.
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