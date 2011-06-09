Require Import list_functor.
Require Import option_functor.
Require Import List.
Require Import CatSem.CAT.NT.

Section head_nt.
Definition head_option (A:Set) (xs:list A) :=
  match xs with
     | nil => None
     | a :: _ => Some a
  end.

Program Definition head_NT : NT  list_functor option_functor := Build_NT (trafo:=head_option) _.
Next Obligation.
split.
intros c d f xs.
induction xs;reflexivity.
Qed.

Program Definition tl_NT : NT list_functor list_functor := Build_NT (trafo:=tl) _.
Next Obligation.
split.
intros c d f xs.
induction xs;reflexivity.
Qed.