Require Export SET.
Require Import CatSem.CAT.functor.
Require Import List.

Section List_Functor.

Definition List (A:Set) : Set := list A.

Program Instance List_functor_struct :
Functor_struct (C:=type_cat) (D:=type_cat) (Fobj:=List) map.
Next Obligation.
intros a b f g H xs.
induction xs.
reflexivity.
simpl.
f_equal.
rewrite H.
reflexivity.
assumption.
Qed.
Next Obligation.
intro a.
intro xs.
induction xs.
reflexivity.
simpl.
rewrite IHxs.
reflexivity.
Qed.
Next Obligation.
intros a b c f g xs.
induction xs.
reflexivity.
simpl.
rewrite IHxs.
reflexivity.
Qed.
Definition list_functor : Functor type_cat type_cat := Build_Functor List_functor_struct.

End List_Functor.
