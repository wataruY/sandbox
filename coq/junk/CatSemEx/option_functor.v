Require Import CatSem.CAT.functor.
Require Import TYPE.
Section Option_Functor.


Definition opt (A:Set) : Set := option A.

Program Instance option_functor_struct : Functor_struct (C:=type_cat) (D:=type_cat) (Fobj:=opt) option_map.
Next Obligation.
intros a b f g H x.
induction x.
simpl.
f_equal;apply H.
reflexivity.
Qed.
Next Obligation.
intros a x.
induction x; simpl;auto.
Qed.
Next Obligation.
intros a b c f g x; induction x;reflexivity.
Qed.
Definition option_functor : Functor type_cat type_cat := Build_Functor option_functor_struct.
End Option_Functor.