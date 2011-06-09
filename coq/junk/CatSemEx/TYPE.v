Require Import CatSem.CAT.category.

Section SET.
Definition arrow := fun x y => x -> y.
Hint Unfold arrow.
Program Instance arrow_setoid (a b:Type) `(s:Setoid b) : Setoid (arrow a b) :=
{ equiv := fun f g:arrow a b => forall x:a, f x == g x }.
Next Obligation.
split.
intros f g.
reflexivity.
intros f g H x.
symmetry.
intuition.
intros f g h H0 H1 x.
transitivity (g x); intuition.
Qed.

Theorem arrow_ext_equiv (A B:Type) (f g:A->B) `(s:Setoid B) : (forall x:A, f x = g x) -> f == g.
intro H.
intro x.
rewrite H.
reflexivity.
Qed.

Program Definition eq_setoid A : Setoid A :=
  @Build_Setoid A (@Logic.eq A) _.

Program Instance type_cat : Cat_struct (obj:=Set) arrow :=
{
  mor_oid a b := arrow_setoid a b (eq_setoid b);
  id a := fun x=>x;
  comp a b c f g x := (g (f x))
}.
Next Obligation.
intros f g H.
intros h i H0 x.
rewrite H.
rewrite H0.
reflexivity.
Qed.


Definition SET : Cat := Build_Cat (obj:=Set) type_cat.
End SET.
