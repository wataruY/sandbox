Require Import product_lemmata.
Require Import product_notations.
Require Import CatSem.CAT.functor.

Section ProdFunctor.

Variable C:Cat.
Variable Hprod:Cat_Prod C.


(* _ * A *)
Section ProdFunctorR.
Variable A:C.
Let Fobj : C -> C.
intro a.
apply (a ∏ A).
Defined.

Let Fmor : forall a b:C, a ---> b -> Fobj a ---> Fobj b.
unfold Fobj.
intros a b f.
apply product_mor.
assumption.
eapply id.
Defined.

Program Instance RProd_Functor_struct : Functor_struct Fmor.
Obligation Tactic := unfold Fmor,Fobj.
Next Obligation.
intros a b  f g H.
rewrite H.
cat.
Qed.
Next Obligation.
intros a.
apply  product_mor_id.
Qed.
Next Obligation.
intros a b c f g.
rewrite <- product_mor_product_mor.
cat.
Qed.

End ProdFunctorR.

Section ProdFunctorL.

Variable A:C.

Let Fobj : C -> C.
intro a.
apply (A∏a).
Defined.

Let Fmor : forall a b:C, a ---> b -> Fobj a ---> Fobj b.
unfold Fobj.
intros a b f.
apply product_mor.
eapply id.
apply f.
Defined.

Program Instance LProd_Functor_struct : Functor_struct Fmor.
Obligation Tactic := unfold Fobj,Fmor.
Next Obligation.
intros a b f g H.
rewrite H.
cat.
Qed.
Next Obligation.
intros a.
rewrite product_mor_id.
cat.
Qed.
Next Obligation.
intros a b c f g.
rewrite <- product_mor_product_mor.
cat.
Qed.

End ProdFunctorL.

Record RProdFunctor (A:C) :=
{ raobj := A
; rpf_struct := RProd_Functor_struct raobj 
}.

Record LProodFunctor (A:C) :=
{ laobj := A
; lpf_struct := LProd_Functor_struct laobj
}.

End ProdFunctor.