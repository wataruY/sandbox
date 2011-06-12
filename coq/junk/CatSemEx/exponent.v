Require Export CatSem.CAT.product.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.


Section Exponentiation.

Variable C:Cat.
Variable H:Cat_Prod C.
Notation "a ∏ b" := (product a b) (at level 40).
Notation "a × b" := (product_mor H a b) (at level 40).

Class Cat_Exp :=
{ exp : C -> C -> C
; eval {a b} : (exp a b) ∏ a ---> b
; curry {a b c} (g: c ∏ a ---> b) : c ---> (exp a b)
; curry_oid:> forall a b c:C,
       Proper (equiv ==> equiv) (@curry a b c)
; eval_curry {a b c} {g:c ∏ a ---> b} : (curry g × id a) ;; eval == g
}.

End Exponentiation.
