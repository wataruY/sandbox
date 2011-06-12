Require Export CatSem.CAT.product.
Require Import product_notations.
Require Import product_lemmata.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.


Section Exponentiation.

Variable C:Cat.
Variable H:Cat_Prod C.

Section Def.

Class Cat_Exp :=
{ exp : C -> C -> C
; eval {a b} : (exp a b) ∏ a ---> b
; curry {a b c} (g:c ∏ a ---> b) : c ---> (exp a b)
; curry_oid :> forall a b c:C, Proper (equiv ==> equiv) (curry (a:=a) (b:=b) (c:=c))
; eval_curry {a b c} (g:c ∏ a ---> b) : curry g × id a ;; eval  == g
}.

End Def.

End Exponentiation.