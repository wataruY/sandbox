Require Import exploration.
Require Import product_notations.
Require Import product_lemmata.
Require Import CatSem.CAT.coproduct.
Section Theorems.

Notation "b ^^ a" := (exp a b) (at level 20, right associativity).

Variable C:Cat.
Variable Hprod:Cat_Prod C.
Variable Hexp:Cat_Exp Hprod.
Section Hoge.


(* eval_curry (c:=a) (a:=b) (b:=a∏b) (id (a ∏ b)) *)
 
Local Implicit Arguments prl [obC morC C Cat_Prod a b].
Local Implicit Arguments prr [obC morC C Cat_Prod a b].

Definition uncurry {a b c:C} (f:a ---> c ^^ b) : a ∏ b ---> c.
eapply comp.
2: apply eval.
eapply product_mor.
apply f.
apply id.
Defined.

Theorem curry_uncurry_id {a b c:C} (f:a ∏ b ---> c) :
 uncurry (curry f) == f.
unfold uncurry.
rewrite eval_curry.
cat.
Qed.

eapply eval.

(* Build_Cat_Prod (C:=C) (product:=(product (C:=C))) (prl:=fun a b:C, prl (a:=a) (b:=b) (Cat_Prod:=Hprod))  *)
(* (prr : forall a b : C, a ∏ b ---> b) *)
Section Exp_ISO.


Variables a b:C.



Section Exp_based_prod.

Definition exp_product := fun Z Y:C => Z ^^ Y ∏ Y.

Definition exp_prr : forall a b:C, exp_product a b ---> b.
intros Z Y.
unfold exp_product.
apply prr.
Defined.

Definition exp_prl : forall a b:C, exp_product a b ---> a.
intros Z Y.
apply eval.
Defined.

Definition exp_prod_mor : forall a c d:C, a ---> c -> a ---> d -> a ---> (exp_product c d).
intros X Y Z f g.
unfold exp_product.
apply prod_mor.
eapply comp.
  2:apply curry.
  apply f.
  apply prl.
assumption.
Defined.

Variable Hsum:Cat_Coprod C.

Program Instance Exp_Prod : Cat_Prod C :=
{ product := exp_product
; prl := exp_prl
; prr := exp_prr
; prod_mor := exp_prod_mor
}.
Obligation Tactic := unfold exp_product, exp_prl, exp_prr, exp_prod_mor.
Next Obligation.
intros a c d f g Hfg h i Hhi. 
rewrite Hfg.
rewrite Hhi.
cat.
Qed.
Next Obligation.
intros a c d f g.
split.
Abort.

Variable a b :C.
Theorem hoge : curry (eval (a:=a) (b:=b)) × id a== id (b ^^ a ∏ a).
etransitivity.
Focus 2.
apply product_mor_id.


reapply
assert (H:= eval_curry ((eval (a:=a) (b:=b)))).
assert (H':eval (a:=a) (b:=b) == id (b ^^ a ∏ a);;eval (a:=a) (b:=b)).
  cat.

rewrite H' in H at 3.
symmetry.
etransitivity.
  symmetry.
  rewrite <- product_mor_id.