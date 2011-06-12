Require Import exponent.
Require Import exponent_notations.
Require Import CatSem.CAT.functor.
Section Exponent_Functor.

Variable C:Cat.
Variable Prod:Cat_Prod C.
Variable Exp:Cat_Exp Prod.

Implicit Arguments product_mor [obC morC C a a' b b' H].

Section curry_eval_id.

Variable T Y:C.

Section T_Y_cat.


Class ObjTY_struct (x:C) := {  morTY : T ∏ x ---> Y }.
Record ObjTY :=
{ baseTY : C
; objTY_struct :> ObjTY_struct baseTY
}.


Class Xi_struct (from to:ObjTY):=
{ ξmor : baseTY from ---> baseTY to
; ξmor_prop :
   morTY (ObjTY_struct:=from) == (id T × ξmor);;morTY (ObjTY_struct:=to)
}.
Implicit Arguments ξmor [from to].
Record Xi :=
{ ξf : ObjTY
; ξf' : ObjTY
; xi_struct :> Xi_struct ξf' ξf
; ξ := ξmor xi_struct
}.

Definition ObjTY_equiv x y : Prop :=
  baseTY x = baseTY y.
Instance ObjTY_setoid : Setoid ObjTY :=
{ equiv := ObjTY_equiv }.
unfold ObjTY_equiv.
split.
  intros x; reflexivity.
  intros x y H.
  symmetry; apply H.
  intros x y z H0 H1.
  transitivity (baseTY y); assumption.
Qed.

Definition Xi_struct_equiv : forall (x y:ObjTY), relation (Xi_struct x y).
intros x y f g.
apply ((ξmor f == ξmor g)).
Defined.

Theorem Xi_struct_mor_oid : forall (x y:ObjTY), Setoid (Xi_struct x y).
intros x y.
apply (Build_Setoid (equiv:=Xi_struct_equiv x y)).
unfold Xi_struct_equiv.
split.
  intros f.
  reflexivity.
  intros f g H.
  symmetry; apply H.
  intros f g h H0 H1.
  rewrite H0.
  rewrite H1.
  reflexivity.
Defined.

Program Instance Xi_Cat_struct : Cat_struct Xi_struct :=
{ mor_oid := Xi_struct_mor_oid }.
Next Obligation.
intro a.
esplit.
instantiate (1:= id (baseTY a)).
assert (H:id T × id (baseTY a) == id (T ∏ (baseTY a))).
  apply (product_mor_id Prod T (baseTY a)).
rewrite H.
cat.
Defined.
Next Obligation.
intros a b c [f Hf] [g Hg].
esplit.
rewrite Hf.
rewrite Hg.
rewrite <- assoc.
rewrite <- product_mor_product_mor.
cat.
Defined.
Next Obligation.
intros a b c.
intros [f Hf] [g Hg] Hfg [h Hh] [i Hi] Hhi.
simpl in *.
unfold Xi_struct_equiv in *.
simpl in *.
rewrite Hfg.
rewrite Hhi.
cat.
Qed.  
Next Obligation.
intros a b [f Hf].
simpl.
unfold Xi_struct_equiv.
simpl.
cat.
Qed.
Next Obligation.
intros a b [f Hf].
simpl.
unfold Xi_struct_equiv.
simpl.
cat.
Qed.
Next Obligation.
intros a b c d [f Hf] [g Hg] [h Hh].
simpl.
unfold Xi_struct_equiv.
simpl.
rewrite assoc.
cat.
Qed.
End T_Y_cat.


Section Product_property.

Variable a b c d:C.
Variable g:a ---> b.
Variable h:c ---> d.

Definition g_X_h : a ∏ c ---> b ∏ d.
eapply prod_mor.
  eapply comp.
    2:apply g.
    apply prl.
  eapply comp.
    2:apply h.
    apply prr.
Defined.

Variable g: forall (x x':C), x'--->x.

Hypothesis g_prop : forall (f':objTY x') (f:objTY x),
                    f' == id T × g x x';;f.

Instance 

Class T_Y_structure :=
{ 

; morTY {x' x:C} : (T ∏ x' ---> Y) -> (T ∏ x ---> Y)

}.

Section T_Y_ex.
e TY:T_Y_structure
Variable x x':C.
Variable f:T ∏ x ---> Y.
Variable f':T ∏ x' ---> Y.
Let 

Instance Cat_struct :  

Definition Y_intro_r (x:C) : x ---> x ∏ Y.
apply prod_mor.
apply (id x).

End curry_eval_id.

Variable X Y:C.

Definition Fobj := fun Z:C => Z ^^ (Y ^^ X).

Definition Fmor (a b:C) (f:a ---> b) : Fobj a ---> Fobj b.
unfold Fobj.
apply curry.
eapply comp.
apply eval.
apply f.
Defined.



Instance Exp_Functor_struct : Functor_struct Fmor.
unfold Fmor.
split.
  intros a b f g H.
  rewrite H.
  reflexivity.
  intros a.
  unfold Fobj.
  rewrite id_r.
  pose (H:=product_mor (H:=Prod) (id (a ^^ (Y ^^ X))) (id Y))cac.
  erewrite