Require Export CatSem.CAT.product.
Require Import product_notations.
Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

Section Exponentiation.

Variable C:Cat.
Variable Prod:Cat_Prod C.

Implicit Arguments product_mor [obC morC C a a' b b' H].


(* definition of C (T ---> Y) *)
Section T_Y_cat.
Variable T Y:C.

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
{ xi_to : ObjTY
; xi_from : ObjTY
; xi_struct :> Xi_struct xi_from xi_to
; ξ := ξmor xi_struct
}.

Definition ObjTY_equiv x y : Prop :=
  baseTY x = baseTY y.
Hint Unfold ObjTY_equiv.

Instance ObjTY_setoid : Setoid ObjTY :=
{ equiv := ObjTY_equiv }.
split.
  intros x; reflexivity.
  intros x y H.
  symmetry; apply H.
  intros x y z H0 H1.
  transitivity (baseTY y); assumption.
Qed.

Definition Xi_struct_equiv (x y:ObjTY) : relation (Xi_struct x y).
intros x y f g.
apply ((ξmor f == ξmor g)).
Defined.

Theorem Xi_struct_mor_oid : forall (x y:ObjTY), Setoid (Xi_struct x y).
intros x y.
apply (Build_Setoid (equiv:=Xi_struct_equiv (x:=x) (y:=y))).
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
{ id a := _ 
; comp a b c f g := _
; mor_oid := Xi_struct_mor_oid }.
Next Obligation.
esplit.
instantiate (1:= id (baseTY a)).
assert (H:id T × id (baseTY a) == id (T ∏ (baseTY a))).
  apply product_mor_id.
rewrite H.
cat.
Defined.
Next Obligation.
destruct f as [f Hf].
destruct g as [g Hg].
esplit.
rewrite Hf.
rewrite Hg.
rewrite <- assoc.
rewrite <- product_mor_product_mor.
cat.
Defined.
Next Obligation.
intros [f Hf] [g Hg] Hfg [h Hh] [i Hi] Hhi.
simpl in *.
unfold Xi_struct_equiv in *.
simpl in *.
rewrite Hfg.
rewrite Hhi.
cat.
Qed.  
Next Obligation.
destruct f as [f Hf].
simpl.
unfold Xi_struct_equiv.
simpl.
cat.
Qed.
Next Obligation.
destruct f as [f Hf].
simpl.
unfold Xi_struct_equiv.
simpl.
cat.
Qed.
Next Obligation.
destruct f as [f Hf];destruct g as [g Hg];destruct h as [h Hh].
simpl.
unfold Xi_struct_equiv.
simpl.
rewrite assoc.
cat.
Qed.

End T_Y_cat.