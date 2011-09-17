Require Export CatSem.CAT.category.
Require Export CatSem.CAT.functor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
(* for coq 8.3 rc1 *)

Unset Automatic Introduction.

Section FAlgebra.
Variable C:Cat.

Variable F : Functor C C.

Record F_Algebra_struct (A:C) := {
  falg_functor := F
; falg_alpha :> F A ---> A 
}.

Record F_Alg := 
{ Falg_obj :> C
; Falg_struct :> F_Algebra_struct Falg_obj
}.

Section FALG.

Record Falg_morphism (Fa Fb:F_Alg) :=
{ falg_morphism_morph :> Fa ---> Fb
; falg_morphism_prop :> falg_alpha Fa ;; falg_morphism_morph == #F falg_morphism_morph ;; falg_alpha Fb
}.

Program Definition Falg_morph_comp (Fa Fb Fc:F_Alg) (f: Falg_morphism Fa Fb) (g:Falg_morphism Fb Fc) : Falg_morphism Fa Fc :=
Build_Falg_morphism (falg_morphism_morph := f ;; g) _.
Next Obligation.
intros a b c f g.
rewrite <- assoc.
rewrite (falg_morphism_prop f).
rewrite assoc.
rewrite (falg_morphism_prop g).
rewrite preserve_comp.
rewrite assoc.
reflexivity.
apply F.
Qed.

Program Instance Falg_morph_oid : forall Fa Fb : F_Alg, Setoid (Falg_morphism Fa Fb) :=
{ equiv f g := falg_morphism_morph f == falg_morphism_morph g }.
Next Obligation.
split.
  intros f;reflexivity.

  intros f g H;symmetry; assumption.

  intros f g h H0 H1; etransitivity; eauto.
Qed.

Program Definition Falg_morph_id (Fa:F_Alg) : Falg_morphism Fa Fa :=
Build_Falg_morphism (falg_morphism_morph := (id (Falg_obj Fa))) _.
Solve Obligations using cat.

Program Instance Falg_cat_struct : Cat_struct Falg_morphism :=
{ comp := Falg_morph_comp ; mor_oid := Falg_morph_oid ; id := Falg_morph_id }.
Solve Obligations using cat.
Next Obligation.
intros a b c f g H0 h i H1.
simpl in *.
rewrite H0; rewrite H1.
reflexivity.
Qed.
Next Obligation.
simpl; intros.
rewrite assoc.
reflexivity.
Qed.

End FALG.

End FAlgebra. 

