Require Export CatSem.CAT.category.
Require Export CatSem.CAT.functor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.

Section FAlgebra.
Variable C:Cat.
Variable F:Functor C C.

Record F_Algebra :=
{ F_Algebra_obj :> C
; F_Algebra_alg :> F F_Algebra_obj ---> F_Algebra_obj
}.

Record F_Algebra_mor (FA FB:F_Algebra) :=
  { F_Algebra_mor_mor :> FA ---> FB
  ; F_Algebra_mor_prop : comp (Cat_struct:=C)  FA (F_Algebra_mor_mor) == #F F_Algebra_mor_mor ;; FB}.

Infix "--->_F" := F_Algebra_mor (at level 60, right associativity).

Program Instance F_Algebra_mor_oid (FA FB:F_Algebra) : Setoid (FA --->_F FB) :=
  { equiv f g := (F_Algebra_mor_mor f) == g }.
Next Obligation.
intros a b.
split.
  intros f; reflexivity.

  intros f g H; symmetry; assumption.

  intros f g h H0 H1; etransitivity; eauto.
Qed.

Definition F_Algebra_mor_id (A:F_Algebra) : A --->_F A.
split with (id (F_Algebra_obj A)).
cat.
Defined.

Definition F_Algebra_mor_comp (a b c:F_Algebra) (f: a --->_F b) (g: b --->_F c) : a --->_F c.
split with (F_Algebra_mor_mor f ;; g).
pose (H:=comp_oid (Cat_struct:=C)).
rewrite <- assoc.
rewrite (F_Algebra_mor_prop f).
rewrite assoc.
rewrite (preserve_comp (Functor_struct:=F)).
rewrite (F_Algebra_mor_prop g).
rewrite assoc.
reflexivity.
Defined.

Program Instance F_Algebra_Cat_struct : Cat_struct F_Algebra_mor :=
{ mor_oid := F_Algebra_mor_oid 
; id := F_Algebra_mor_id
; comp := F_Algebra_mor_comp }.
Solve Obligations using cat.
Next Obligation.
intros a b c f g H0 h i H1.
simpl in *.
rewrite H0; rewrite H1.
reflexivity.
Qed.
Next Obligation.
intros a b c d f g h.
simpl in *.
rewrite assoc.
reflexivity.
Qed.

Definition FALG : Cat := Build_Cat F_Algebra_Cat_struct.

End FAlgebra.
