Require Export CatSem.CAT.category.
Require Export CatSem.CAT.functor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.

Section FAlgebra.
Variable C:Cat.
Variable F:Functor C C.

Record FAlg :=
{ FAlg_obj :> C
; FAlg_alpha : F FAlg_obj ---> FAlg_obj
}.

Record FAlg_map (FA FB:FAlg) :=
  { FAlg_map_mor :> FA ---> FB
  ; FAlg_map_prop : FAlg_alpha FA ;; FAlg_map_mor == #F FAlg_map_mor ;; FAlg_alpha FB}.

Infix "--->_F" := FAlg_map (at level 60, right associativity).

Program Instance F_Algebra_mor_oid (FA FB:FAlg) : Setoid (FA --->_F FB) :=
  { equiv f g := FAlg_map_mor f == g }.
Next Obligation.
intros a b.
split.
  intros f; reflexivity.

  intros f g H; symmetry; assumption.

  intros f g h H0 H1; etransitivity; eauto.
Qed.

Definition F_Algebra_mor_id (A:FAlg) : A --->_F A.
exists (id (FAlg_obj A)).
cat.
Defined.

Definition F_Algebra_mor_comp (a b c:FAlg) (f: a --->_F b) (g: b --->_F c) : a --->_F c.
exists (FAlg_map_mor f ;; g).
rewrite <- assoc.
rewrite (FAlg_map_prop f).
rewrite assoc.
rewrite (preserve_comp (Functor_struct:=F)).
rewrite (FAlg_map_prop g).
rewrite assoc.
reflexivity.
Defined.

Program Instance F_Algebra_Cat_struct : Cat_struct FAlg_map :=
{ mor_oid := F_Algebra_mor_oid 
; id := F_Algebra_mor_id
; comp := F_Algebra_mor_comp }.
Solve Obligations using cat.
Next Obligation.
intros a b c f g H0 h i H1.
simpl in *.
apply comp_oid; assumption.
Qed.
Next Obligation.
intros a b c d f g h.
simpl in *.
rewrite assoc.
reflexivity.
Qed.

Definition FALG : Cat := Build_Cat F_Algebra_Cat_struct.

End FAlgebra.
