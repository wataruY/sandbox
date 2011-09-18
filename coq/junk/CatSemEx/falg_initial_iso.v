Require Import falg.
Require Import CatSem.CAT.monic_epi.
Require Import CatSem.CAT.initial_terminal.

Set Implicit Arguments.
Unset Strict Implicit.


Section Cat.
Variable C:Cat.
Variable F:Functor C C.
Let FAlg := FALG F.

Section InitialFalgebra.

Definition InitialAlgebra := Initial FAlg.

End InitialFalgebra.

Section LambekTheorem.

Variable InitAlg : InitialAlgebra.

Let A := F_Algebra_obj (Init (Initial:=InitAlg)).
Let α := F_Algebra_alg (Init (Initial:=InitAlg)).
Hint Unfold A.
Hint Unfold α.

Let FA : F_Algebra F.
apply (Build_F_Algebra (F_Algebra_obj:= F A)).
unfold A.
apply Fmor.
apply α.
Defined.
Hint Unfold FA.

Let α_inv : A ---> F A.
pose (FA' := F_Algebra_mor_mor (InitMor (Initial:=InitAlg) FA)).
info auto.
Defined.
Hint Unfold α_inv.

Theorem InitMorC : α ;; α_inv == #F α_inv ;; #F α.
unfold α, α_inv.
etransitivity.
  apply (F_Algebra_mor_prop (InitMor (Initial:=InitAlg) FA)).
symmetry.
simpl.
unfold A.
apply comp_oid; reflexivity.
Qed.
Hint Resolve InitMorC : falg.

Definition FX_X_map : F_Algebra_mor FA (Init (Initial:=InitAlg)).
apply Build_F_Algebra_mor with (F_Algebra_mor_mor := α).
simpl.
reflexivity.
Defined.
Hint Resolve FX_X_map : falg.

Program Definition X_FX_map : F_Algebra_mor (Init (Initial:=InitAlg)) FA :=
  Build_F_Algebra_mor (F_Algebra_mor_mor := α_inv) _.
Next Obligation.
unfold α_inv.
apply (F_Algebra_mor_prop (InitMor (Initial:=InitAlg) FA) ).
Qed.
Hint Resolve X_FX_map : falg.

Theorem X_FX_X_id : comp (Cat_struct:=FAlg) X_FX_map FX_X_map == id (Init (Initial:=InitAlg)).
rewrite InitMorUnique.
symmetry.
rewrite InitMorUnique.
reflexivity.
Qed.
Hint Resolve X_FX_map : falg.

Theorem FX_comp_Finv_id_FX : #F α_inv ;; #F α == id (F A).
etransitivity.
  symmetry; apply preserve_comp.
    apply F.
symmetry; etransitivity.
  symmetry;apply preserve_ident.
    apply F.
pose (H:=X_FX_X_id).
simpl in H.
symmetry;etransitivity.
   rewrite functor_map_morphism.
   3: apply H.
   reflexivity.
   apply F.
reflexivity.
Qed.
Hint Resolve FX_comp_Finv_id_FX : falg.

Theorem inv_alpha_alpha_id : α ;; α_inv == id (F A).
rewrite InitMorC.
apply FX_comp_Finv_id_FX.
Qed.
Hint Resolve inv_alpha_alpha_id : falg.

Program Instance F_alg_alpha_invertible : Invertible α := { inverse := α_inv }.
Next Obligation.
pose (H:=X_FX_X_id).
apply H.
Qed.
Next Obligation.
apply inv_alpha_alpha_id.
Qed.

Instance F_init_alg_alpha_iso : isomorphic C (F A) A :=
{ inv_morphism := α
; invertible := F_alg_alpha_invertible
}.

End LambekTheorem.

End Cat.