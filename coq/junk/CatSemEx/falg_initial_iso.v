Require Import falg.
Require Import CatSem.CAT.monic_epi.
Require Import CatSem.CAT.initial_terminal.
Require Import aux.

Set Implicit Arguments.
Unset Strict Implicit.

Section Cat.
Variable C:Cat.
Variable F:Functor C C.
Let FALG := falg.FALG F.

Context (InitialAlgebra : Initial FALG).

Section LambekTheorem.

Notation "0" :=(Init (Initial:=InitialAlgebra)).
Notation "!" := (InitMor (Initial:=InitialAlgebra)).
Infix "--->_F" := (mor (c:=FALG)) (at level 81).

Let A := FAlg_obj 0.
Let α := FAlg_alpha 0.

Hint Unfold A.
Hint Unfold α.

Let FA : FALG.
exists (F A).
apply Fmor.
apply α.
Defined.
Hint Unfold FA.

Let α_inv : A ---> F A := ! FA.
Hint Unfold α_inv.

Theorem InitMorC : α ;; α_inv == #F α_inv ;; #F α.
unfold α, α_inv.
etransitivity.
  apply (FAlg_map_prop (! FA)).
simpl.
apply comp_oid; reflexivity.
Qed.
Hint Resolve InitMorC : falg.

Let FA_to_A : FA --->_F 0.
exists α.
cat.
Defined.
Hint Resolve FA_to_A : falg.

Program Let A_to_FA : 0 --->_F FA :=
  Build_FAlg_map (FAlg_map_mor:=! FA) _.
Next Obligation.
apply (FAlg_map_prop (! FA)).
Qed.
Hint Resolve A_to_FA : falg.

Theorem A_FA_A_id : A_to_FA ;; FA_to_A == id 0.
transitivity (! 0);[apply InitMorUnique | apply init_reflection].
Qed.
Hint Resolve A_FA_A_id : falg.

Theorem F_inv_F_alpha_id : #F α_inv ;; #F α == id (F A).
simpl.
transitivity (#F (α_inv ;; α)).
  rewrite (preserve_comp (Functor_struct:=F)); reflexivity.
rewrite <- (preserve_ident (Functor_struct:=F)).
apply (functor_map_morphism (Functor_struct:=F)).
transitivity (id A).
  exact A_FA_A_id.
  reflexivity.
Qed.
Hint Resolve F_inv_F_alpha_id : falg.

Theorem inv_alpha_alpha_id : α ;; α_inv == id (F A).
rewrite InitMorC.
auto with falg.
Qed.
Hint Resolve inv_alpha_alpha_id : falg.

Program Instance F_alg_alpha_invertible : Invertible α := { inverse := α_inv }.
Solve Obligations using auto with falg.

Instance F_init_alg_alpha_iso : isomorphic C (F A) A :=
{ inv_morphism := α
; invertible := F_alg_alpha_invertible
}.

End LambekTheorem.

End Cat.
