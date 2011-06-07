Require Import Program.
Require Import Setoid.
Section Feq.

Definition feq {A B:Type} (f g:A->B) := forall x:A, f x = g x.
Infix "=_f" := feq (at level 20).

Theorem feq_eq {A B:Type} (f g:A->B) : (forall a:A, f a = g a) <-> f =_f g.
unfold feq.
reflexivity.
Qed.

Theorem feq_trans : forall A B:Type, Transitive (@feq A B).
intros A B f g h .
unfold feq.
intros H0 H1 x.
rewrite H0.
apply H1.
Qed.

Add Parametric Relation A B : (A->B) (@feq A B)
  transitivity proved by (feq_trans A B) as feq_rel.

Section Functor.

Class Functor (F:Type->Type) := 
{ fmap {A B:Type} (f:A->B) : F A -> F B
; functor_id {A:Type} : fmap (id:A->A) =_f id
; functor_comp {A B C:Type} (f:B->C) (g:A->B) (x:F A) :
  (fmap f ∘ fmap g) =_f fmap (f ∘ g)
}.
Program Instance list_functor {A:Type} : Functor list :=
Build_Functor _ List.map _ _.
Local Obligation Tactic := intros; try (intro xs; induction xs); unfold compose; simpl; auto.

Next Obligation.
rewrite IHxs; auto.
Qed.
Next Obligation.
f_equal.
assumption.
Qed.

End Functor.

Section Monad.

Class Monad (M:Type->Type) `{HFunctor: Functor M} :=
{ unit {A} : A -> M A
; join {A} : M (M A) -> M A
; join_fmap {A} : (join ∘ (fmap join:M (M (M A)) -> M (M A))) =_f (join ∘ join)
; unit_join {A} : (join ∘ (fmap unit)) =_f (join ∘ (unit:M A -> M (M A)))
}.
Class Kleisli (M:Type->Type) `{HFunctor: Functor M} :=
{ return' {A} : A -> M A
; bind {A B} : M A -> (A -> M B) -> M B
; left_unit A B (a:A) (f:A->M B) : bind (return' a) f = f a
; right_unit A (ma:M A) : bind ma return' = ma
; bind_assoc A B C (f:A->M B) (g:B->M C) (ma:M A): bind (bind ma f) g = bind ma (fun a => bind (f a) g)
}.

Lemma unit_fmap_join {M:Type->Type} {A B:Type}  `{Monad M} (f:A->M B) : (join ∘ fmap f ∘ unit) =_f f.

Theorem comp_assoc {A B C D:Type} (f:C->D) (g:B->C) (h:A->B) : ((f∘g) ∘ h) =_f (f ∘ (g ∘ h)).


Program Instance monad_kleisli (M:Type->Type) `{HMonad:Monad M} : Kleisli M.
Next Obligation.
apply (unit X).
Defined.
Next Obligation.
apply join.
apply (fmap X0).
assumption.
Defined.
Next Obligation.
unfold monad_kleisli_obligation_2.
unfold monad_kleisli_obligation_1.
change ((join ∘ fmap f ∘ unit) a = f a).
revert a.
apply feq_eq.
cutrewrite (f = id f).
setoid_rewrite <- functor_id.