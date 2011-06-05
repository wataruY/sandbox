Require Import Program.
Require Import Setoid.
Section Feq.

Definition feq {A B:Type} (f g:A->B) := forall x:A, f x = g x.
Infix "=_f" := feq (at level 20).

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

Class Monad {M:Type->Type} `(HFunctor: Functor M) :=
{ unit {A:Type} : A -> M A
; join {A:Type} : M (M A) -> M A
; join_fmap {A:Type} : (join ∘ (fmap join:M (M (M A)) -> M (M A))) =_f (join ∘ join)
; unit_join {A:Type} : (join ∘ (fmap unit)) =_f (join ∘ (unit:M A -> M (M A)))
}.