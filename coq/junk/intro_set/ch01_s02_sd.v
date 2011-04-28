Require Import ch01_s02.
Require Import Constructive_sets.
Require Import Ring.
Section SymmetricDifference.
Variable U:Type.
Notation set := (Ensemble U).
Add Ring symmetric_difference_ring : (set_semi_ring U).

Definition SymmetricDifference (U:Type) (A B:Ensemble U) : Ensemble U := ((A ∖ B) ⋃ (B ∖ A)).
Infix "Δ" := (SymmetricDifference _) (at level 65, left associativity) : set_scope.

Theorem sd_comm (A B:set)
: A Δ B = B Δ A.
by extensionality=> x; (destruct 1;[right|left]).
Qed.

Theorem sd_minus (A B:set) (H:classic)
: A Δ B = (A ⋃ B) ∖ (A ⋂ B).
unfold SymmetricDifference.
rewrite union_minus_distrib.
elim_setminus.
repeat rewrite (de_morgan_iu _ _ _ H).
replace (A ⋂ (∁A ⋃ ∁B) ⋃ B ⋂ (∁A ⋃ ∁B)) with
  (A ⋂ ∁A ⋃ A ⋂ ∁B ⋃ B ⋂ ∁A ⋃ B ⋂ ∁B).
  repeat rewrite intersection_compl_empty.
    ring.
ring.
Qed.

Theorem sd_assoc (A B C:set) (H:classic)
: A Δ B Δ C = (A Δ B) Δ C.
by repeat (rewrite sd_minus; last auto).
Qed.

Theorem sd_distr_intersection (A B C:set) (H:classic)
: A ⋂ (B Δ C) = A ⋂ B Δ A ⋂ C.
repeat (rewrite sd_minus; last auto).
elim_setminus.
repeat (rewrite de_morgan_iu; last auto).

End SymmetricDifference.