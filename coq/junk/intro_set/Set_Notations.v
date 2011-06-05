Require Import Ensembles.

Bind Scope set_scope with Ensemble.
Delimit Scope set_scope with set.

Notation "A ⊇ B" := (Included _ B A) (at level 70, no associativity) : set_scope. 
Notation "A ⊆ B" := (Included _ A B) (at level 70, no associativity) : set_scope.
Infix "⋂" := (Intersection _) (at level 40, left associativity) : set_scope.
Infix "⋃" := (Union _) (at level 50, left associativity) : set_scope.
Infix "∖" := (Setminus _) (at level 50, left associativity) : set_scope.
Notation "x ∈ A" := (In _ A x) (at level 20, no associativity) : set_scope.
Notation "x ∉ A" := (not (In _ A x)) (at level 20, no associativity) : set_scope.
Notation "∅" := (Empty_set _) : set_scope.
Notation "∁ A" := (Complement _ A) (at level 1) : set_scope.