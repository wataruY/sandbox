Load Set_Notations.

Open Scope set_scope.

Inductive UnionSF (U:Type) (UU:Ensemble (Ensemble U)) : Ensemble U :=
  UnionSF_intro (x:U) :
  (exists A, A ∈ UU /\ x ∈ A) -> UnionSF _ UU x.
Inductive IntersectionSF (U:Type) (UU:Ensemble (Ensemble U)) : Ensemble U :=
  IntersectionSF_intro  (x:U) :
  (forall A, A∈UU -> x ∈ A) -> IntersectionSF _ UU x.

Global Ltac extensionality := apply Extensionality_Ensembles; split.