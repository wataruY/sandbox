Require Import List.

Section ForallElement.

Variable A : Type.

Inductive All (P : A -> Prop) : list A -> Prop :=
  | All_nil : All P nil
  | All_cons a l : P a -> All P l -> All P (a :: l).

End ForallElement.
