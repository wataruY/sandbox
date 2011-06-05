CoInductive List (A:Type) : Type :=
| bot
| nil 
| cons : A -> List A -> List A.
Implicit Arguments nil [A].
Implicit Arguments cons [A].
Implicit Arguments bot [A].
CoFixpoint rev {A:Type} (xs:List A) : List A :=
match xs with
  | nil => nil
  | cons x xs' => cons x (rev xs')
  | bot => bot
end.

Theorem 