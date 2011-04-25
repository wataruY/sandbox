
Inductive inspect {A : Type} (x : A) : Prop :=
  it (y : A) : x = y -> inspect x .
