Require Import List.

Definition singleton (A:Type) (x:A) := x :: nil.
Definition flatten (A:Type) := flat_map (A:=list A) (B:=A) (fun x => x).
