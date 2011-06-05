Require Import Relations.

Definition Decidable (P:Prop) := {P}+{~P}.

Definition isLeft {A B} : {A}+{B} -> Prop :=
  fun x => if x then True else False.

Class EqDec (A:Type) :=
{
  EQ : relation A ;
  eqb x y : Decidable (EQ x y) ;
  eqb_inv x y : isLeft (eqb x y) -> x = y
}.

Instance prod_eqb A B `(EA:EqDec A, EB:EqDec B) : EqDec (A*B).