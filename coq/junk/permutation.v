Require Import List Permutation Relations Setoid Arith.

Section Sorting.

Variable A:Type.

Infix "=_P" := Permutation (at level 30).

Definition Dec (P:Prop) := {P}+{~P}.

Class EqDec (A:Type) := 
{ eqb (x y:A) : Dec (x = y) }.

Program Fixpoint list_eqb (xs ys:list A) `{H:EqDec A}: Dec (xs = ys) :=
  match xs,ys with
     | nil,nil => left _ _
     | nil,_ => right _ _
     | _,nil => right _ _
     | x::xs',y::ys' =>
         if eqb x y then
           if list_eqb xs' ys' then left _ _
           else right _ _
         else right _ _
  end.
Next Obligation.
Proof.
  split; [intro xs'|]; intros [H0]; discriminate.
Defined.
  
Instance list_EqDec `(H:EqDec A) : EqDec (list A).
split.
intros.
eapply list_eqb.
auto.
Defined.

Class Ord (A:Type) `(Heq:EqDec A):=
{ Le : relation A
; Gt : relation A
; Ord_prf (x y:A) : {Le x y}+{x = y}+{Gt x y}
}.

Instance EqDec_nat : EqDec nat.
split.
induction x; induction y.
left; auto.
right; intro; discriminate.
right; intro; discriminate.
case (IHx y).
left;f_equal;trivial.
intro H;right.
contradict H.
injection H; auto.
Defined.

Theorem nat_tricho x y : {x<=y}+{x=y}+{x>y}.
induction x; induction y.
left; right; trivial.
left;left; auto with arith.
right; auto with arith.
destruct IHx as [[H|H]|H].