Require Import ssreflect.
Require Import List Arith Omega Program.
Require Import Recdef.

Set Implicit Arguments.

Section NthElemOf.
  Generalizable Variables A B C.
  (* NthElemOf x n l <-> n < length l /\ x ∈ l /\ l[n] = x *)
  Inductive NthElemOf `(x:A) : nat -> list A -> Prop :=
  | neo_hd l : NthElemOf x 0 (x :: l)
  | neo_k n l y : NthElemOf x n l -> NthElemOf x (S n) (y :: l).
  
  Functional Scheme nth_error_ind := Induction for nth_error Sort Prop.

  Theorem NthElemOf_nth_error `(x:A) n l : nth_error l n = value x <-> NthElemOf x n l.
    functional induction (nth_error l n); simpl; split => H.
    done.
    inversion H.
    injection H; move => *; subst; by apply neo_hd.
    by inversion_clear H.
    done.
    inversion H.
    by intuition constructor.
    inversion_clear H; by intuition.
  Qed.
  
  Lemma NthElem_In `(x:A) n l : NthElemOf x n l -> In x l.
  elim.
  by constructor.
  simpl;tauto.
  Qed.
  
  Theorem NthElem_length `(x:A) n l : NthElemOf x n l -> n < length l.
  elim; simpl; by intuition.
  Qed.

End NthElemOf.