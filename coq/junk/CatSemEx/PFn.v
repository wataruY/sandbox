Require Import CatSem.CAT.category.

Section Pfn.

Let parrow (a b:Set) := a -> option b.
Infix "~>" := parrow (at level 80).

Definition parrow_equiv :forall a b:Set, relation (a ~> b).
intros a b f g.
exact (forall x:a, f x = g x).
Defined.

Instance parrow_oid (a b:Set) : Setoid (a ~> b) :=
{ equiv := parrow_equiv a b }.
unfold parrow_equiv.
split;congruence.
Defined.

Definition Pfn_id a : a ~> a := Some.
Definition Pfn_comp a b c (f: a ~> b) (g: b ~> c) : a ~> c.
intro x.
case (f x).
  apply g.
  exact None.
Defined.

Program Instance Pfn_struct : Cat_struct parrow :=
{ mor_oid := parrow_oid
; id := Pfn_id 
; comp := Pfn_comp }.
Obligation Tactic := unfold parrow_equiv, Pfn_id, Pfn_comp.
Next Obligation.
intros a b c f g Hfg h i Hhi x.
rewrite Hfg.
destruct (g x); congruence.
Qed.
Next Obligation.
intros a b f x.
destruct (f x); congruence.
Qed.
Next Obligation.
intros a b f g; reflexivity.
Qed.
Next Obligation.
intros a b c d f g h x.
destruct (f x); reflexivity.
Qed.

Definition PFn : Cat := Build_Cat Pfn_struct.

End Pfn.