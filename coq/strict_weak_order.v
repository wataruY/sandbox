Require Import RelationClasses.
Require Import Relation_Definitions.
Require Import Logic.
Require Import Classical.
Require Import Program.Tactics.
Require Import SetoidClass.

Set Implicit Arguments.
Unset Strict Implicit.

Generalizable Variables A R.

Section Relation_Classes.
  Definition Irreflexive `(R:relation A) :=
    forall x, ~  R x x.
  Definition incomparable `(R:relation A) : relation A :=
    fun x y => ~ R x y /\ ~ R y x.
End Relation_Classes.

Section StrictWeakOrder.

  Class StrictWeakOrder `(R:relation A) :=
  { swo_irrefl : Irreflexive R
  ; swo_asym : Asymmetric R
  ; swo_trans : Transitive R
  ; swo_equiv_trans : Transitive (incomparable R)
  }.
  Lemma and_idemp (P:Prop) : P <-> P /\ P.
  tauto.
  Qed.

  Program Instance SWO_incomp_oid `(Hswo:@StrictWeakOrder A R) :
    Setoid A := {| equiv := incomparable R |}.
  Next Obligation.
  split.
  unfold Reflexive,incomparable.
  split; apply swo_irrefl.

  unfold incomparable, Symmetric.
  tauto.

  apply swo_equiv_trans.
  Qed.

  Instance irrefl_trans_asymm
    `(Hirrefl:@Irreflexive A R) `(Htrans:Transitive A R) : Asymmetric R.
  unfold Asymmetric.
  intros x y H0 H1.
  absurd (R x x).
  apply Hirrefl.
  etransitivity; eassumption.
  Qed.

  Instance swo_equiv_trans' {A:Type} (R:relation A)
    (H:forall x y, R x y -> forall z, R x z \/ R z y) :
    Transitive (incomparable R).
  unfold incomparable.
  intros x y z H0 H1.
  destruct_conjs.
  repeat match goal with
    | |- False => contradiction
    | |- ~ _ => unfold not; intro
    | |- _ /\ _  => split 
    | H' : R ?X ?Z |- _ => edestruct (H _ _ H' y)
  end.
  Qed.
End StrictWeakOrder.

Section StrictTotalOrder.

Class Trichotomy `(Aoid:Setoid A) `(R:relation A)  :=
{ ord x y : {R x y}+{x == y}+{R y x} }.

Class StrictTotalOrder `(Aoid:Setoid A) `(R:relation A) :=
{ sto_irrefl : Irreflexive R
; sto_trans : Transitive R
; sto_ord : Trichotomy Aoid R
}.

Instance total_refl {A:Type} (R:relation A)
  (Htotal:forall x y,{R x y}+{R y x}) : Reflexive R.
intro x.
destruct (Htotal x x); assumption.
Qed.
End StrictTotalOrder.

Section StrictTotalOrder_from_StrictWeakOrder_using_Quotient.

Record QuotientSet `(Aoid:Setoid A) : Type :=
  { quotient_set : A
  ;  quotient_class (x y:A) : x == y
}.
Notation "S / Oid" := (@QuotientSet S Oid).

Context `(SWO:StrictWeakOrder A' R).

Let A'oid := (SWO_incomp_oid SWO).
Let S := A' / A'oid.
Let Gt : relation S :=
  fun (A B:S) => forall (a:A') (b:A'), R a b.

Theorem not_lt_in_quot (a b:S) : ~ R (quotient_set a) (quotient_set b).
apply (quotient_class a (quotient_set a) (quotient_set b)).
Qed.

Theorem Gt_irrefl : Irreflexive Gt.
intros A.
unfold Gt.
intro H.
eapply (not_lt_in_quot).
apply H.
Existential 1 := A.
Existential 1 := A.
Qed.

Instance Gt_Asymmetric : Asymmetric Gt.
unfold Gt.
intros A B H0 H1.
apply (not_lt_in_quot) with (a:=A) (b:=B).
apply H0.
Qed.

Instance Gt_Trans : Transitive Gt.
unfold Gt.
unfold Transitive.
tauto.
Qed.

Section Setoid_on_QuotientSet.

  Instance Sequiv_oid : Setoid S := { equiv := incomparable Gt }.
  unfold Gt.
  unfold incomparable.
  split.

  intro x.
  apply -> and_idemp.
  intro H.
  apply not_lt_in_quot with (a:=x) (b:=x).
  apply H.

  intros x y H.
  assumption.

  intros x y z H0 H1.
  assumption.
  Defined.

  Instance quotient_set_proper : Proper (equiv (Setoid:=Sequiv_oid) ==> equiv) (@quotient_set A' _).
  intros x y H.
  simpl in *.
  unfold incomparable, Gt in *.
  destruct_conjs.
  split;
  match goal with
    | |- ~ (R (quotient_set ?X) ?Y) => intro H'; absurd (R (quotient_set X) Y);
      [apply (quotient_class X (quotient_set X) Y)| assumption]
  end.
  Qed.
End Setoid_on_QuotientSet.
Let Soid := Sequiv_oid.

Lemma Sequiv_forall (A B:S) : A == B.
simpl; unfold incomparable, Gt.
apply -> and_idemp.
intro H'.
absurd (R (quotient_set A) (quotient_set A)).
apply (@quotient_class _ _ A).
apply H'.
Qed.

Theorem Sequiv_tricho A B : {Gt A B} + {A == B} + {Gt B A}.
left;right.
apply Sequiv_forall.
Qed.


Program Instance STO_from_SWO : StrictTotalOrder Sequiv_oid Gt :=
{ sto_irrefl := Gt_irrefl ; sto_ord := _ }.
Next Obligation.
split.
apply Sequiv_tricho.
Defined.

End StrictTotalOrder_from_StrictWeakOrder_using_Quotient.
