Require Import CatSem.CAT.category.

Section Monoid.


Set Implicit Arguments.
Set Strict Implicit.
Unset Automatic Introduction.

Class Monoid_struct (S:Type) :=
{ dot : S -> S -> S
; mon_oid :> Setoid S
; dot_assoc : forall x y z, dot (dot x y) z ==dot x (dot y z)
; unit : S
; unit_id_l : forall y, dot unit y == y
; unit_id_r : forall x, dot x unit == x
}.

Record Monoid :=
{ Mset :> Type
; monoid_struct :> Monoid_struct Mset
}.

Instance Monoid_setoid : Setoid Monoid :=
{ equiv x y := Mset x = Mset y }.
split; unfold Reflexive, Symmetric, Transitive; auto.
intros x y z H H0.
transitivity y; auto.
Qed.

End Monoid.

Section MonoidHom.

Infix "∙" := dot (at level 40).
Notation "'ε'" := unit.

Section Monoid_Hom_Proper.
Variable A:Type.
Variable f:A->A.
Hypothesis Aoid: Setoid A.

Hypothesis Hx:Proper (equiv ++> equiv) f.

Goal forall x y:A, x == y -> f x == f y.
intros.
pose (H':=Hx x y).
apply H'.
assumption.
Qed.

End Monoid_Hom_Proper.

Class Monoid_mor_struct {A B:Type} (M:Monoid_struct A) (M':Monoid_struct B) :=
{ homM  : A -> B
; homM_morphism : Proper (equiv ==> equiv) homM
; hom_distr : forall x y:A, homM (x ∙ y) == homM x ∙ homM y
; hom_id : homM ε == ε
}.

End MonoidHom.

Section Monoid_cat.

Let Mmor (M M':Monoid) : Type.
intros.
eapply Monoid_mor_struct.
apply M.
apply M'.
Defined.

Instance Monoid_equiv : Setoid Monoid.

Notation "# f" := (homM (Monoid_mor_struct:=f)) (at level 0).

Definition Mmor_equiv (M M':Monoid) : relation (Mmor M M') :=
  fun (f g:Mmor M M') => (forall (x:M), #f x = #g x).

Program Instance Mmor_oid M M' : Setoid (Mmor M M') :=
{ equiv  :=  @Mmor_equiv M M' }.
Next Obligation.
unfold Mmor_equiv.
split.
intros f g.
reflexivity.
intros f g H x.
symmetry.
apply H.
intros f g h H0 H1 x.
transitivity (#g x).
apply H0.
apply H1.
Qed.

Let Mmor_id_hom {M:Monoid} : Mset M -> Mset M.
auto.
Defined.

Program Instance Mmor_id_struct {A:Type} {M:Monoid_struct A} : Monoid_mor_struct M M :=
{ homM x := x
}.
Solve Obligations using try reflexivity.
Next Obligation.
intros x y f.
assumption.
Qed.

Let Mmor_comp {A B C:Type} (g:B->C) (f:A->B) := fun (x:A) => g (f x).

Definition Mmor_struct_comp_hom {A B C:Type} (a:Monoid_struct A) (b:Monoid_struct B) (c:Monoid_struct C) :
           Monoid_mor_struct a b -> Monoid_mor_struct b c -> Monoid_mor_struct a c.
intros A B C a b c f g.
assert (HmorF:=(homM_morphism (Monoid_mor_struct:=f))).
assert (HmorG:=homM_morphism (Monoid_mor_struct:=g)).

apply Build_Monoid_mor_struct with (homM:=@Mmor_comp A B C #g #f); unfold Mmor_comp.
intros x y H.
assert (Hf: # f x == #f y).
  apply HmorF; assumption.
apply HmorG; assumption.

intros x y.
symmetry.
rewrite hom_distr.
rewrite <- hom_distr.
reflexivity.

rewrite hom_id.
apply hom_id.
Defined.


Definition MON_mor_equiv {A:Type} (a b:Monoid_struct A) : relation (Monoid_mor_struct a b) :=
  fun f g => forall x:A, #f x = #g x.

Program Instance MON_mor_oid {A:Type} (M:Monoid_struct A) (M':Monoid_struct A) : Setoid (Monoid_mor_struct M M') :=
{ equiv := @MON_mor_equiv _ M M'
}.
Next Obligation.
unfold MON_mor_equiv.
split; unfold Reflexive, Transitive, Symmetric.
reflexivity.
intros a b  H x.
symmetry; apply H.
intros a b c H0 H1 x.
transitivity(#b x); auto.
Qed.

Local Ltac unfold_defs := unfold MON_mor_equiv, Mmor_struct_comp_hom, Mmor_id_struct, Mmor_comp in *.

Program Instance MON_struct {A:Type} : Cat_struct (obj:=Monoid_struct A)  (fun M M' => Monoid_mor_struct M M') :=
{ id a := Mmor_id_struct (M:=a)
; comp := Mmor_struct_comp_hom
; mor_oid := MON_mor_oid
}.
Next Obligation.
unfold MON_mor_equiv.
intros f g Hfg h i Hhi x.
simpl.
assert (Hoid:=homM_morphism (Monoid_mor_struct:=h) ).
unfold Mmor_comp.
rewrite Hfg.
rewrite Hhi.
reflexivity.
Qed.
Next Obligation.
unfold_defs.
destruct f.
simpl in *.
reflexivity.
Qed.
Next Obligation.
unfold_defs;destruct f; simpl in *.
reflexivity.
Qed.
Next Obligation.
unfold_defs; destruct f; destruct g; destruct h; simpl in *.
reflexivity.
Qed.

End Monoid_cat.
