Load Set_Notations.
Load set_defs.
Section Product.

Variable U V:Type.
Open Scope set_scope.

Inductive Product (A:Ensemble U) (B:Ensemble V) :
          Ensemble (U*V) :=
  Product_intro : forall x y, x∈A -> y∈B -> (x,y)∈Product A B.
Infix "×" := Product (at level 30).

Theorem In_product x A B : x ∈ (A×B) -> fst x∈A /\ snd x∈B.
intro H.
destruct x.
destruct H.
simpl.
auto.
Qed.

Theorem Empty_Product_r (A:Ensemble U) : A × ∅ = ∅.
extensionality;intros x H.
apply In_product in H as [HA HB].
contradict HB.
contradict H.
Qed.

Require Import Image.

Section Proj.
Variables (A:Ensemble U) (B:Ensemble V).
Let X := A×B.

Definition proj1 : U*V -> U.
intro H.
destruct H.
assumption.
Defined.

