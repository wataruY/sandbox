Load Set_Notations.
Load set_defs.
Require Import Program.Tactics.
Require Import Classical_sets.
Require Import Setoid.

Section CartesionProduct.

Definition Product {U V} (A:Ensemble U) (B:Ensemble V) : Ensemble (U*V).
intros [x y].
exact (x ∈ A /\ y ∈ B).
Defined.
Hint Unfold Product : sets.
Infix "×" := Product (at level 20).
Theorem ProdOK {U } (A:Ensemble U) (B:Ensemble U) x : (x,x) ∈ Product A B <-> x ∈ Intersection _ A B.
  split; intro.
  inversion_clear H.
  split; auto.
  destruct H; auto with sets.
Qed.

Theorem in_prod {U V} (A:Ensemble U) (B:Ensemble V) x y : (x,y) ∈ (A × B) <-> x ∈ A /\ y ∈ B. 
  unfold Product.
  split; intro H.
  inversion_clear H; tauto.
  constructor; tauto.
Qed.
Theorem in_swap_prod {U V} (A:Ensemble U) (B:Ensemble V) x y : (x,y) ∈ (A × B) <-> (y,x) ∈ (B × A).
  split; intro H; apply  in_prod; inversion_clear H; tauto.
Qed.
Infix "=_s" := (Same_set _) (at level 70).

Theorem prod_empty_empty {U} (A:Ensemble U) (B:Ensemble U) : A = ∅ -> A × B = ∅ /\ B × A = ∅.
  intros Aop.
  subst.
  split; apply Extensionality_Ensembles;split; intros [x y]; inversion_clear 1; contradiction.
Qed.

Theorem pair_in_empty_set {U V} (x:U) (y:V) : (x,y)∈∅ -> x ∈ ∅ /\ y ∈ ∅. 
inversion 1.
Qed.

Theorem prod_comm_empty_or_same1 {U} (A B:Ensemble U) : A = ∅ \/ B = ∅ \/ A = B -> A × B = B × A .
intros [H|[H|H]].
  destruct (prod_empty_empty _ B H).
  congruence.

  subst.
  apply Extensionality_Ensembles; split; intros [x y] H.
    destruct (@in_prod U U A (Empty_set U) x y) as [H0 H1].
    destruct (H0 H) as [H2 H3].
    contradiction.

    destruct H.
    contradiction.

  subst; reflexivity.
Qed.

Theorem equiv_union_intersection {U} (A B:Ensemble U) : A = B <-> A ⋃ B = A ⋂ B.
  split.
  intro;subst.
  apply Extensionality_Ensembles.
  split;intros x H.
  destruct H; split; tauto.

  destruct H; auto with sets.

  intro.
  apply Extensionality_Ensembles.
  apply Extension in H.
  destruct H as [H0 H1].
  split; intros x H.
    assert (H':=(Union_introl _ _ B _ H)).
    assert (H'': x ∈ (A⋂B)).
       exact (H0 x H').
    destruct H''; assumption.
    assert (H': x∈ (A ⋂ B)).
      exact (H0 x (Union_intror _ A _ _ H)).
    destruct H'; assumption.
Qed.

Theorem prod_comm_empty_or_same2 : forall {U} (A B:Ensemble U), A × B = B × A -> A = ∅ \/ B = ∅ \/ A = B.
  intros U A B Hprod.
  case (classic (A=∅));case (classic (B=∅)); try tauto.
  (* ... \/ A = B *)
  intros Beq0 Aeq0.
  right;right.
  apply Extensionality_Ensembles.
  apply Extension in Hprod.
  destruct Hprod as [Hprod1 Hprod2].
  split; intros x Hx.
    (* A ⊆ B *)
    case (classic (x ∈ B)); [tauto|].
    intro HB.
    contradict Beq0.
    apply Extensionality_Ensembles; split; intros y Hy.
      destruct (Hprod1 (x,y)).
      split; assumption.
      contradiction.
      contradiction.
    (* B ⊆ A *)
    case (classic (x ∈ A)); [tauto|].
    intros HA.
    contradict Aeq0.
    apply Extensionality_Ensembles.
    split; intros y Hy.
      destruct (Hprod2 (x,y)).
      split; assumption.
      contradiction.
      contradiction.
Qed.

Theorem prod_distr_over_union {U V} (A:Ensemble U) (B:Ensemble V) (C:Ensemble V) : A × (B ⋃ C) = (A × B) ⋃ (A × C).
  apply Extensionality_Ensembles.
  split; intros [x y] Hxy.
    rewrite in_prod in Hxy.
    destruct Hxy as [Ax BCy].
    destruct BCy;[left|right]; split; assumption.
    
    rewrite in_prod.
    apply Union_inv in Hxy.
    destruct Hxy as [H|H]; rewrite in_prod in H.
      split.
        tauto.
        left; tauto.

      split; [|right]; tauto.
Qed.

End CartesionProduct.