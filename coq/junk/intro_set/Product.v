Load Set_Notations.
Load set_defs.
Require Import Constructive_sets.
Require Import SetoidClass.
Require Import Setoid.
Require Import Program.Tactics.
Require Import Classical_sets.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.

Section Ensembleoid.
Variable U:Type.
Program Instance Ensemble_oid : Setoid (Ensemble U) :=
  { equiv A B := Same_set U A B }.
Solve Obligations using split; unfold Same_set, Reflexive, Symmetric, Transitive; intros; destruct_conjs; split; auto with sets.
End Ensembleoid.

Section Product.
Open Scope set_scope.
Section Product_def.
Inductive Product {U V:Type} (A:Ensemble U) (B:Ensemble V) :
          Ensemble (U*V) :=
  Product_intro : forall x y, x∈A -> y∈B -> (x,y)∈Product A B.
End Product_def.
Infix "×" := Product (at level 30).

Theorem in_product {U V} (x:U*V) A B : x ∈ (A×B) -> fst x∈A /\ snd x∈B.
intro H.
destruct x.
destruct H.
simpl.
auto.
Qed.

Theorem product_prop {U V A B} (x:U) (y:V) : (x,y) ∈ (A × B) <-> (x∈A /\ y∈B).
  split; intro.
  apply in_product in H; simpl in *.
  destruct_conjs;split; assumption.

  constructor; tauto.
Qed.
Theorem product_elem_swap {U V A B} (x:U) (y:V) : (x,y) ∈ (A×B) <-> (y,x) ∈ (B×A).
  split; intros H;
    apply in_product in H; simpl in *;
      constructor; tauto.
Qed.


Section empty_product.
Variable U V:Type.
Let A_oid := Ensemble_oid U.
Let prod_oid1 := Ensemble_oid (U*V)%type.
Let prod_oid2 := Ensemble_oid (V*U)%type.
Let prod_oid3 := Ensemble_oid (U*U)%type.
Let B_oid := Ensemble_oid V.
Theorem empty_product (A:Ensemble U) (B:Ensemble V) :
  A == ∅ -> (A×B) == ∅ /\ (B×A) == ∅.
intros [H I].
assert (H0:A == ∅).
  split; assumption.
simpl in H0.
apply Extensionality_Ensembles in H0.
subst.
split; (split; [intros [x y] H1; apply in_product in H1; simpl in H1; destruct_conjs; contradiction|auto with sets]).
Qed.
End empty_product.
  
  
Theorem Empty_Product_r {U V} (A:Ensemble U) : A × (Empty_set V) = ∅.
extensionality;intros x H.
apply in_product in H as [HA HB].
contradict HB.
contradict H.
Qed.

  Section Projection.
    Variable U V:Type.
    Variable AB:Ensemble (U*U).
    Inductive Proj1  : Ensemble U :=
      ProjL_intro x y : (x,y) ∈ AB -> x ∈ Proj1.
    Inductive Proj2  : Ensemble U :=
      ProjR_intro x y : (x,y) ∈ AB -> y ∈ Proj2.
    Theorem inv_Proj1 x : x ∈ Proj1 -> exists y, (x,y) ∈ AB.
      intros H.
      inversion_clear H.
      match goal with | [H: (_,?Y) ∈ AB |- _] => exists Y end.
      assumption.
    Qed.
    Theorem inv_Proj2 y : y ∈ Proj2 -> exists x, (x,y) ∈ AB.
      intro H.
      inversion_clear H.
      match goal with | [H: (?X,_) ∈ AB |- _] => exists X end.
      assumption.
    Qed.
    Variable A: Ensemble U.
    Variable B: Ensemble V.
    End Projection.

End Product.
Infix "×" := (Product) (at level 30).

Section Relation.

Variable U:Type.

Record Relation (A B:Ensemble U) :=
  { graph :> Ensemble (U*U); graph_prop : graph ⊆ (A × B) }.
Definition dom {A B:Ensemble U} (R:Relation A B) := Proj1 (graph R).
Definition cod {A B:Ensemble U} (R:Relation A B) := Proj2 (graph R).
Hint Unfold dom : relation.
Hint Unfold cod : relation.

Let Pairoid := Ensemble_oid (U*U).
Ltac destruct_Proj :=
  repeat (try match goal with 
        | [H: _ ∈ Proj1 _ |- _ ] => apply inv_Proj1 in H
      end ;
  try match goal with
        | [H: _ ∈ Proj2 _ |- _ ] => apply inv_Proj2 in H
      end).

Ltac derive_base := do 3
    match goal with
      | [H:ex _ |- _ ] => destruct H
      | [H:_ ∈ graph _ |- _] => apply graph_prop in H
      | [H:_ ∈ (_ × _) |- _] => apply in_product in H; simpl in H; destruct H
    end.
Ltac proj_imply_base := destruct_conjs; try split; destruct_Proj; repeat derive_base; assumption.

Section Lemmas.

Variable A B:Ensemble U.
Variable R:Relation A B.


Theorem graph_weak x y : (x,y) ∈ R -> (x,y) ∈ (A × B).
intro H.
apply graph_prop in H.
assumption.
Qed.

Theorem inv_dom x : x ∈ dom R -> exists y, y ∈ cod R /\ (x,y) ∈ R.
autounfold with relation.
intro H.
apply inv_Proj1 in H.
destruct H as [y Hy].
exists y.
split; [econstructor|]; eassumption.
Qed.
Theorem inv_cod y : y ∈ cod R -> exists x, x ∈ dom R /\ (x,y) ∈ R.
autounfold with relation.
intro H.
apply inv_Proj2 in H.
destruct H as [x Hx].
exists x.
split;[ econstructor|]; eassumption.
Qed.
Theorem cod_dom_graph : R ⊆ (dom R × cod R). 
autounfold with relation.
intros [x y] H.
split;econstructor; eassumption.
Qed.

Theorem cod_dom_inc_product : (dom R × cod R) ⊆ (A × B).
  autounfold with relation.
  intros [x y] H.
  apply in_product in H.
  simpl in H.
  proj_imply_base.
Qed.

End Lemmas.


Program Instance Relation_oid {A B} : Setoid (Relation A B) :=
  { equiv R R' := graph R == graph R' }.
Next Obligation.
replace ((fun R R' : Relation A B => Same_set (U * U) (graph R) (graph R'))) with
   ((fun R R' : Relation A B => (graph R) == (graph R'))).
2: auto.
split; autounfold; intros.
reflexivity.
symmetry; assumption.
etransitivity; eauto.
Qed.

Program Definition Empty_Rel (A B:Ensemble U) : Relation A B :=
  {|  graph := ∅ |}.
Next Obligation.
auto with sets.
Qed.

Inductive Dup (A:Ensemble U) : Ensemble (U*U) :=
  Dup_intro x : x ∈ A -> (x,x) ∈ Dup A.

Program Definition Identity_Rel (A:Ensemble U) : Relation A A :=
  {| graph xy := let (x,y) := xy in x = y /\ x ∈ A |}.
Next Obligation.
intros [x y] H.
unfold In in *.
destruct_conjs.
subst.
split;auto with sets.
Qed.

Definition Swap {U V} (A:Ensemble (U*V)) : Ensemble (V*U) :=
  fun x => (snd x, fst x) ∈ A.
Hint Unfold Swap : relation.

Program Definition Inverse {A B} (R:Relation A B) : Relation B A :=
  {| graph := Swap (graph R) |}.
Next Obligation.
intros [x y] H.
unfold Swap,In in H.
simpl in H.
apply product_elem_swap.
eapply graph_prop.
eassumption.
Qed.

Theorem dom_weak {A B} (R:Relation A B) : dom R ⊆ A.
autounfold with relation.
intros x H.
proj_imply_base.
Qed.

Let Soid := Ensemble_oid U.

Theorem dom_inv_cod {A B} (R:Relation A B) : dom (Inverse R) == cod R.
autounfold with relation.
simpl.
split; intros x H.
destruct_Proj.
destruct H as [y Hy].
esplit.
instantiate (1:=y).
unfold Swap,In in Hy.
simpl in Hy.
assumption.

inversion_clear H.
econstructor.
unfold In,Swap.
eassumption.
Qed.

Theorem cod_inv_dom {A B} (R:Relation A B) : cod (Inverse R) = dom R.
apply Extensionality_Ensembles.
split; intros x H.
  autounfold with relation in *.
  simpl in H.
  inversion_clear H.
  econstructor.
  eassumption.

  autounfold with relation in *.
  simpl.
  inversion_clear H.
  econstructor.
  eassumption.
Qed.

Theorem inv_inv {A B} (R:Relation A B) : Inverse (Inverse R) == R.
simpl.
split; intros [x y] H.
  unfold Swap in H.
  unfold In in H.
  simpl in H.
  assumption.

  unfold Swap, In.
  apply H.
Qed.

Theorem inv_monotonic {A B} (R S:Relation A B) (H:R ⊆S) : Inverse R ⊆ Inverse S.
  simpl.
  intros [x y] Hx.
  unfold Swap,In in Hx|-*.
  simpl in Hx|-*.
  apply H.
  assumption.
Qed.

Program Definition RelProd {A B C D}  (R:Relation A B) (S:Relation C D) : Relation A D :=
  {| graph wz := let (w,z) := wz in
    exists x, x ∈ B /\ exists y, y ∈ C /\ x = y /\ (w,x) ∈ R /\ (y,z) ∈ S|}.
Next Obligation.
  intros [w z] H.
  unfold In in H.
  destruct H as [x [Hx H]].
  destruct H as [y [Hy [Hxy H]]].
  destruct H as [Hw Hz].
  split.
  assert (Hab : (w,x) ∈ (A×B)).
    exact (graph_prop Hw).
  inversion_clear Hab; assumption.

  assert (Hcd : (y,z) ∈ (C×D)).
    exact (graph_prop Hz).
  inversion_clear Hcd; assumption.
Qed.
Infix "⋈" := RelProd (at level 80).
Program Instance rel_oid {A B} : Setoid (Relation A B) := { equiv R S := graph R = graph S }.
Next Obligation.
  split; autounfold; congruence.
Qed.


Theorem relprod_graph_inv {A B C D} {R:Relation A B} {S:Relation C D} {w z} :
  (w,z)∈ (R⋈S) <-> exists x, x ∈ B /\ exists y, x = y /\ y ∈ C /\ (w,x) ∈ R /\ (y,z) ∈ S.
split;repeat match goal with
         | [H: ?A |- ?A ] => assumption
         | [H: _ ∈ ?A |- _ ∈ ?A ] => eassumption
         | [|- (_,_) ∈ graph (_ ⋈ _) ] => unfold In;simpl
         | [|- _ -> _] => intro
         | [H: ex _ |- _] => destruct H
         | [H: _ ∈ graph (_ ⋈ _) |- _] => inversion_clear H
         | [H: _ /\ _ |- _] => destruct_conjs
         | [|-ex _] => eexists
         | [|- _ /\ _] => split
end; assumption.
Qed.

Theorem relprod_assoc {A B C D} (R:Relation A B) (S:Relation B C) (T:Relation C D) :
  (R ⋈ S ⋈ T) == (R ⋈ (S ⋈ T)).
  split; intros [w z] H; simpl;unfold In;
  repeat match goal with
           | [H: _ = _ |-_] => subst
           | [|- _ = _] => reflexivity
    | [H: (_,_) ∈ graph (_ ⋈ _) |- _ ] => rewrite relprod_graph_inv in H; destruct H; destruct_conjs
    | [|- ex _ ] => eexists
    | [|- _ /\ _] => split
    | [ H: _ ∈ ?A |- ?A _ ] => eassumption
  end.  
Qed.

Definition Transitive {A B} (R:Relation A B) : Prop :=
  forall x y z,(x,y) ∈ R -> (y,z) ∈ R -> (x,z) ∈ R.

Theorem in_graph_in_base {A B} (R:Relation A B) x y : (x,y) ∈ R -> x ∈ A /\ y ∈ B. 
intro H.
destruct (in_product (graph_prop H)). 
split; auto.
Qed.


Definition self_join_in_self_iff_trans {A B} (R:Relation A B) :
  (R ⋈ R) ⊆ R <-> Transitive R.
split; intro H.
  unfold Transitive; intros x y z Hxy Hyz.
  destruct (in_graph_in_base Hxy) as [H0 H1].
  destruct (in_graph_in_base Hyz) as [H2 H3].
  apply H.
  exists y; split;[assumption|].
  exists y; split;[assumption|].
  split; [reflexivity|].
  tauto.

  intros [x z] Hxz.
  destruct Hxz as [y0 [Ay0 H']].
  destruct H' as [y1 [Ay1 H']].
  destruct_conjs.
  subst.
  eapply H; eassumption.
Qed.

Definition Irreflexive {A B} (R:Relation A B) : Prop :=
  forall x, (x,x) ∉ R.

Theorem no_iden_intersection_r_r_imply_irrefl {A B} (R:Relation A B) :
  Identity_Rel A ⋂ R = ∅ <-> Irreflexive R.
split; intro H.
  intros x Hx.
  apply Extension in H.
  destruct H as [H0 H1].
  assert (Hiden:(x,x) ∈ graph (Identity_Rel A)).
    unfold In.
    simpl.
    split; [reflexivity|].
      assert (Ax:= graph_prop Hx).
      apply in_product in Ax; destruct_conjs.
      assumption.
  absurd ((x,x) ∈ ∅).
    auto with sets.
    apply H0.
    auto with sets.

  apply Extensionality_Ensembles.
  split; intros [x y] Hx.
    absurd ((x,x) ∈ R).
      apply H.
      apply Intersection_inv in Hx.
      destruct Hx as [H0 H1].
      inversion_clear H0.
      congruence.
      
      elim Hx.
Qed.

Definition Symmetric {A B} (R:Relation A B) : Prop :=
  forall x y, (x,y) ∈ R -> (y,x) ∈ R.

Lemma in_invR {A B} (R:Relation A B) x y : (x,y) ∈ Inverse R <-> (y,x) ∈ R.
split; intro H;  unfold In in *; simpl in *;  unfold Swap in *; simpl in *;  assumption.
Qed.

Theorem rop_inc_r_iff_symm {A B} (R:Relation A B) :
  Inverse R ⊆ R <-> Symmetric R.
split.
  intro Rop_inc_R.
  intros x y Rxy.
  apply (Rop_inc_R (y,x)).
  apply in_invR.
  assumption.

  intro Rsym.
  intros [x y] Rinv.
  apply Rsym.
  apply in_invR in Rinv.
  replace (graph (Inverse (Inverse R))) with (graph R) in Rinv.
    assumption.
    (* inv_inv *)
    symmetry.
    apply Extensionality_Ensembles.
    setoid_replace (Same_set (U * U) (Inverse (Inverse R)) R) with
      ((Inverse (Inverse R))  == R).
    apply inv_inv.
    tauto.
Qed.

Definition Functional {A B} (R:Relation A B) : Prop :=
  forall x y z, (x,y) ∈ R -> (x,z) ∈ R -> y = z.

Lemma in_swap {A B} (R:Relation A B) x y : (x,y) ∈ Swap R = (y,x) ∈ R.
reflexivity.
Qed.

Theorem invR_join_R_inc_iden_iff_functional {A B} (R:Relation A B) :
  (Inverse R ⋈ R) ⊆ Identity_Rel (cod R) <-> Functional R.
  unfold cod.  
split.
  intro invR_R_inc_Id.
  intros x y z Hxy Hxz.
  assert (invRR : (y,z) ∈ (Inverse R ⋈ R)).
    unfold In.
    simpl.
    exists x.
    split.
    Ltac in_base_set :=
      match goal with
        | [R:Relation ?A ?B, Hin:(?X,?Y) ∈ ?R |- ?X ∈ ?A ] =>
          let H' := fresh in assert (H':=graph_prop Hin);
            apply in_product in H'; simpl in H'; tauto
      end.
    in_base_set.
    exists x;split.
    in_base_set.
    split; [reflexivity|].
    split; [|assumption].
    rewrite in_swap.
    assumption.
    destruct (invR_R_inc_Id _ invRR).
    assumption.

  intros Rfun [x y] iRRxy.
    unfold In in iRRxy.
    simpl in iRRxy.
    destruct iRRxy as [z [Hz H]].
    destruct H as [w [Hw H]].
    destruct H as [eq_z_w [swapRxz Rwy]].
    subst.
    rewrite in_swap in swapRxz.
    constructor.
    eapply Rfun.
      eassumption.
      assumption.
    econstructor.
    eassumption.
Qed.

Definition Surjective {A B} (R:Relation A B) : Prop :=
  forall x, x ∈ dom R -> exists y, (x,y) ∈ graph R.

Program Definition RelCast {A B} (R:Relation A B) C D (H0:A ⊆ C) (H1:B ⊆ D):  Relation C D :=
  {| graph := graph R |}.
Next Obligation.
  intros [x y] H.
  assert (H':=in_product (graph_prop H)); simpl in H'.
  split; auto with sets.
    apply H0; tauto.
    apply H1; tauto.
Qed.

Definition RelProj1 {A B} (R:Relation A B) (C:Ensemble U) : Ensemble U :=
  fun x => exists y, y∈ (C ⋂ cod R) /\ x ∈ dom R.
Hint Unfold Surjective : relation. 
Hint Unfold RelProj1 : relation.

Theorem join_cod_dom_imply_surjective {A B} (R:Relation A B) : dom R == RelProj1 R (cod R) <-> Surjective R.
split; intro H.
  intros x Hx.
  apply inv_Proj1.
  assumption.

  split; intros x Hx.
    (* dom R ⊆ R.cod R *)
    unfold In,RelProj1.
    replace (cod R ⋂ cod R) with (cod R).
    assert (xRy: exists y : U, (x, y) ∈ graph R).
      exact (H x Hx).
    destruct xRy as [y Hy].
    exists y.
    unfold cod,dom.
    split.
      eapply ProjR_intro; eassumption.
      eapply ProjL_intro; eassumption.
    (* ⋂ idemp *)
    apply Extensionality_Ensembles.
      split; intros y Hy.
        split; assumption.
        inversion Hy; assumption.

    (* R.cod R ⊆ dom R *)
    unfold RelProj1 ,In in Hx.
    destruct Hx as [y Hy].
    apply Hy.
Qed.    

End Relation.