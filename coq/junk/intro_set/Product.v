Load Set_Notations.
Load set_defs.
Require Import Constructive_sets.
Require Import SetoidClass.
Require Import Setoid.
Require Import Program.Tactics.
Require Import Classical_sets.
Require Import ChoiceFacts.

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

Theorem Empty_Product_l {U V} (B:Ensemble V) : (Empty_set U) × B = ∅.
extensionality; intros x H.
  apply in_product in H as [H0 HB].
  contradiction.
  contradiction.
Qed.

Section Projection.
  Variable U V:Type.
  Variable A:Ensemble U.
  Variable B:Ensemble V.
  Section Proj_def.
  Variable S:Ensemble (U*V).
  Inductive Proj1 : Ensemble U :=
    Proj1_intro x : (exists y, (x,y) ∈ S) -> x ∈ Proj1.
  Theorem in_proj1 x : x ∈ Proj1 -> (exists y, (x,y) ∈ S).
    inversion_clear 1.
    assumption.
  Qed.
  Inductive Proj2  : Ensemble V :=
    Proj2_intro y : (exists x, (x,y) ∈ S) -> y ∈ Proj2.
  Theorem in_proj2 y : y ∈ Proj2 -> (exists x, (x,y) ∈ S).
    inversion_clear 1; assumption.
  Qed.
  End Proj_def.
  Theorem Proj_prop :
    (A × B) = (Proj1 (A × B) × Proj2 (A × B)).
    apply Extensionality_Ensembles.
    split; intros [x y] H.
    split; econstructor; eauto.
    repeat match goal with
             | [H: ?X |- ?X ] => assumption
             | [|- (_,_) ∈ (_ × _)] => split
             | [H: (_,_) ∈ (_ × _) |- _] => apply in_product in H ; simpl in H
             | [H: _ /\ _ |- _] => destruct H
             | [H: _ ∈ Proj1 _ |- _] => apply in_proj1 in H; destruct H
             | [H: _ ∈ Proj2 _ |- _] => apply in_proj2 in H; destruct H  
           end.
  Qed.
End Projection.

End Product.
Infix "×" := (Product) (at level 30).


Section Relation.

Variable U:Type.

Let pr1 := @Proj1 U U.
Let pr2 := @Proj2 U U.
Hint Unfold pr1 : relation.
Hint Unfold pr2 : relation.

Record Relation (A B:Ensemble U) :=
  { graph :> Ensemble (U*U); graph_prop : graph ⊆ (A × B) }.
Infix "--->" := Relation (at level 50). 
Definition dom {A B:Ensemble U} (R:A ---> B) := pr1 (graph R).
Theorem dom_prop {A B} (R:A ---> B) x :
  x ∈ dom R <-> exists c, (x,c) ∈ R.
split.
  intro xR.
  inversion_clear xR.
  eauto.

  intros H.
  destruct_conjs.
  constructor.
  eauto.
Qed.
Definition cod {A B:Ensemble U} (R:Relation A B) := pr2 (graph R).
Theorem cod_prop {A B} (R:A ---> B) y :
  y ∈ cod R <-> exists x, (x,y) ∈ R.
split.
  inversion_clear 1.
  eauto.

  intro;destruct_conjs.
  constructor; eauto.
Qed.
Hint Unfold dom : relation.
Hint Unfold cod : relation.

Theorem rel_inc_prod {A B} (R:A ---> B) : R ⊆ (A × B).
apply graph_prop.
Qed.

Let Pairoid := Ensemble_oid (U*U).

Ltac in_base_set := try match goal with
    | [R: ?A ---> _|- ?X ∈ ?A] =>
      eapply proj1;
        try match goal with
          | [H: (X,?Y) ∈ graph R |- _] =>
            change (X ∈ A) with (fst (X,Y) ∈ A)
        end
    | [R: _ ---> ?B|- ?Y ∈ ?B] =>
      eapply proj2;
        try match goal with
          | [H: (?X,Y) ∈ graph R |- _] =>
            change (Y ∈ B) with (snd (X,Y) ∈ B)
        end
  end;apply in_product; eapply graph_prop; eassumption.

Section Lemmas.

Variable A B:Ensemble U.
Variable R:Relation A B.


Theorem graph_weak x y : (x,y) ∈ R -> (x,y) ∈ (A × B).
apply graph_prop.
Qed.

Theorem in_dom x : x ∈ dom R -> exists y, y ∈ cod R /\ (x,y) ∈ R.
autounfold with relation.
intro H.
apply in_proj1 in H.
destruct H as [y Hy].
exists y.
split.
  constructor.
  eauto.

  assumption.
Qed.

Theorem in_cod y : y ∈ cod R -> exists x, x ∈ dom R /\ (x,y) ∈ R.
autounfold with relation.
intro H.
apply in_proj2 in H.
destruct H as [x Hx].
exists x.
split.
  constructor.
  eauto.

  assumption.
Qed.

Theorem cod_dom_graph : R ⊆ (dom R × cod R). 
autounfold with relation.
intros [x y] H.
split; constructor; eauto.
Qed.


Theorem cod_dom_inc_product : (dom R × cod R) ⊆ (A × B).
  autounfold with relation.
  intros [x y] H.
  apply in_product in H.
  simpl in H.
  destruct H as [H0 H1].
  do 2 match goal with
    | [H: _ ∈ Proj1 _ |-_] => apply in_proj1 in H
    | [H: _ ∈ Proj2 _ |-_] => apply in_proj2 in H
  end.
  destruct_conjs; split; eauto; in_base_set.
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
unfold Swap,In in H;simpl in H.
apply product_elem_swap.
eapply graph_prop.
eassumption.
Qed.

Theorem dom_weak {A B} (R:Relation A B) : dom R ⊆ A.
autounfold with relation.
intros x H.
apply in_proj1 in H; destruct_conjs.
in_base_set.
Qed.

Let Soid := Ensemble_oid U.

Theorem dom_inv_cod {A B} (R:Relation A B) : dom (Inverse R) == cod R.
autounfold with relation.
simpl.
split; intros x H.
apply in_proj1 in H.
constructor.
eassumption.

apply in_proj2 in H.
constructor.
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
split; intros [x y] H;  assumption.
Qed.

Theorem inv_monotonic {A B} (R S:Relation A B) (H:R ⊆S) : Inverse R ⊆ Inverse S.
  simpl.
  intros [x y] Hx.
  apply H.
  assumption.
Qed.

Program Definition RelProd {A B C D}  (R:Relation A B) (S:Relation C D) : Relation A D :=
  {| graph wz := let (w,z) := wz in
    exists x, x ∈ B /\ exists y, y ∈ C /\ x = y /\ (w,x) ∈ R /\ (y,z) ∈ S|}.
Next Obligation.
  intros [w z] H.
  destruct H.
  destruct_conjs.
  split; in_base_set.
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
    eexists.
    eassumption.
Qed.

Definition Injective {A B} (R:Relation A B) : Prop :=
  forall x y z, (x,z) ∈ R -> (y,z) ∈ R -> x = y.

Theorem R_join_Rinv_inc_iden_iff_injective {A B} (R:Relation A B) :
  (R ⋈ Inverse R) ⊆ Identity_Rel (dom R) <-> Injective R.
unfold dom.
split.
  intros H x y z xRz yRz.
  assert (xRR'y:(x,y) ∈ (R ⋈ Inverse R)).
    do 2 (exists z; split; [in_base_set|]).
    split; [reflexivity|].
    split; [assumption|].
    simpl.
    rewrite in_swap.
    assumption.
  destruct (H _ xRR'y).  
  assumption.

  intros Rinj [x y] xRR'y.
  destruct xRR'y as [x' [Bx' H]].
  destruct H as [y' [By' H]].
  destruct H as [x'_eq_y' [xRx' y'R'y]].
  apply in_invR in y'R'y.
  subst.
  do 2 rewrite in_invR in y'R'y.
  constructor.
    symmetry;exact (Rinj _ _ _ y'R'y xRx').
    econstructor.
    eexists; eassumption.
Qed.

Definition RelProj1 {A B} (R:Relation A B) (C:Ensemble U) : Ensemble U :=
  fun x => exists y, y ∈ C /\ (x,y) ∈ R.

Definition Total {A B} (R:Relation A B) :=
  A = dom R.

Theorem join_cod_dom_imply_total {A B} (R:Relation A B) : A = RelProj1 R B <-> Total R.
split; intro H.
  (* -> Total *)
  apply Extensionality_Ensembles.
  apply Extension in H.  
  destruct H as [H0 H1].
  split; intro x.
    (* x ∈ A -> x ∈ dom R *)
    intro Ax.
    assert (xRy:=H0 _ Ax).
    destruct xRy as [y Hy].
    constructor.
    exists y; tauto.
    (* x ∈ dom -> x ∈ A *)
    intro xR.
    apply in_dom in xR.
    destruct_conjs.
    in_base_set.
  (* Total -> *)
  apply Extensionality_Ensembles.
  apply Extension in H.
  destruct H as [AR RA].
  split; intro x.    
    (* A -> R.B *)
    intro Ax.
    assert (xR:=AR x Ax).
    apply in_dom in xR.
    destruct xR as [y [Ry xRy]].
    exists y.
    split; [in_base_set|assumption].
    (* R.B -> A *)
    intro xRB.
    inversion_clear xRB as [y H].
    destruct H as [By xRy].
    in_base_set.
Qed.    

Definition RelProj2 {A B} (R:Relation A B) (C:Ensemble U) : Ensemble U :=
  fun y => exists x, x∈ (C ⋂ dom R) /\ y ∈ cod R.

Definition Surjective {A B} (R:Relation A B) : Prop :=
  cod R = B.

Theorem iden_inc_cod_join_R_iff_surjective {A B} (R:Relation A B) :
  B ⊆ RelProj2 R A <-> Surjective R.
  split.
    intros cod_inc_domR.
    apply Extensionality_Ensembles.    
    split; intro y.
      (* y ∈ cod R -> y ∈ B *)
      intro Ry.
      
      apply in_cod in Ry.
      destruct_conjs.
      in_base_set.
      (* y ∈ B -> y ∈ cod R *)
      intros By.
      assert (ARy:=cod_inc_domR _ By).
      inversion_clear ARy.
      tauto.
    (* Onto -> B ⊆ A.R *)
    intro Rsurj.
    apply Extension in Rsurj.
    destruct Rsurj as [RB BR].
    intros y By.
    assert (Ry := BR _ By).
    apply in_cod in Ry.
    destruct Ry as [x H].
    exists x.
    destruct_conjs.
    split.
      (* x ∈ dom *)
      split; [in_base_set|assumption].
      (* y ∈ cod *)
      eauto.
Qed.

End Relation.