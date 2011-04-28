Require Import Ensembles ssreflect Relations Constructive_sets.
Load ch01_s02_setminus.
Definition classic := forall P:Prop, ~~P -> P.
Definition EOM := forall P:Prop, P \/ ~ P.

Lemma nnppEom : classic -> EOM.
rewrite /classic /EOM.
move=> H.
move=> P.
apply H.
move=> H0.
elim H0.
right.
contradict H0.
tauto.
Qed.

Section Sets.
Variable U:Type.
Notation set := (Ensemble U).
Open Scope set_scope.
Section Union.

Theorem union_inc_l (A B:set) : Included _ A (Union _ A B).
move=> x Ax.
by apply: Union_introl.
Qed.

Theorem union_inc_r (A B:set) : Included _ B (Union _ A B).
move=> x Bx.
by apply: Union_intror.
Qed.

Theorem inc_trans : transitive set (Included _).
move=> A B C hAB hBC x Ax.
by apply: hBC; apply hAB.
Qed.

Theorem inc_union (A B C:set)
        (hAC:Included _ A C) (hBC:Included _ B C)
: Included _ (Union _ A B) C.
move=> x ABx.
by case: ABx => [y Ax|y Bx]; [apply hAC|apply hBC].
Qed.

Theorem union_idemp (A:set) : Union _ A A = A.
apply Extensionality_Ensembles.
split=> x.
  by case.
  by move=> Ax; apply Union_introl.
Qed.

Theorem union_comm (A B:set) : Union _ A B = Union _ B A.
apply Extensionality_Ensembles.
split=> x;
  by case=> y Hy; [apply Union_intror|apply Union_introl].
Qed.

Theorem union_assoc (A B C:set)
: Union _ A (Union _ B C) = Union _ (Union _ A B) C.
apply Extensionality_Ensembles.
split=> x; case=> y.
  by move=> Ay; do 2 apply Union_introl.
  by case=> z H; first apply Union_introl; apply Union_intror.
  by case=> z H; last apply Union_intror; apply Union_introl.
  by move=> H; apply Union_intror; apply Union_intror.
Qed.

Theorem union_inc_eq (A B:set)
: Included _ A B <-> Union _ A B = B.
split.
  move=>hAiB.
  apply Extensionality_Ensembles.
  split=> x.
    by case=>y; [apply hAiB|].
    by move=>Bx; apply Union_intror.
  move=> H.
  apply Extension in H.
  case: H.
  move=> H0 H1 x Ax.
  apply: H0.
  by apply Union_introl.
Qed.

Theorem Extension' (B C:set) : B = C -> Same_set _ B C.
intro; subst; by split.
Qed.

Theorem inc_union_introl (A B C:set)
: Included _ A B -> Included _ (Union _ A C) (Union _ B C).
move=> AiB x ACx.
by case: ACx => y H; [apply Union_introl; apply AiB|apply Union_intror].
Qed.

Theorem in_empty_false (x:U) : ~ In _ (Empty_set _) x.
move=> H.
by case H.
Qed.

Theorem empty_union_unit (A:set) 
: Union _ (Empty_set _) A = A.
apply Extensionality_Ensembles.
split=> x.
  by move=>EAx; case (Union_inv _ _ _ _ EAx) => H.
  by move=>Ax; apply Union_intror.
Qed.

Theorem intersection_included_l (A B:set)
: Included _ (Intersection _ A B) A.
move=> x; by case.
Qed.

Theorem intersection_included_r (A B:set)
: Included _ (Intersection _ A B) B.
move=> x; by case.
Qed.

Theorem inc_intersection (A B C:set)
: Included _ C A -> Included _ C B ->
  Included _ C (Intersection _ A B).
move=> CA CB x Cx.
by split; [apply CA|apply CB].
Qed.

Theorem intersection_idemp (A:set) : Intersection _ A A = A.
apply Extensionality_Ensembles.
split => x.
  by case.
  move => H.
  by split.
Qed.

Theorem intersection_comm (A B:set) 
: Intersection _ A B = Intersection _ B A.
apply Extensionality_Ensembles.
by split => x; case.
Qed.

Theorem intersection_assoc (A B C:set)
: Intersection _ A (Intersection _ B C) =
               Intersection _ (Intersection _ A B) C.
apply Extensionality_Ensembles.
split => x.
  case => y Ay.
  move=> H.
  by split; [split;[|case H]| case H].
  case => y H.
  move=> Cy.
  by split; [case H | split; first case H].
Qed.

Theorem inc_intersection_eq (A B:set) 
:  Included _ A B <-> Intersection _ A B = A.
split.
  move=> AiB.
  apply Extensionality_Ensembles.
  split => z.
    by case.
    by move => Az; split; last apply AiB.
  move=> AB x Ax.
  apply Extension in AB.
  case: AB => H0 H1.
    by case: (H1 _ Ax).
Qed.



Theorem inc_intersection_intro (A B C:set) 
: A ⊆ B -> A ⋂ C ⊆ B ⋂ C.
move=> AiB x ACx.
by case: ACx => y Ay Cy; split; first apply AiB.
Qed.



Theorem union_distr_intersection (A B C:set)
: (A ⋃ B) ⋂ C = (A ⋂ C) ⋃ (B ⋂ C).
extensionality.
  by move=>x; case=> y; case=> z; [left|right].
  move=>x; case => y; case => z H0 H1; split.
    by left.
    done.
    by right.
    done.
Qed.

Theorem intersection_distr_union (A B C:set)
: A ⋂ B ⋃ C = (A ⋃ C) ⋂ (B ⋃ C).
extensionality;
  move=>x; case=> y.
    case=> z Az Bz; split; by left.
    move=> Cy; split; by right.
  clear.
  destruct 1.
    destruct 1.
      by left; split.
      by right.
    by destruct 1; right.
Qed.

Theorem union_intersection_absorption (A B:set) 
: (A ⋃ B) ⋂ A = A.
extensionality; move=> x.
  destruct 1; first done.
    move=> Ax.
    by split; first left.
Qed.

Theorem intersection_union_absorption (A B:set)
: (A ⋂ B) ⋃ A = A.
extensionality; move=> x.
  destruct 1.
    by destruct H.
    done.
  by move=> H; right.
Qed.

Inductive DSum (B C:set) : set :=
  | DSum_intro x : Disjoint _ B C -> x ∈ (B ⋃ C) -> DSum B C x.
Notation "A ⨁ B" := (DSum A B) (at level 8) : set_scope.

Notation Univ := (Full_set _).

Theorem union_compl_univ (A:set)
 (Hclassic:classic) : A ⋃ ∁ A = Univ.
extensionality.
  done.
  move=>x H.
  case (nnppEom Hclassic (x∈A)).
    by left.
    by right.
Qed.

Theorem intersection_compl_empty (A:set) 
: A ⋂ ∁ A = ∅.
extensionality=> x.
  by case=> y.
  done.
Qed.

Theorem compl_compl (A:set)
  (Hclassic:classic) : ∁ (∁ A) = A.
extensionality=> x.
  by case (nnppEom Hclassic (x∈A)).
  by move=> Ax CAx.
Qed.

Theorem compl_empty_univ : ∁ ∅ = Full_set U.
extensionality=> x.
  done.
  by move => Ux Cx.
Qed.

Theorem compl_univ_empty
: ∁ (Full_set U) = ∅.
extensionality=> x.
  rewrite /Complement /In.
  move=> H.
  by contradict H.
  done.
Qed.

Theorem compl_imp (A B:set) (Hclassic:classic)
: A ⊆ B <-> ∁ B ⊆ ∁ A.
split.
  move=> AiB x hB hA.
  elim hB.
  by apply AiB.
  rewrite /Complement /Included /In.
  intros.
  case: (nnppEom Hclassic (x∈B)).
    done.
    move => H1.
    contradict H0.
    by apply: H.
Qed.

Theorem de_morgan_ui (A B:set)
: ∁(A ⋃ B) = ∁ A ⋂ ∁ B.
extensionality =>x.
  move=> cAB.
    by split=> H; elim cAB; [left|right].
  destruct 1 as [x cA cB].
    move=> H.
    by destruct H; [apply: cA|apply: cB].
Qed.

Theorem de_morgan_iu (A B:set)
        (Hclassic:classic)
: ∁(A ⋂ B) = ∁ A ⋃ ∁ B.
extensionality=> x H.
  apply Hclassic.
  move=> H'.
  apply: H.
  by split; apply Hclassic; contradict H'; [left|right].
  by destruct H; move=> H'; destruct H'; apply: H.    
Qed.

Definition Set_family :=  Ensemble set.


Theorem union_family_inc
        (UU:Ensemble set) (A:set)
: A ∈ UU -> A ⊆ (UnionSF _ UU).
move=> UUA x Ax.
apply UnionSF_intro.
eapply ex_intro.
eauto.
Qed.

Theorem union_system_inv (UU:Ensemble set) (x:U) 
: x ∈ (UnionSF _ UU) -> exists A, A ∈ UU /\ x ∈ A.
move=> H.
destruct H.
auto.
Qed.

Theorem union_family_preserve (UU:Ensemble set) (C:set)
: (forall A, A ∈ UU -> A ⊆ C) -> (UnionSF _ UU) ⊆ C.
move=> H x.
  case => y [z [H0 H1]].
  eapply H; eassumption.
Qed.

Theorem intersection_family_inc (UU:Ensemble set) (A:set)
: A ∈ UU -> (IntersectionSF _ UU) ⊆ A.
move=> Huu x H.
  elim: H => y H.
  by apply H.
Qed.

Theorem intersection_family_preserve (UU:Ensemble set) (C:set)
: (forall A, A∈UU -> C ⊆ A) -> C ⊆ (IntersectionSF _ UU).
move=> HAUU x Cx.
  apply IntersectionSF_intro.
  move=> A Hu.
  by eapply HAUU.
Qed.

Theorem sub_empty_is_empty (A:set) :
A ⊆ ∅ -> A = ∅.
move=> H.
  extensionality=> x.
  move=> Ax.
  by apply H.
  done.
Qed.

Theorem intersection_empty_disj (A B:set)
: A ⋂ B = ∅ -> Disjoint _ A B.
move=> H.
apply: Disjoint_intro=> x ABx.
apply Extension in H.
case: H => [H0 H1].
eapply in_empty_false.
by apply (H0 x).
Qed.

Theorem disj_is_inc_compl1 (A B:set) 
: A ⋂ B = ∅ <-> B ⊆ ∁ A.
split.
  move=> H x Bx.
  have Hdisj := intersection_empty_disj _ _ H.
    destruct Hdisj.
    have H1 := H0 x.
    intro.
    elim H1.
    done.
  move=> H.
  extensionality=> x.
    destruct 1 as [x Ax Bx].
    by have cAx := H _ Bx.
    done.
Qed.

Theorem disj_is_inc_compl2 (A B:set)
: A ⋂ B = ∅ <-> A ⊆ ∁ B.
split.
  move=> ABo.
  have Hdisj := intersection_empty_disj _ _ ABo=> x Ax.
  case: Hdisj=> H Bx.
  eapply H.
  split; eauto.
  move=> AcB.
  extensionality=> x.
  destruct 1 as [x Ax Bx].
  by have cBx := AcB _ Ax.
  done.
Qed.

(* A ⋂ B = ∅ <-> ∁ A ⊇ B <-> A ⊆ ∁ B *)

Theorem inn_complement (A:set) (x:U)
: x ∉ A <-> x ∈ ∁ A.
by split=> H H'; case: H.
Qed.

Theorem set_subet_is_minus_empty (A B:set) (Hclassic:forall P, ~~P -> P)
: A ∖ B = ∅ <-> A ⊆ B.
split.
  move=> H x Ax.
  apply Extension in H.
  destruct H as [H0 _].
  have H : (x ∉ (A ∖ B)).
    move=> H.
    by elim (H0 x).
  rewrite set_minus_intersect in H.
  apply (proj1 (inn_complement _ x)) in H.
  rewrite (de_morgan_iu _ _ Hclassic) in H.
  destruct H.
    by contradiction.
    by apply Hclassic in H.
  move=> AB.
  extensionality=> x.
    rewrite set_minus_intersect.
    destruct 1 as [x Ax cBx].
    elim cBx.
    by apply AB.
    done.    
Qed.

Require Import Ring.

Theorem intersection_fullset (A:set)
: (Full_set _) ⋂ A = A.
extensionality=> x.
  by case.
  by move=> Ax; split.
Qed.

Theorem intersection_empty_zero (A:set)
: ∅ ⋂ A = ∅.
extensionality=> x.
  by destruct 1.
  by intro.
Qed.

Definition set_semi_ring : semi_ring_theory (R:=set) (Empty_set _) (Full_set _) (Union _) (Intersection _) eq.
split.
  apply empty_union_unit.
  apply union_comm.
  apply union_assoc.
  apply intersection_fullset.
  apply intersection_empty_zero.
  apply intersection_comm.
  apply intersection_assoc.
  apply union_distr_intersection.
Defined.

Add Ring set_semi_ring : set_semi_ring.



Theorem minus_distrib_union (A B C:set)
: A ∖ (B ⋃ C) = (A ∖ B) ⋂ (A ∖ C).
elim_setminus.
rewrite de_morgan_ui.
pattern A at 1.
rewrite <- (intersection_idemp A).
ring.
Qed.

Theorem minus_distrib_intersection (A B C:set) (H:forall P:Prop, ~~P -> P)
: A ∖ (B ⋂ C) = (A ∖ B) ⋃ (A ∖ C).
elim_setminus.
rewrite de_morgan_iu; last done.
ring.
Qed.

Theorem union_minus_distrib (A B C:set) 
: (A ⋃ B) ∖ C = (A ∖ C) ⋃ (B ∖ C).
elim_setminus; ring.
Qed.

Theorem intersection_minus_distrib (A B C:set)
: (A ⋂ B) ∖ C = (A ∖ C) ⋂ (B ∖ C).
elim_setminus.
pattern (∁ C) at 1.
rewrite <- intersection_idemp.
ring.
Qed.

Theorem intersection_minus_distrib_r (A B C:set) (H:classic)
: A ⋂ (B ∖ C) = A⋂B ∖ A⋂C.
elim_setminus.
rewrite de_morgan_iu; last done.
cutrewrite ((A ⋂ B) ⋂ (∁A ⋃ ∁C) = B ⋂ (A ⋂ (∁A ⋃ ∁C))); last ring.
replace (A ⋂ (∁A ⋃ ∁C)) with (A ⋂ ∁ C); first ring.
  rewrite (intersection_comm _ (∁A ⋃ ∁C)).
  rewrite union_distr_intersection.
  rewrite (intersection_comm (∁ A) A).
  rewrite intersection_compl_empty.
  rewrite empty_union_unit.
  ring.
Qed.

Theorem minus_minus_union (A B C:set)
: A ∖ B ∖ C = A ∖ (B ⋃ C).
elim_setminus.
rewrite de_morgan_ui.
ring.
Qed.

Theorem minus_minus_distr (A B C:set) (H:classic)
: A ∖ (B ∖ C) = (A ∖ B) ⋃ A ⋂ C.
elim_setminus.
rewrite (de_morgan_iu _ _ H).
rewrite intersection_comm.
rewrite union_distr_intersection.
rewrite (compl_compl _ H).
ring.
Qed.


End Union.
End Sets.
