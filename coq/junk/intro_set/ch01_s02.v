Require Import Ensembles ssreflect Relations Constructive_sets.
Load Set_Notations.



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

Ltac extensionality := apply Extensionality_Ensembles; split.

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

Notation "∁ A" := (Complement _ A) (at level 1) : set_scope.
Notation Univ := (Full_set _).

Definition EOM (A:set) := forall x:U, A x \/ ~ A x.

Theorem union_compl_univ (A:set)
 (Heom:EOM A) : A ⋃ ∁ A = Univ.
extensionality.
  done.
  move=>x H.
  case (Heom x).
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
  (Heom:EOM A) : ∁ (∁ A) = A.
extensionality=> x.
  by case (Heom x).
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

Theorem compl_imp (A B:set) (Heom:EOM B)
: A ⊆ B <-> ∁ B ⊆ ∁ A.
split.
  move=> AiB x hB hA.
  elim hB.
  by apply AiB.
  rewrite /Complement /Included /In.
  intros.
  case: (Heom x).
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
        (Hclassic: forall P:Prop, ~~P -> P)
: ∁(A ⋂ B) = ∁ A ⋃ ∁ B.
extensionality=> x H.
  apply Hclassic.
  move=> H'.
  apply: H.
  by split; apply Hclassic; contradict H'; [left|right].
  by destruct H; move=> H'; destruct H'; apply: H.    
Qed.

Definition Set_family :=  Ensemble set.

Inductive UnionSF (U:Type) (UU:Ensemble (Ensemble U)) : Ensemble U :=
  UnionSF_intro (x:U) :
  (exists A, A ∈ UU /\ x ∈ A) -> UnionSF _ UU x.
Inductive IntersectionSF (U:Type) (UU:Ensemble (Ensemble U)) : Ensemble U :=
  IntersectionSF_intro  (x:U) :
  (forall A, A∈UU -> x ∈ A) -> IntersectionSF _ UU x.

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

Theorem set_union_minus (A B:set)
: A ∖ B = (A ⋃ B) ∖ B.
extensionality=> x.
  case=> Ax nBx.
  by split;first left.
  by case; destruct 1 as [x Ax| x Bx]; move=> nBx; split.
Qed.

Theorem set_minus_intersection (A B:set)
: A ∖ B = A ∖ A ⋂ B.
extensionality=> x.
  case=> Ax nBx; split.
    done.
    by contradict nBx; case nBx.
  case=> Ax nABx; split.
    done.
    contradict nABx.
    by split.
Qed.

Theorem set_minus_compl_intersection (A B:set)
: A ∖ B = A ⋂ ∁ B.
extensionality=> x.
  by case=> Ax Bx; split.
  by destruct 1 as [x Ax nBx]; split.
Qed.