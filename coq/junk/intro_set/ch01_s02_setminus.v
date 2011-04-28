Require Import ssreflect Constructive_sets.
Load Set_Notations.
Load set_defs.

Section Setminus.
Variable U:Type.
Notation set := (Ensemble U).
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

Theorem set_minus_disjoint (A B:set)
: A ∖ B = A <-> Disjoint _ A B.
split.
  move=> H.
  apply Extension in H.
  destruct H as [H0 H1].
  split=> x.
  move=> nAB.
  destruct nAB.
  absurd (x ∈ B).
    by apply H1.
    done.
  case =>H.
  extensionality=> x.
    by case.
    move=> Ax.
    split.
      done.
      move=> Bx.
      by destruct (H x).
Qed.

Theorem set_minus_intersect (A B:set)
: A ∖ B = A ⋂ ∁ B.
by extensionality=> x; destruct 1; split.
Qed.

End Setminus.

Global Ltac elim_setminus := repeat rewrite set_minus_intersect.
 