
Section List.

Variable A:Type.

Fixpoint app (l l':list A) : list A :=
  match l with
     | nil => l'
     | cons x xs => cons x (app xs l')
  end.
Notation "[]" := nil.

Require Import List.

Theorem app_nil_r' (l:list A): l ++ [] = l.
induction l; simpl.
reflexivity.
f_equal.
assumption.
Qed.

Theorem app_assoc' (xs ys zs:list A) : xs ++ ys ++ zs = (xs ++ ys) ++ zs.
induction xs; simpl.
reflexivity.
f_equal.
assumption.
Qed.

Theorem rev_app_distr' (l1 l2: list A): rev (l1 ++ l2) = rev l2 ++ rev l1.
induction l1; simpl.
rewrite app_nil_r.
auto.
rewrite IHl1.
rewrite app_assoc.
auto.
Qed.

Theorem rev_rev_id (l: list A): rev (rev l) = l.
induction l; simpl.
auto.
rewrite rev_app_distr.
rewrite IHl.
auto.
Qed.

Theorem fold_right_app' (B:Type) (f:A -> B -> B) (e:B) (xs ys:list A): fold_right f e (xs++ys) = fold_right f (fold_right f e ys) xs.
induction xs; simpl.
auto.
rewrite IHxs.
auto.
Qed.

Definition compose (B C D:Type) (f:C->D) (g:B->C) : B -> D.
auto.
Defined.

End List.

Theorem fold_right_fusion (A B C:Type) (f:A -> B -> B) (e:B) (h:B->C) (g:A->C->C) :
(forall (x:A) (y:B), h (f x y) = g x (h y)) ->
forall xs , (compose _ _ _ h (fold_right f e)) xs = fold_right g (h e) xs.
intro H.
unfold compose.
induction xs; simpl.
trivial.
rewrite H.
rewrite IHxs.
trivial.
Qed.