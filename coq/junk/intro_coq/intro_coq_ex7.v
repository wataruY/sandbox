Require Import List.

Section Reverse_Reverse.
Variable A:Type.
Let L := list A.

Lemma append_nil (l:L) : l ++ nil = l.
induction l.
reflexivity.
simpl.
rewrite IHl.
reflexivity.
Qed.

Lemma append_assoc (xs ys zs:L) : (xs ++ ys) ++ zs = xs ++ ys ++ zs.
induction xs.
reflexivity.
simpl.
rewrite IHxs.
reflexivity.
Qed.

Lemma reverse_append (xs ys:L) : rev (xs ++ ys) = rev ys ++ rev xs .
induction xs.
rewrite append_nil.
reflexivity.
simpl.
rewrite IHxs.
rewrite append_assoc.
reflexivity.
Qed.

Theorem reverse_reverse (l:L) : rev (rev l) = l.
induction l.
reflexivity.
simpl.
rewrite reverse_append.
rewrite IHl.
reflexivity.
Qed.

End Reverse_Reverse.