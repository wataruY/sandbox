Require Import Relations.

Section Group.

Variable G:Set.
Variable op:G -> G -> G.
Infix "/" := op.

Hypothesis (Q1 : forall a b, a/a = b/b)
           (Q2 : forall a b, a/(b/b) = a)
           (Q3 : forall a b c, (a/a)/(b/c) = c/b)
           (Q4 : forall a b c, (a/c)/(b/c) = a/b).

Definition right_unit f (e:G) := forall a:G, f a e = a.
Definition left_unit f (e:G) := forall a:G, f e a = a.
Definition a_inv_a f (e:G) : forall a:G