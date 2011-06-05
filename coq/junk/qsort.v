Require Import List.
Require Import Relations.

Section Option.

Definition option_bind {A B:Type} (x:option A) (f:A->option B) : option B.
case x.
apply f.
apply None.
Defined.
Definition option_bind' {A B:Type} (x:option A) (y:option B) := option_bind x (fun _ => y).

Definition option_sum {A:Type} (x:option A) (y:option A) : option A.  
induction x.
exact (value a).
induction y.
exact (value a).
exact None.
Defined.
End Option.

Section BTree.

Variable A:Type.

Inductive Tree : Type := 
  | Node : Tree -> A -> Tree -> Tree
  | Leaf : Tree.

Definition isLeaf : Tree -> bool :=
  fun x => match x with
             | Leaf => true
             | _ => false
           end.

Fixpoint flatten (t:Tree) : list A :=
  match t with
     | Leaf => nil
     | Node xt a yt => a :: flatten xt ++ flatten yt
  end.


  

Fixpoint find_tree (p:A->bool) (t:Tree) : option A :=
  match t with
     | Leaf => None
     | Node xt a yt => if p a
                       then value a
                       else option_sum (find_tree p xt)
                                        (find_tree p yt)
  end.

Theorem find_nil (p:A->bool) : find p nil = None.
auto.
Qed.

Theorem option_sum_none_l (x:option A) : option_sum None x = x.
induction x;auto.
Qed.

Theorem option_sum_none_r (x:option A) : option_sum x None = x.
induction x;auto.
Qed.

Theorem find_option_sum (p:A->bool) (xs ys:list A) :
find p (xs++ys) = option_sum (find p xs) (find p ys).
Local Ltac foo := repeat (rewrite app_nil_l in *|-* || rewrite app_nil_r in *|-* || rewrite find_nil in *|-* || rewrite option_sum_none_l in *|-* || rewrite option_sum_none_r in *|-* || reflexivity).
induction xs; induction ys; foo.
simpl.
case (p a).
reflexivity.
rewrite IHxs.
reflexivity.
Qed.

Theorem find_tree_flatten (xt:Tree) (p:A->bool) : find_tree p xt = find p (flatten xt).
induction xt as [xt IHxt a yt IHyt|].
  simpl;case (p a).
    auto.
    rewrite IHxt.
    rewrite IHyt.
    rewrite find_option_sum.
    reflexivity.
    auto.
Qed.