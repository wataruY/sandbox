Require Import Arith.

Section BinOp.
Variable A:Set.
Inductive bin : Set := node : bin -> bin -> bin | leaf : A -> bin.

Fixpoint flatten_aux (t fin:bin) : bin :=
  match t with
    | node t1 t2 => flatten_aux t1 (flatten_aux t2 fin)
    | x => node x fin
  end.
Fixpoint flatten (t:bin) : bin :=
  match t with
    | node t1 t2 => flatten_aux t1 (flatten t2)
    | x => x
  end.
Fixpoint check_flattened (t:bin) : bool :=
  match t with
    | node (leaf _) t2 => check_flattened t2
    | node _ _ => false
    | leaf _ => true
  end.

Functional Scheme flatten_ind := Induction for flatten Sort Set.
Functional Scheme flatten_aux_ind := Induction for flatten_aux Sort Set.

Theorem flatten_check t : check_flattened (flatten t) = true.
functional induction (flatten t) as [t t1 t2 IH IHb|].
revert IHb.
generalize (flatten t2).
clear t2.
intro t2.
functional induction (flatten_aux t1 t2);auto.
trivial.
Qed.

End BinOp.

Fixpoint bin_nat (t:bin nat) : nat :=
  match t with
    | node t1 t2 => bin_nat t1 + bin_nat t2
    | leaf n => n
  end.

Implicit Arguments node [A].
Implicit Arguments leaf [A].

Theorem flatten_aux_valid t0 t1 : bin_nat t0 + bin_nat t1 = bin_nat (flatten_aux _ t0 t1).
functional induction (flatten_aux _ t0 t1); auto.
simpl in *|-*.
rewrite <- plus_assoc.
rewrite <- IHb0.
auto.
Qed.

Theorem bin_nat_flatten t : bin_nat (flatten _ t) = bin_nat t.
functional induction (flatten _ t); simpl in *|-*; auto.
rewrite <- IHb.
generalize (flatten _ t2).
clear IHb; clear t2.
intro t2.
functional induction (flatten_aux _ t1 t2); simpl in *|-*;auto.
rewrite IHb0.
rewrite IHb.
ring.
Qed.

Theorem flatten_valid_2 t t' : bin_nat (flatten _ t) = bin_nat (flatten _ t') -> bin_nat t = bin_nat t'.
repeat rewrite bin_nat_flatten; trivial.
Qed.

Theorem reflection_test' x y z t u : x+(y+z+(t+u)) = x+y+(z+(t+u)).
change (bin_nat
          (node (leaf x)
                (node (node (leaf y) (leaf z))
                      (node (leaf t) (leaf u)))) =
        bin_nat
          (node (node (leaf x) (leaf y))
                (node (leaf z) (node (leaf t) (leaf u))))).
apply flatten_valid_2; auto.
Qed.

Ltac model v :=
  match v with
    | (?X1 + ?X2) =>
        let r1 := model X1 with
            r2 := model X2
        in constr:(node r1 r2)
    | ?X1 => constr:(leaf X1)
  end.

Ltac assoc_eq_nat :=
  match goal with
    | [ |- (?X1 = ?X2 :> nat) ] =>
      let term1 := model X1 with
          term2 := model X2
      in (change (bin_nat term1 = bin_nat term2));
         apply flatten_valid_2;
         lazy beta iota zeta delta [flatten flatten_aux bin_nat];
         auto
  end .

Theorem reflection_test'' x y z t u : x+(y+z+(t+u)) = x+y+(z+(t+u)).
assoc_eq_nat.
Qed.
