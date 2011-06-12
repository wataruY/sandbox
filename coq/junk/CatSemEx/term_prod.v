Require Import product_lemmata.
Require Import CatSem.CAT.initial_terminal.
Require Import CatSem.CAT.monic_epi.
Require Import product_notations.

Section product_with_terminal.

Variable C:Cat.
Variable Hprod:Cat_Prod C.
Variable Hterm:Terminal C.

Notation "1" := (Term (Terminal:=Hterm)).
Implicit Arguments TermMor [obC morC C Terminal a].
Notation "!" := (TermMor (Terminal:=Hterm)).
Implicit Arguments prl [obC morC C Cat_Prod a b].
Implicit Arguments prr [obC morC C Cat_Prod a b].


Variable X:C.

Let mor_x1_1x : X ∏ 1 ---> 1 ∏ X.
apply prod_mor.
eapply !.
apply prl.
Defined.

Let mor_1x_x1 : 1 ∏ X ---> X ∏ 1.
apply prod_mor.
apply prr.
apply !.
Defined.

Theorem comp_term_mor_uniq a b (f:a--->1) (g:a--->b) : f == g ;; !.
rewrite TermMorUnique.
symmetry.
rewrite TermMorUnique.
reflexivity.
Qed.

Instance mor_x1_1x_invertible : Invertible mor_x1_1x :=
{ inverse := mor_1x_x1
}.
unfold mor_x1_1x, mor_1x_x1.
rewrite prod_mor_prod_mor.
rewrite prod_prl.
symmetry.
eapply prod_mor_unique.
cat.
split.
2:reflexivity.
rewrite TermMorUnique.
apply comp_term_mor_uniq.

unfold mor_x1_1x,mor_1x_x1.
rewrite prod_mor_prod_mor.
rewrite prod_prr.
symmetry.
eapply prod_mor_unique.
split.
  cat.
  apply comp_term_mor_uniq.
Qed.

Instance x1x_isomorphic : isomorphic C (X ∏ 1) (1 ∏ X) :=
{ inv_morphism := mor_x1_1x
}.

Let mor_x_1x : X ---> 1 ∏ X := ⟨!,id X⟩.

Let mor_1x_x : 1 ∏ X ---> X := prr.


Program Instance mor_x_1x_inv : Invertible mor_x_1x :=
{ inverse := mor_1x_x }.
Local Obligation Tactic := unfold mor_x_1x, mor_1x_x.
Next Obligation.
rewrite distrib_prod.
rewrite <- comp_term_mor_uniq.
cat.
apply prod_mor_pr_id.
Qed.
Next Obligation.
cat.
Qed.

Instance x1_isomorphic : isomorphic C X (1 ∏ X ).

End product_with_terminal.