Require Export CatSem.CAT.product.
Require Import product_notations.

Section prod_product_lemmata.

Variable C:Cat.
Variable Hprod:Cat_Prod C.

Local Implicit Arguments prl [obC morC C Cat_Prod a b].
Local Implicit Arguments prr [obC morC C Cat_Prod a b].

Theorem distrib_prod {a b c d:C} (f:a ---> b) (g:b ---> c) (h:b ---> d): f ;; ⟨g , h⟩ == ⟨ f ;; g , f ;; h⟩ .
apply prod_mor_unique.
split;rewrite assoc;cat.
Qed.

Theorem prod_mor_pr_id {a b:C} : ⟨prl,prr⟩ == id (a∏b).
rewrite <- product_mor_id.
symmetry.
apply prod_mor_unique.
split;rewrite product_mor_id;cat.
Qed.

Theorem product_mor_prod_mor {a b c d} (f:a--->c) (g:b--->d) : f × g == ⟨prl;;f, prr;;g⟩.
rewrite <- id_l.
rewrite <- prod_mor_pr_id.
apply prod_mor_product_mor.
Qed.

Theorem product_mor_prl {a b c d} (f:a ---> b) {g:c--->d} : f × g ;; prl == prl ;; f.
rewrite product_mor_prod_mor.
apply prod_prl.
Qed.

Theorem product_mor_prr {a b c d} (f:a ---> b) {g:c--->d} : f × g ;; prr == prr ;; g.
rewrite product_mor_prod_mor.
cat.
Qed.

End prod_product_lemmata.