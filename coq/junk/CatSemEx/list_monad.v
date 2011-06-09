Require Import list_aux.
Require Import CatSem.CAT.monad_def.
Require Import List.
Require Import list_functor.
Section List_Monad.
(* return *)
Program Definition singleton_Eta : NT (Id type_cat) list_functor := Build_NT (trafo:=singleton) _ .
Next Obligation.
split.
simpl.
unfold singleton.
reflexivity.
Qed.

(* join *)
Program Definition flatten_Mu : NT (CompF list_functor list_functor) list_functor := Build_NT (trafo:=flatten) _.
Next Obligation.
split.
simpl.
unfold flatten.
intros c d f xss.
induction xss.
reflexivity.
simpl.
rewrite map_app.
f_equal.
assumption.
Qed.

(* list MonaD *)
Theorem flatten_distrib_app (A:Type) (xss yss:list (list A)) : flatten _ (xss++yss) = flatten _ xss ++ flatten _ yss.
induction xss.
reflexivity.
simpl.
rewrite <- app_assoc.
f_equal; assumption.
Qed.

Program Instance list_monad_struct : MonaD_struct (C:=type_cat) list_functor :=
{ Eta := singleton_Eta;
  Mu := flatten_Mu
}.
Next Obligation.
unfold subst_ax.
simpl.
intros c xss.
induction xss.
reflexivity.
simpl.
rewrite flatten_distrib_app.
f_equal; assumption.
Qed.
Next Obligation.
unfold eta_mu_ax1.
simpl.
intros c xs.
induction xs.
reflexivity.
simpl.
f_equal;assumption.
Qed.
Next Obligation.
unfold eta_mu_ax2.
simpl.
intros c xs.
apply app_nil_r.
Qed.

Definition list_monad : MonaD type_cat := Build_MonaD list_monad_struct.

End List_Monad.

