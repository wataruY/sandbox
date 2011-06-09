Load "Type".
Require Import CatSem.CAT.functor.
Require Import List.
Section List_Functor.

Definition List (A:Set) : Set := list A.

Program Instance List_functor_struct :
Functor_struct (C:=type_cat) (D:=type_cat) (Fobj:=List) map.
Next Obligation.
intros a b f g H xs.
induction xs.
reflexivity.
simpl.
f_equal.
rewrite H.
reflexivity.
assumption.
Qed.
Next Obligation.
intro a.
intro xs.
induction xs.
reflexivity.
simpl.
rewrite IHxs.
reflexivity.
Qed.
Next Obligation.
intros a b c f g xs.
induction xs.
reflexivity.
simpl.
rewrite IHxs.
reflexivity.
Qed.
Definition list_functor : Functor type_cat type_cat := Build_Functor List_functor_struct.

End List_Functor.

Section List_Monad.
Require Import CatSem.CAT.monad_def.
(* return *)
Definition singleton (A:Type) (x:A) := x :: nil.
Hint Unfold singleton.
Program Definition singleton_Eta : NT (Id type_cat) list_functor := Build_NT (trafo:=singleton) _ .
Next Obligation.
split.
simpl.
unfold singleton.
reflexivity.
Qed.

(* join *)
Definition flatten (A:Type) := flat_map (A:=list A) (B:=A) (fun x => x).

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

