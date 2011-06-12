Require Import CatSem.CAT.monad_def.

Section Kleisli_category.

Variable C:Cat.
Variable M:MonaD C.

Let objCt := obj C.

Section objCt_mor.

Definition objCt_mor_oid : forall a b:C, Setoid (a ---> M b).
intros a b.
apply mor_oid.
Defined.

End objCt_mor.

Definition compT : forall a b c:objCt, a ---> M b -> b ---> M c -> a ---> M c.
intros a b c f g.
eapply comp.
apply f.
eapply comp.
apply Fmor.
apply g.
apply (Mu (MonaD_struct:=M) c).
*Defined.

Program Instance Kleisli_category_struct : Cat_struct (fun a b => a ---> M b):=
{ mor_oid := objCt_mor_oid
; id := Eta (MonaD_struct:=M)
; comp := compT
}.
Obligation Tactic := unfold compT.
Next Obligation.
intros a b c.
intros f f' Hf
       g g' Hg.
rewrite Hf.
rewrite Hg.
reflexivity.
Qed.
Next Obligation.
intros a b f.
rewrite (Eta1_ax b).
apply id_r.
Qed.
Next Obligation.
intros a b f.
rewrite <- assoc.
rewrite (NTcomm (Eta (MonaD_struct:=M)) f).
rewrite assoc.
rewrite (Eta2_ax (MonaD_struct:=M) b).
simpl.
apply id_r.
Qed.
Next Obligation.
intros a b c d f g h.
etransitivity;[|symmetry].
(* lhs *)
  do 2 rewrite assoc.
  assert (Hassoc: Mu c;;(#M h;;Mu d) == Mu c;;#M h;;Mu d).
    rewrite assoc.
    reflexivity.
  rewrite Hassoc.
  rewrite (NTcomm (Mu (MonaD_struct:=M)) h).
  rewrite assoc.
(* rhs *)
Focus 2.
  repeat rewrite (preserve_comp (Functor_struct:=M)).
  repeat rewrite assoc.
  rewrite <- (Subst_ax (MonaD_struct:=M) d).
  simpl.
reflexivity.
reflexivity.
Qed.

Definition kleisli_category := Build_Cat Kleisli_category_struct.

End Kleisli_category.