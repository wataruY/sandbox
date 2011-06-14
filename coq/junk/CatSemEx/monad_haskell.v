Require Import CatSem.CAT.monad_def.
Require Import CatSem.CAT.monad_haskell.

Section MonaD_monad.

Variable C:Cat.
Variable M:MonaD C.

Let eta := (Eta (MonaD_struct:=M)).
Let mu := (Mu (MonaD_struct:=M)).

Definition return' : forall c : C, c ---> M c := eta.
Definition bind : forall a b : C, a ---> M b -> M a ---> M b :=
  fun a b f => #M f;;mu b.

Program Instance Monad_klisl : Monad_struct M :=
{ weta := return'
; kleisli := bind
}.
Next Obligation.
unfold bind.
intros a b f g H.
rewrite H.
reflexivity.
Qed.
Next Obligation.
intros a b f.
unfold return',bind.
rewrite <- assoc.
rewrite (trafo_ax (NT_struct:=eta) f).
rewrite assoc.
unfold eta,mu.
rewrite (Eta2_ax (MonaD_struct:=M) b).
exact (id_r f).
Qed.
Next Obligation.
intro a.
unfold bind,return'.
apply (Eta1_ax a).
Qed.
Next Obligation.
intros a b c f g.
unfold bind.
etransitivity.
(* lhs *)
  rewrite assoc.
  assert (Hassoc:(mu b;; ((#) M (a:=b) (b:=M c) g;; mu c)) == (mu b;; (#) M (a:=b) (b:=M c) g);; mu c).
    rewrite assoc.
    reflexivity.
  rewrite Hassoc.
  rewrite (trafo_ax (NT_struct:=mu) g).
  repeat rewrite assoc.
(* rhs *)
Focus 2.  
  symmetry.
  rewrite (preserve_comp f (#M g;;mu c)).
  rewrite (preserve_comp (#M g) (mu c)).
  repeat rewrite assoc.
  assert (mu_mu:=Subst_ax (MonaD_struct:=M) c).
  simpl in mu_mu.
  unfold mu.
  rewrite <- mu_mu.
  reflexivity.
reflexivity.
Qed.

End MonaD_monad.









