Require Import CatSem.CAT.monad_def.
Require Import CatSem.CAT.monad_haskell.

Section Kleisli_Monad.

Variable C:Cat.
Variable M:Monad C.

Let eta := weta (Monad_struct:=M).
Let kl := kleisli (Monad_struct:=M).

Program Definition eta_NT : NT (Id C) M :=
          Build_NT _ (trafo:=fun x => eta x).
Next Obligation.
split.
intros a b f.
simpl.
unfold lift.
unfold eta.
apply etakl.
Defined.

Program Definition join_NT : NT (M O M) M :=
          Build_NT _ (trafo:=join (M:=M)).
Next Obligation.
split.
intros a b f.
simpl.
rewrite join_lift.
unfold join.
rewrite (kleisli_lift (id (M a)) f).
rewrite id_l.
reflexivity.
Defined.

Program Instance kleisli_monad_struct : MonaD_struct M :=
{ Eta := eta_NT
; Mu := join_NT
}.
Next Obligation.
intro a.
simpl.
apply join_join.
Qed.
Next Obligation.
intro a.
simpl.
rewrite join_lift.
unfold eta.
apply kl_eta.
Qed.
Next Obligation.
intro a.
simpl.
unfold eta.
apply join_weta.
Qed.