Require Import Arith Finite_sets_facts Powerset_facts Image.
Fixpoint expt (n m:nat) : nat :=
  match m with
    | 0 => 1
    | S p => n * (expt n p)
  end.

Section Powerset_Cardinal.

Theorem power_empty_singleton (U:Type) : Power_set _ (Empty_set U) = Singleton _ (Empty_set _).
apply Extensionality_Ensembles.
split.
unfold Included.
intros.
apply Singleton_intro.
apply Extensionality_Ensembles.
elim H.
intros.
split.
apply Included_Empty.
assumption.
unfold Included.
intros.
elim H.
apply Definition_of_Power_set.
apply Included_Empty.
Qed.

Theorem power_add_split
        (U:Type)
        (A:Ensemble U) (BS:Ensemble (Ensemble U))
        (x:U)
: Power_set U (Add U A x) = (Union _ (Power_set _ A) (Im _ _ (Power_set _ A) (fun y => Add _ y x))).
apply Extensionality_Ensembles.
split.
  (* -> *)
  intros z H.
  destruct H.
  case (Included_Add _ _ _ _ H).
    (* X is included by A *)
    intro.
    apply Union_introl.
    apply Definition_of_Power_set.
    assumption.
    (* exists A' which X is A' U {x} and A' is included by A *)
    intros [A' [Heq Hin]].
    apply Union_intror.
    subst.
    eapply Im_intro.     
      apply Definition_of_Power_set.
      eassumption.
      trivial.
  (* <- *)
  intros z H.
  apply Definition_of_Power_set.
  case (Union_inv _ _ _ _ H).
    (* In (Power_set A) *)
    intro H'.
    intros y H''.
    apply Add_intro1.
    destruct H'.
    auto.
    (* In (Im (fun y => Add U y x) (Power_set A)) *)
    clear.
    intros H y Hy.
    destruct H.
    subst.
    destruct H.
    destruct (Add_inv _ _ _ _ Hy); try subst; auto with sets.
Qed.
