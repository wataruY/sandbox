Require Import Arith Finite_sets_facts Powerset_facts Image.
Fixpoint expt (n m:nat) : nat :=
  match m with
    | 0 => 1
    | S p => n * (expt n p)
  end.

Section Powerset_Cardinal.

Theorem power_empty_singleton (U:Type) : Power_set _ (Empty_set U) = Singleton _ (Empty_set _).
Proof with auto with sets.
apply Extensionality_Ensembles.
split.
  intros A Hempty.
  apply Singleton_intro.
  destruct Hempty...
  intros A H.
  apply Definition_of_Power_set.
  rewrite (Singleton_inv _ _ _ H)...
Qed.

Theorem power_add_split
        (U:Type)
        (A:Ensemble U)
        (x:U)
: Power_set U (Add U A x) = (Union _ (Power_set _ A) (Im _ _ (Power_set _ A) (fun y => Add _ y x))).
apply Extensionality_Ensembles.
split.
  (* -> *)
  intros B hBiP.
  destruct hBiP as [B hBiAx].
  case (Included_Add _ _ _ _ hBiAx).
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
  intros B HinU.
  apply Definition_of_Power_set.
  case (Union_inv _ _ _ _ HinU).
    (* In (Power_set A) *)
    intro hBinP.
    intros y hBy.
    apply Add_intro1.
    destruct hBinP.
    auto.
    (* In (Im (fun y => Add U y x) (Power_set A)) *)
    clear.
    intros hBinIm y hBy.
    destruct hBinIm as [B hBinP].
    subst.
    destruct hBinP.
    destruct (Add_inv _ _ _ _ hBy); try subst; auto with sets.
Qed.

Theorem cardinal_disj (U:Type) (A:Ensemble U) (x:U) :
~ In _ A x -> 
forall n, cardinal _ A n -> cardinal _ (Add _ A x) (S n).
intros hNotAx n.
induction 1.
  apply card_add; auto with sets.
  apply card_add; [apply card_add|]; assumption.
Qed.

Theorem union_not_in (U:Type) (A B:Ensemble U) (x:U) :
~ In _ A x -> ~ In _ B x -> ~ In _ (Union _ A B) x.
intros HA HB.
contradict HA.
destruct ( Union_inv U A B x HA).
  assumption.
  contradiction.
Qed.

Theorem cardinal_union (U:Type) (A B:Ensemble U) :
Disjoint _ A B ->
forall m n, cardinal _ A m -> cardinal _ B n ->
            cardinal _ (Union _ A B) (m + n).
intros Hdisj m n HcardA.
generalize dependent n.
induction HcardA.
  (* #A = 0 *)
  simpl.
  rewrite Empty_set_zero.
  trivial.
  (* #A n -> #A (S n) *)
  intros.
  simpl.
  rewrite Union_commutative.
  rewrite <- Union_add.
  apply card_add.
  rewrite Union_commutative.
  apply IHHcardA.
    (* preserves, A /\ B = 0 *)
    elim Hdisj.
    intros.
    apply Disjoint_intro.
    intro y.
    assert (H2 := H1 y).
    contradict H2.
    apply Intersection_inv in H2.
    destruct H2.
    apply Intersection_intro;
      [apply Add_intro1|]; assumption.
    assumption.
  (* x </- A \/ B *)
  assert (H1 : ~ In _ B x).
  elim Hdisj.
  intro.
  assert (H2 := H1 x).
  contradict H2.
  apply Intersection_intro;[apply Add_intro2|]; assumption.
  apply union_not_in; assumption.
Qed.

Theorem add_same_eq_inj (U:Type) (A B:Ensemble U) (x:U) :
~ In _ A x -> ~ In _ B x -> Add _ A x = Add _ B x -> A = B.
intros HinA HinB H.
apply Extensionality_Ensembles.
apply Extension in H.
unfold Same_set in *|-*.
unfold Included in *|-*.
destruct H as [H0 H1].
split.
  intros.
  assert (H0' := H0 _ (Add_intro1 U A x x0 H)).
  destruct (Add_inv _ _ _ _ H0').
    assumption.
    rewrite <- H2 in H.
    contradiction.
  intros y H.
  assert (H1' := H1 _ (Add_intro1 _ _ _ y H)).
  destruct (Add_inv _ _ _ _ H1').
    assumption.
    subst.
    contradiction.
Qed.

Theorem im_preserve_cardinal (U:Type) (A:Ensemble (Ensemble U)) (x:U) n :
   (forall y, In _ A y -> ~ In _ y x) ->
   cardinal _ A n ->
   cardinal _ (Im _ _ A (fun y => Add U y x)) n.
intro Hnin.
intro Hcard.
generalize dependent x.
induction Hcard.
intros.
rewrite image_empty.
auto with sets.
intros z Hnin.
rewrite Im_add.
apply card_add.
apply IHHcard.
intros.
apply Hnin.
apply Add_intro1.
assumption.
contradict H.
apply Im_inv in H.
destruct H.
destruct H.
assert (H1 : ~ In _ x0 z).
  apply Hnin.
  apply Add_intro1.
  assumption.
assert (H2 : ~ In _ x z).
  apply Hnin.
  apply Add_intro2.
assert (H3 : x0 = x).
  apply (add_same_eq_inj _ _ _ z).
    assumption.
    assumption.
    assumption.
rewrite <- H3.
assumption.
Qed.

Theorem power_set_cardinal_expt2 (U:Type) (A:Ensemble U) : forall n,
cardinal _ A n -> cardinal _ (Power_set _ A) (expt 2 n).
intro n.
induction 1.
rewrite power_empty_singleton.
simpl.
rewrite <- Empty_set_zero'.
apply card_add.
auto with sets.
auto with sets.
rewrite power_add_split.
simpl.
rewrite plus_0_r.
apply cardinal_union.
apply Disjoint_intro.
intro y.
contradict H0.
apply Intersection_inv in H0.
destruct H0.
induction H0.
induction H1.
rewrite H2 in H0.
apply H0.
auto with sets.
assumption.
assert (H1 : (forall y, In _ (Power_set _ A) y -> ~ In _ y x)).
  intros.
  contradict H0.
  induction H1.
  apply H1.
  assumption.
apply im_preserve_cardinal.
assumption.
assumption.
Qed.