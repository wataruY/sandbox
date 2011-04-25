
Module Type DICT.
 Parameters (key data dict : Set)
            (empty : dict)
            (add : key -> data -> dict -> dict)
            (find : key -> dict -> option data).
 Axiom (empty_def : forall k, find k empty = None)
       (diff_key : forall (d : dict) (k k' : key) (v : data),
                   k <> k -> find k (add k' v d) = find k d).
End DICT.

Module Type DICT_PLUS.
 Require Import List.
 Declare Module Dict : DICT.
 Parameter build : list (Dict.key * Dict.data) -> Dict.dict.
End DICT_PLUS.

Module Type KEY.
 Parameters (A : Set)
            (eqdec : forall a b:A, {a = b}+{a <> b}).
End KEY.

Require Import ZArith.
Open Scope Z_scope.

Module ZKey : KEY with Definition A:=Z.
 Definition A:=Z.
 Definition eqdec:=Z_eq_dec. 
End ZKey.

Require Import List.

Theorem neq_comm (A : Type) (a b : A): a <> b -> b <> a.
Proof.
  intro H.
  contradict H.  
  auto.
Qed.

Hint Resolve nil_cons : datatypes.

Module LKey (K:KEY) : KEY with Definition A := list K.A.
  Definition A := list K.A.
  Definition eqdec : forall (a b:A), {a = b} + {a <> b}.
  Proof.
    intro a.
    elim a.
      induction b.
        left; auto.

        right.
        apply nil_cons.

      intros a0 k Ha.
      induction b.
        right.
        apply neq_comm.
        apply nil_cons.
      
        case (K.eqdec a0 a1).
          intro H0.
          case (Ha b).
            intro H1.
            subst; auto with datatypes.

            right.
            red.
            injection 1.
            intros; contradiction.

          right.
          red.
          injection 1.
          intros; contradiction.
  Qed.
End LKey.

Module PairKey (K1 K2:KEY) : KEY with Definition A := (K1.A * K2.A)%type.
  Definition A := (K1.A * K2.A)%type.
  Definition eqdec : forall a b:A, {a = b}+{a <> b}.
    destruct a as [a c]; destruct b as [b d].
    Ltac not_eq := right;
                   red; injection 1; intros;
                   contradiction.
    destruct (K1.eqdec a b); subst; try not_eq.
      destruct (K2.eqdec c d); subst.
        auto with datatypes.
        not_eq.
  Defined.
End PairKey.

(* A Module doesn't have the signature KEY also can be used as an argument its signature requires KEY. *)
Module BoolKey.
  Definition A := bool.
  Definition eqdec : forall a b:A, {a=b}+{a<>b}.
    intros a b.
    destruct a; destruct b; auto; right; discriminate.
  Qed.
End BoolKey.

Module BoolKeys : KEY with Definition A := list bool := LKey BoolKey.

Module Type DEC_ORDER.
  Parameter A : Set.
  Bind Scope A_scope with A.
  Local Open Scope A_scope.
  Parameter le lt : relation A.
  Notation "x <= y" := (le x y) : A_scope.
  Notation "x < y" := (lt x y) : A_scope.
  Axiom ordered : order A le.
  Axiom lt_le_weak : forall a b:A, a < b -> a <= b.
  Axiom lt_diff : forall a b:A, a < b -> a <> b.
  Axiom le_lt_or_eq :
      forall a b:A, a <= b -> a < b \/ a = b.
  Axiom lt_eq_lt_dec : forall a b, {a<b}+{a=b}+{b<a}.
End DEC_ORDER.

Definition asymmetry (A:Type) (R : relation A) : Prop :=
  forall x y:A, R x y -> ~ R y x.

Module Type MORE_DEC_ORDERS.
  Parameter A : Set.
  Bind Scope A_scope with A.
  Local Open Scope A_scope.
  Parameter le lt : relation A.
  Notation "x <= y" := (le x y) : A_scope.
  Notation "x < y" := (lt x y) : A_scope.

  Axiom le_trans : transitive _ le.
  Axiom le_refl : reflexive _ le.
  Axiom le_antisym : antisymmetric _ le.
  Axiom lt_asymm : asymmetry _ lt.
  Axiom lt_irreflexive : forall a:A, ~ a < a.
  Axiom lt_trans : transitive _ lt.
  Axiom lt_not_le : forall a b, a<b -> ~ b<=a.
  Axiom le_not_lt : forall a b, a<=b -> ~ b<a.
  Axiom lt_intro : forall a b, a <= b -> a <> b -> a < b.

  Parameter le_lt_dec : forall a b:A, {a <= b}+{b < a}.
  Parameter le_lt_eq_dec : forall a b, a <= b -> {a < b}+{a = b}.
End MORE_DEC_ORDERS.


Module More_Dec_orders (P:DEC_ORDER)
: MORE_DEC_ORDERS
with Definition A := P.A
with Definition le := P.le
with Definition lt := P.lt.
  Definition A := P.A.
  Definition le := P.le.
  Definition lt := P.lt.
  Open Scope A_scope.
  Notation "x <= y" := (le x y) : A_scope.
  Notation "x < y" := (lt x y) : A_scope.

  Theorem le_trans : transitive _ le.
  Proof.
    case P.ordered; tauto.
  Qed.
  Theorem le_refl : reflexive _ le.
  Proof.
    destruct P.ordered; tauto.
  Qed.
  Theorem lt_intro : forall a b:A, a <= b -> a <> b -> a < b.
  Proof.
    intros a b Hle Hdiff.
    destruct (P.le_lt_or_eq _ _ Hle); tauto.
  Qed.
  Theorem lt_irreflexive : forall a:A, ~lt a a.
  intros a H.
  destruct (P.lt_diff _ _ H).
  trivial.
  Qed.
  Theorem le_antisym : antisymmetric _ le.
  Proof.
    case P.ordered; auto.
  Qed.
  Theorem lt_not_le : forall a b:A, a < b -> ~ b <= a.
  Proof.
    intros a b H H'.
    absurd (a = b).
    apply (P.lt_diff _ _ H).
    apply le_antisym.
    apply P.lt_le_weak.
    assumption.
    assumption.
  Qed.
  Theorem le_not_lt : forall a b:A, a <= b -> ~ b < a.
  Proof.
    intros a b H H'.
    apply lt_not_le in H'.
    elim H'.
    assumption.
  Qed.
  Theorem lt_asymm : asymmetry _ lt.
  Proof.
    intros a b H H'.
    eapply  lt_not_le.
    eassumption.
    apply P.lt_le_weak.
    assumption.
  Qed.
  Theorem lt_trans : transitive _ lt.
  Proof.
    intros a b c H0 H1.
    apply lt_intro.
    eapply le_trans; apply P.lt_le_weak; eassumption.
    intro e.
    subst.
    eapply lt_asymm; eassumption.
  Qed.
  Definition le_lt_dec : forall a b:A, {a <= b}+{b < a}.
  intros a b.
  case (P.lt_eq_lt_dec a b).
  destruct 1; auto.
  left; apply P.lt_le_weak; assumption.
  subst; left; apply le_refl.
  intro; auto.
  Defined.
  Definition le_lt_eq_dec : forall a b, a <= b -> {a < b}+{a = b}.
  intros a b H.
  case (P.lt_eq_lt_dec a b).
    destruct 1; eauto.
    intro.
    apply le_not_lt in H.
    contradiction.
  Defined.
End More_Dec_orders.

Module Lexico (D1:DEC_ORDER) (D2:DEC_ORDER) <:
       DEC_ORDER with Definition A := (D1.A*D2.A)%type.
  Open Scope type_scope.
  Module M1 := More_Dec_orders D1.
  Module M2 := More_Dec_orders D2.

  Definition A := D1.A*D2.A.
  Definition le (a b:A) : Prop :=
    let (a1, a2) := a in
      let (b1, b2) := b in
        D1.lt a1 b1 \/ a1 = b1 /\ D2.le a2 b2.
  Definition lt (a b:A) : Prop :=
    let (a1, a2) := a in
      let (b1, b2) := b in
        D1.lt a1 b1 \/ a1 = b1 /\ D2.lt a2 b2.

  Theorem lt_asymmetric : asymmetry _ lt.
  Proof.
    unfold asymmetry, lt.    
    destruct x; destruct y.
    destruct 1.
    intro H0; destruct H0.
    eapply M1.lt_asymm; eassumption.
    destruct H0.
    subst.
    eapply M1.lt_irreflexive; eassumption.
    intro.
    repeat match goal with | [ H:_/\_ |- _ ] => destruct H end.
    destruct H0.
    subst.
    eapply M1.lt_irreflexive; eauto.
    destruct H0.
    eapply M2.lt_asymm; eauto.
  Qed.
  Definition ordered : order _ le.
    split.
    unfold reflexive in |-*; intro x.
    unfold le; case x.
    intros.
    right.
    split; [trivial | apply M2.le_refl].
    unfold transitive, le in |-*.
    simple destruct x; simple destruct y; simple destruct z.
    simple destruct 1.
    intro H0.
    simple destruct 1.
    intro H2.
    left.
    eapply M1.lt_trans; eassumption.
    destruct 1.
    subst.
    auto.
    destruct 1.
    destruct 1.
    subst.
    eauto.
    subst.
    destruct H2; subst.
    right.
    destruct H; split; try trivial; eapply M2.le_trans; eassumption.
    unfold antisymmetric.
    unfold le.
    simple destruct x; simple destruct y.
    simple destruct 1.
    intro.
    simple destruct 1.
    intro.
    elim (M1.lt_asymm _ _ H0 H2).
    destruct 1.
    subst.
    contradict H0.
    eapply M1.lt_irreflexive.
    destruct 1.
    destruct 1.
    subst.
    contradict H2.
    apply M1.lt_irreflexive.
    destruct H2.
    cutrewrite (a0 = a2).
    rewrite H0.
    trivial.
    apply M2.le_antisym; auto.
  Defined.
  Definition lt_le_weak : forall a b:A, lt a b -> le a b.
  unfold lt, le.
  destruct a; destruct b.
  destruct 1.
  auto.
  destruct H; subst.
  right; auto.
  split; try trivial.
  apply D2.lt_le_weak.
  assumption.
  Defined.
  Definition lt_diff : forall a b:A, lt a b -> a <> b.
  unfold lt.
  destruct a; destruct b.
  destruct 1.
  intro H0.
  injection H0.
  intros; subst.
  eapply M1.lt_irreflexive; eauto.
  destruct H; subst.
  intro H1; injection H1; intros; subst.
  eapply M2.lt_irreflexive; eauto.
  Defined.
  Definition le_lt_or_eq :
      forall a b:A, le a b -> lt a b \/ a = b.
  unfold le, lt.
  destruct a; destruct b.
  destruct 1.
  left.
  auto.
  destruct H; subst.
  case (D2.le_lt_or_eq _ _ H0).
  intro; left; right; split; auto.
  intro; subst.
  right; trivial.
  Defined.
  Definition lt_eq_lt_dec : forall a b:A, {lt a b}+{a=b}+{lt b a}.
  unfold lt.
  destruct a; destruct b.
  case (D1.lt_eq_lt_dec a a1).
  destruct 1.
  left; left; auto.
  subst.
  case (D2.lt_eq_lt_dec a0 a2).
  destruct 1.
  left; left; right; split; auto.
  subst.
  left; right.
  trivial.
  intro.
  right; right; split; auto.
  intro.
  right.
  eauto.
  Defined.
End Lexico.  