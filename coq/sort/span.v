Require Import ssreflect.
Require Import List.
Require Import Sorted.
Require Import Program.Tactics.
Require Import Permutation.

Set Implicit Arguments.
Unset Strict Implicit.
Generalizable Variables A.

Section Span.
  Inductive HdPred `(P:A -> Prop) : list A -> Prop :=
  | HdPred0 : HdPred P nil
  | HdPred1 a l : P a -> HdPred P (a::l).

  Definition span_prop `(P:A -> Prop) xs ys zs :=
    xs = ys ++ zs /\ Forall P ys /\ HdPred (fun x => ~ P x) zs.
  Hint Unfold span_prop.
  Context `(P:A->Prop).
  Variable (p:forall x, {P x}+{~P x}).
  Definition span xs : {ys:list A & {zs:list A | span_prop P xs ys zs}}.
  induction xs.
  do 2 eexists nil.
  split; first reflexivity.
  split; first constructor.
  constructor.

  destruct IHxs as [ys [zs H]].
  unfold span_prop in H; destruct_conjs.
  case_eq (p a); intros pa Hp.
  exists (a::ys); exists zs.
  split.
  subst;reflexivity.
  split.
  constructor; assumption.
  assumption.

  exists nil; exists (a::xs).
  split.
  reflexivity.
  split.
  constructor.
  constructor.
  assumption.
  Defined.

  Theorem span_perm xs :
    let (ys,s) := span xs in
    let (zs,_) := s in Permutation xs (ys ++ zs).
  Proof.
    induction xs as [|a xs].
    destruct (span nil).
    destruct_exists.
    unfold span_prop in *.
    destruct_conjs.
    rewrite H.
    reflexivity.

    destruct (span xs).
    destruct_exists.
    destruct (span (a :: xs)).
    destruct_exists.
    unfold span_prop in *.
    destruct_conjs.
    subst.
    match goal with
      | [H: ?X = ?Y |- Permutation ?X ?Y] => rewrite H; reflexivity
    end.
    Qed.

    
  Fixpoint span_weak xs : list A * list A :=
    match xs with
      | nil => (nil,nil)
      | a :: l => (if p a then let (ys,zs) := span_weak l in (a :: ys, zs) else (nil, xs))%GEN_IF
    end.
  Theorem span_correct xs : let (ys,s) := span xs in
                            let (zs,_) := s in (ys,zs) = span_weak xs.
  induction xs.
  simpl.
  reflexivity.
  simpl.
  destruct (span xs).
  destruct_exists.
  unfold span_prop in *|-.
  destruct_conjs.
  rewrite <- IHxs .
  destruct (p a); reflexivity.
  Qed.
End Span.
(*   Definition spanb `(p:A -> bool):= *)
(*     span _ (fun x => Bool.bool_dec (p x) true). *)
(* Extract Inductive sigT => "(,)" ["(,)"]. *)
(* Extract Inductive list => "[]" ["[]" "(:)"]. *)
(* Extract Inductive sumbool => "Prelude.Bool" ["Prelude.True" "Prelude.False"]. *)
(* Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False"]. *)
(* Extract Inductive prod => "(,)" ["(,)"]. *)
(* Extract Inlined Constant Bool.bool_dec => "(Prelude.==)". *)
(* Set Extraction Optimize. *)
(* Extraction Language Haskell. *)
(* Recursive Extraction spanb. *)
(* Extraction span_weak. *)