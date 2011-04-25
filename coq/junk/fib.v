
Definition extract {A : Set} {P : A -> Prop} (e : sig P) :=
  let (a, _) := e
  in a.

Theorem extract_sutisfy : forall (A:Set) (P:A->Prop) (y:{x:A|P x}),
                          P (extract (P := (fun x => P x)) y).
intros A P y.
destruct y.
simpl.
assumption.
Qed.

Section div_pair.

Require Import ZArith.
Open Scope Z_scope.
Variable div_pair : forall a b:Z, 0< b -> {p:Z*Z | a = fst p * b + snd p /\ 0 <= snd p < b}.

Definition strictly_positiv := {a:Z|0<a}.

(* div_pair_strong (a:Z) (x:strictly_positiv) : {p:Z*Z | a = fst p * (extract x) + snd p /\ 0 <= snd p < (extract x)}. *)