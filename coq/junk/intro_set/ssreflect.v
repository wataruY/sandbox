Require Import ssreflect ssrbool eqtype ssrnat div.

Section HilbertSaxiom.

Variable A B C : Prop.

Lemma HilbertS (hAiBiC:A -> B -> C) (hAiB:A -> B) (hA:A) : C.
Proof.
  by apply: hAiBiC; last exact: hAiB.
Qed.

End HilbertSaxiom.

Section Symmetric_Conjunction_Disjunction.

Lemma andb_sym : forall A B, A && B -> B && A.
Proof.
  case.
    by case.
  done.
Qed.

Lemma andb_sym2 : forall A B, A && B -> B && A.
Proof. by case; case. Qed.

Lemma andb_sym3 : forall A B, A && B -> B && A.
Proof. by do 2! case. Qed.

Lemma and_sym : forall A B:Prop, A /\ B -> B /\ A.
Proof. by move=> a b []. Qed.

Lemma or_sym : forall A B:Prop, A \/ B -> B \/ A.
Proof. by move=> a b [];[apply: or_intror|apply: or_introl]. Qed.

Lemma or_sym2 : forall A B:bool, A \/ B -> B \/ A.
Proof. by move=> [] [] AorB; apply/orP; move/orP : AorB. Qed.

End Symmetric_Conjunction_Disjunction.

Section R_sym_trans.
Require Import Relations.
Variable (D:Type) (R:relation D).

Hypothesis R_sym : symmetric _ R.
Hypothesis R_trans : transitive _ R.

Lemma refl_if : forall x:D, (exists y, R x y) -> R x x.
Proof.
  by move=> x [y Rxy]; apply: R_trans (R_sym _ y _).
Qed.

End R_sym_trans.

Section Smullyan_drinker.

Variable (D:Type) (P:D -> Prop).

Hypothesis (d:D) (EM:forall A:Prop, A\/~A).

Lemma drinker : exists x, P x -> forall y, P y.
Proof.
have [[y notPy]| nonotPy] := EM (exists y, ~P y); first by exists y.
exists d => _ y; case: (EM (P y)) => // notPy.
by case: nonotPy; exists y.
Qed.

End Smullyan_drinker.

Section Equality.

Variable f:nat -> nat.
Hypothesis f00 : f 0 = 0.

Lemma fkk : forall k, k = 0 -> f k = k.
Proof.
  move=> k k0.
  by rewrite k0.
Qed.

Lemma fkk2 : forall k, k=0 -> f k = k.
Proof. by move=> k ->. Qed.

Hypothesis f10 : f 1 = f 0.

Lemma ff10 : f (f 1) = 0.
Proof. by rewrite f10 f00 . Qed.

Variables (D :eqType) (x y:D).

Lemma eq_prop_bool : x = y ->  x == y.
Proof. by move/eqP. Qed.

Lemma eq_bool_prop : x == y -> x = y.
Proof. by move/eqP. Qed.

End Equality.

Section Using_Definition.

Variable U:Type.

Definition set := U -> Prop.

Definition subset (A B:set) := forall x, A x -> B x.

Lemma subset_trans : transitive _ subset.
Proof.
rewrite /transitive /subset => x y z subxy subyz t.
by move/subxy; move/subyz.
Qed.

End Using_Definition.

Section arith.

Lemma plus_commute : forall n m, n + m = m + n.
Proof.
  by elim=> [| n IHn m];
     last rewrite -[n.+1 +m]/(n + m).+1 IHn.
Qed.

Lemma edivnP' : forall m d, edivn_spec m d (edivn m d).
Proof.
  rewrite /edivn => m [|d] //=; rewrite -{1}[m]/(0*d.+1+m).
  elim: m {-2}m 0 (leqnn m) => [|n IHn] [|m] q //=; rewrite ltnS => le_mn.
  rewrite subn_if_gt; case: ltnP => [// | le_dm].
Abort.