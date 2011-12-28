Require Import Program.
Require Import Bvector.

Section Vcase.
  Lemma veccase1 {A:Type} (v:vector A 0) : v = Vnil.
  dependent induction v; reflexivity.
  Qed.
  Lemma veccase2 {A:Type} n (v:vector A (S n)) : exists x:A, exists w, v = (Vcons _ x n w).
  dependent induction v; eauto.  
  Qed.
End Vcase.