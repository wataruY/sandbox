Require Import ssreflect Program.
Require Import Arith List Omega.
Require Import List Sorted Permutation.
Require Import Recdef.
Require Import Relations.
Require Import RelationClasses.

Section Msort.
  Generalizable Variables A R.
  Context `(PO:PreOrder A R) `(Rdec:forall x y:A, {R x y}+{R y x}).
End Msort.    