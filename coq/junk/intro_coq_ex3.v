Require Import List.

Fixpoint len {A:Type} (xs:list A) : nat :=
  match xs with
    | nil => 0
    | _::ys => S (len ys)
  end.

Theorem len_length {A:Type} (xs : list A) : len xs = length xs.
induction xs; simpl; auto with datatypes.
Qed.

Fixpoint all_true (xs : list bool) : bool :=
  match xs with
     | nil => true
     | y::ys => (y && all_true ys)%bool
  end.

Definition ohead {A:Type} (xs : list A) :=
  match xs with
    | nil => None
    | x::_ => Some x
  end.

Fixpoint nat_list (s n:nat) : list nat :=
  match n with
    | 0 => nil
    | S p => s :: nat_list (S s) p
  end.

Fixpoint reverse {A:Type} (xs:list A) : list A :=
  match xs with
    | nil => nil
    | y::ys => reverse ys ++ cons y nil
  end.

Theorem reverse_rev {A:Type} (xs:list A) : reverse xs = rev xs.
induction xs; simpl; auto.
rewrite IHxs.
reflexivity.
Qed.