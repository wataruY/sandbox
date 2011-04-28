Require Import Arith.

Inductive SRX : Set :=
  | Constant
  | Inv (x:SRX)
  | Add (x y:SRX)
  | Mul (x y:SRX).

Inductive IsSimple : SRX -> Prop :=
  | Simple_const : IsSimple Constant
  | Simple_inv x : IsSimple x -> IsSimple (Inv x).

Inductive Canonical : SRX -> Prop :=
  | Canon_const : Canonical Constant
  | Canon_inv x : Canonical x -> Canonical (Inv x)
  | Canon_add x y : Canonical x -> Canonical y -> Canonical (Add x y)
  | Canon_Mul x y : IsSimple x -> IsSimple y -> Canonical (Mul x y).

Inductive Convertible : SRX -> SRX -> Prop :=
  | Add_commutative x y : Convertible (Add x y) (Add y x)
  | Add_associative x y z : Convertible (Add (Add x y) z) (Add x (Add y z))
  | Mul_commutative x y : Convertible (Mul x y) (Mul y x)
  | Mul_associative x y z : Convertible (Mul (Mul x y) z) (Mul x (Mul y z))
  | Add_distributive_over_Mul x y z : Convertible (Add x (Mul y z)) (Mul (Add x y) (Add x z))
  | Mul_distributive_over_Add x y z : Convertible (Mul x (Add y z)) (Add (Mul x y) (Mul x z))
  | Inv_Inv x : Convertible (Inv (Inv x)) x
  | Convertible_trans x y z : Convertible x y -> Convertible y z -> Convertible x z.

Theorem convertible_add_l a b c
: Convertible a b -> Convertible (Add a c) (Add b c).
inversion_clear 1.
eapply Convertible_trans.
apply Add_associative.
eapply Convertible_trans.
eapply Add_commutative.
eapply Convertible_trans.
eapply Add_associative.
eapply Convertible_trans.
apply Add_commutative.
eapply Convertible_trans.
apply Add_associative.
eapply Convertible_trans.

Goal forall a b c d,
     Convertible (Mul (Add a b) (Add c d))
                 (Add (Add (Mul a c) (Mul a d)) (Add (Mul b c) (Mul b d))).
intros.
eapply Convertible_trans.  
apply Mul_distributive_over_Add.
eapply Convertible_trans.
eapply Convertible_trans.
eapply Mul_distributive_over_Add.