Require Import Image Arith.

Section Pigeonhole.

Variable U V:Type.

Theorem Pigeonhole' :
   forall (A:Ensemble U) (f:U -> V) (n:nat),
     cardinal U A n ->
     forall n':nat, cardinal V (Im _ _ A f) n' -> n' < n -> ~ injective _ _ f.
intros A f n Hcard m HcardF Hmn Hinj.
contradict Hmn.
rewrite (injective_preserves_cardinal U V A f n Hinj Hcard m HcardF).
auto with arith.
Qed.