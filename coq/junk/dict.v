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

Module LKey (K:KEY) : KEY with Definition A := list K.A.
 Definition A := list K.A.
 Definition eqdec : forall (a b:A), {a = b} + {a <> b}.
 Proof.
   intro a; elim a.
     induction b as [| b' IHb].
       auto with datatypes.

       destruct IHIHb.
         subst.
         right.
         apply nil_cons.

         right; apply nil_cons.

     intros a' k.
     induction b.
       right.
       apply neq_comm.
       apply nil_cons.
       
       case (K.eqdec a' a0).
         case (H b).
           intros; subst.
           auto with datatypes.

           intro Hn.
           right.
           contradict Hn.
           injection Hn.
           tauto.
         
         intro Hn.
         right.
         contradict Hn.
         injection Hn.
         intro; subst.
         tauto.
 Qed.
End LKey.

