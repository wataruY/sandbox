Require Import ssreflect Program.
Require Import Relations.

CoInductive llist (A:Type) : Type := | lnil | lcons : A -> llist A -> llist A.
Infix "::" := (lcons _) : llist_scope.
Notation "[]" := (lnil _) (at level 0) : llist_scope.

Delimit Scope llist_scope with llist.
Bind Scope list_scope with list.
Create HintDb llists.

Local Open Scope llist_scope.
Local Generalizable Variables A B.

Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..) : llist_scope.

Program Definition listToLList {A} : list A -> llist A :=
  list_rect (const (llist A)) [] (fun a _ l => a :: l).

Definition emptyb `(xs:llist A) : bool :=
  match xs with
    | [] => true
    | _ => false
  end.

Definition LDest `(xs:llist A) : {x:A & {l:llist A | xs = x :: l}}+{xs = []}.
refine (match xs with
       | [] => inright _ _
       | a :: l => inleft _ _
       end).
  reflexivity.
  by exists a; exists l.
Defined.

Definition LHead `(xs:llist A) : A+{xs = []}.
by refine (match xs with
          | [] => inright _ _
          | x :: _ => inleft _ x
        end).
Defined.

Definition LTail `(xs:llist A) : llist A + {xs = []}.
by refine (match xs as x return llist A + {x = []} with
          | [] => inright _ _
          | _ :: l => inleft _ l
          end).
Defined.

Fixpoint nth n `(xs:llist A) : option A :=
  match xs with
      [] => None
    | a :: l => match n with 0 => Some a | S p => nth p l end
  end.

Notation "xs !! n" := (nth n xs) (at level 30).
      
CoFixpoint unfoldr `(f:A -> option (B*A)) `(a:A) : llist B.
refine (match f a with
       | value (b,a') => _
       | error => _
       end).
  exact (b :: (unfoldr _ _ f a')).
  exact [].
Defined.

CoFixpoint repeat `(a:A) : llist A := a :: (repeat a).

Definition repeat' `(a:A) : llist A.
refine (unfoldr (fun _ => value (a,a)) a).
Defined.

CoFixpoint append `(xs:llist A) (ys:llist A) : llist A :=
match xs with
  | [] => ys
  | a :: l => a :: (append l ys)
end.

Infix "++" := append (right associativity, at level 60) : llist_scope.

CoFixpoint g_omega {A} (xs ys:llist A) : llist A :=
match ys with
  | [] => xs
  | y :: ys' => match xs with
                     | [] => y :: (g_omega ys' ys)
                     | x :: xs' => x :: (g_omega xs' ys)
                   end
end.

Infix "+!+" := g_omega (right associativity, at level 60) : llist_scope.

Definition omega {A} (xs:llist A) := g_omega xs xs.

Definition llist_decompose `(l:llist A) : llist A :=
match l with
    [] => [] 
  | a :: l' => a :: l'
end.

Fixpoint llist_decompose_n (n:nat) `(l:llist A) : llist A :=
  match n,l with
    | 0,_ => l
    | _,[] => []
    | S p, a :: l' => a :: llist_decompose_n p l'
  end.

Inductive finite {A} : llist A -> Prop :=
  | finite_nil : finite []
  | finite_cons a xs : finite xs -> finite (a :: xs).


CoInductive infinite {A} : llist A -> Prop :=
          | infinite_cons a xs : infinite xs -> infinite (a :: xs).

Section another_definition_of_infinite.
  Definition infinite_ok {A} (X:llist A -> Prop) :=
    forall l, X l -> (exists a, exists l', l = a :: l' /\ X l').
  Definition infinite1 {A} (l:llist A) :=
    exists X:llist A -> Prop, infinite_ok X /\ X l.
  Hint Unfold infinite_ok infinite1 : llists.
End another_definition_of_infinite.


CoInductive bisimilar {A:Type} : relation (llist A) :=
          | bisim0 : bisimilar [] []
          | bisim1 (a:A) l l' : bisimilar l l' -> bisimilar (a :: l) (a :: l').

Definition bisimulation {A} (R:relation (llist A)) : Prop :=
  forall t u:llist A, R t u ->
                      match t with
                        | [] => u = []
                        | a :: t' => match u with
                                          | [] => False
                                          | b :: u' => a = b /\ R t' u'
                                        end
                      end.

