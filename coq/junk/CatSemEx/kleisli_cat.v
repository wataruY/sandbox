Require Import CatSem.CAT.monad_def.
Require Import Setoid.
Section Kleisli.

Variable C:Cat.
Variable M:MonaD (cat_struct C).

Let obC := obj C.
Let objCt := obC.
Let homCt := fun x y:obC => x ---> M y.

Theorem homCt_rel : forall x y, relation (x ---> M y).
intros.
unfold relation.
intros.
apply (eq X X0).
Qed.

Let eta := Eta (MonaD_struct:=monaD_struct M).

Section Hoge.

Variable D:Cat.
Let ob := obj D.
Theorem hoge (a b c:ob) (f g: a--->b) (h:b--->c): f==g -> f;;h == g;;h.
intro H.
rewrite H.
reflexivity.
Qed.

Theorem hoge2 (a b c:ob) (f g: b--->c) (h:a--->b): f==g -> h;;f == h;;g.
intro H.
rewrite H.
reflexivity.
Qed.

Theorem hoge3 (a b c:ob) (f g:a--->b) (h i:b--->c) :
f == g -> h == i -> f;;h == g;;i.
intros H0 H1.
rewrite H0.
rewrite H1.
reflexivity.
Qed.

Theorem functor_eq (a b:obj C) (f g:(a--->b)) :  f == g -> #M (a:=a) f == #M (a:=a) g.
intro H.
rewrite H.
reflexivity.
Qed.

Theorem hoge4 (a b c:ob) (h:a--->b) : forall (f g:b--->c), f == g -> h;;f == h;;g.
intros f g.
apply hoge3.
reflexivity.
Qed.
End Hoge.


Definition unit : forall x:objCt, homCt x x := trafo (Eta (MonaD_struct:=M)).
Definition compT : forall a b c:objCt, homCt a b -> homCt b c -> homCt a c.
unfold homCt.
intros a b c f g.
eapply comp.
eapply comp.
apply f.
apply Fmor.
apply g.
assert (H:=(trafo (Mu (MonaD_struct:=M)))).
apply (H c).
Defined.

Program Instance Kleisli_cat_struct : Cat_struct (obj:=objCt) homCt :=
{
  id := unit;
  comp := compT
}.
Next Obligation.
intros x y.
apply (mor_oid x (M y)).
Defined.
Next Obligation.
intros a b c.
unfold Proper.
intros f g H.
intros h i H1.
unfold compT.
rewrite H.
rewrite H1.
reflexivity.
Defined.
Next Obligation.
intros a b f.
unfold homCt in *|-*.
unfold compT.
unfold unit.
assert (H:(#) M (a:=b) (b:=M b) (Eta b);; Mu b  == id (M b)).
assert (hoge:=Eta1_ax (MonaD_struct:=M)).
unfold eta_mu_ax1 in hoge.
assert (hoge':=hoge b).
simpl in hoge'.
apply hoge'.
change ((f;; (#) M (a:=b) (b:=M b) (Eta b));; Mu b == f).
rewrite assoc.
rewrite H.
apply id_r.
Qed.
Next Obligation.
unfold homCt.
intros a b f.
unfold compT.
unfold unit.
assert  (Htrafo:Eta a;; #M (a:=a) (b:=M b) f == f ;; Eta (M b) ).
apply trafo_ax.
apply Eta.
change ( Eta a;; (#) M (a:=a) (b:=M b) f;; Mu b == f).
rewrite Htrafo.
assert (Hem:=(Eta2_ax (MonaD_struct:=M))).
rewrite Assoc.
assert (H: f ;; (Eta (M b);; Mu b) == f;;id (M b)).
rewrite <- (Hem b).
reflexivity.
rewrite id_r in H.
assumption.
Qed.
Next Obligation.
unfold homCt.
unfold compT.
intros a b c d f g h.
assert (Hlhs1:f;; (#) M (a:=b) (b:=M c) g;; Mu c;; (#) M (a:=c) (b:=M d) h;; Mu d ==
       f;;(#) M (a:=b) (b:=M c) g;;#M (#M h);;Mu  (M d);;Mu d).
assert (Hlhs2:f;; (#) M (a:=b) (b:=M c) g;; Mu c;; (#) M (a:=c) (b:=M d) h;; Mu d ==
       f;; (#) M (a:=b) (b:=M c) g;; (Mu c;; (#) M (a:=c) (b:=M d) h);; Mu d).
       rewrite assoc.
       rewrite assoc.
assert (Hlhs3:(Mu c;; ((#) M (a:=c) (b:=M d) h;; Mu d)) == (Mu c;; (#) M (a:=c) (b:=M d) h);; Mu d).
etransitivity.
assert (H:=assoc C (Mu (MonaD_struct:=M) c) (#M h) (Mu (MonaD_struct:=M) d)).
symmetry in H.
apply H.
reflexivity.
repeat rewrite assoc.
apply hoge3.
reflexivity.
apply hoge3.
reflexivity.
apply Hlhs3.
rewrite Hlhs2.
assert (H:=NTcomm (Mu (MonaD_struct:=M)) h).
simpl in H.
assert (Hlhs3: f;; (#) M (a:=b) (b:=M c) g;; (Mu c;; (#) M (a:=c) (b:=M d) h);; Mu d ==
       f;;#M g;; (#) M (a:=M c) (b:=M (M d)) ((#) M (a:=c) (b:=M d) h);; Mu (M d);;Mu d).
apply hoge.
repeat rewrite assoc.
apply hoge2.
apply hoge2.
apply H.
rewrite Hlhs3.
reflexivity.
etransitivity.
apply Hlhs1.
symmetry.
etransitivity.
assert (Hrhs1:(#) M (a:=b) (b:=M d) (g;; (#) M (a:=c) (b:=M d) h;; Mu d) ==
               #M g;;#M (#M h);;#M (Mu d)).
etransitivity.
apply (preserve_comp (Functor_struct:=T M) (g;;#M h) (Mu d)).
etransitivity.
apply hoge.
apply (preserve_comp (Functor_struct:=T M)).
reflexivity.
etransitivity.
apply assoc.
etransitivity.
apply hoge2.
2:reflexivity.
etransitivity.
apply hoge3.
2:reflexivity.
apply Hrhs1.
simpl.
assert (Hrhs2:(#) M (a:=M (M d)) (b:=M d) (Mu d) ;; Mu d== Mu (M d);; Mu d).
symmetry.
assert (H:=Subst_ax (MonaD_struct:=M) d).
simpl in H.
apply H.
assert ((#) M (a:=b) (b:=M c) g;;
   (#) M (a:=M c) (b:=M (M d)) ((#) M (a:=c) (b:=M d) h);;
   (#) M (a:=M (M d)) (b:=M d) (Mu d);; Mu d ==
   (#) M (a:=b) (b:=M c) g;;   (#) M (a:=M c) (b:=M (M d)) ((#) M (a:=c) (b:=M d) h);;  ( (#) M (a:=M (M d)) (b:=M d) (Mu d);; Mu d)).
etransitivity.
repeat rewrite assoc.
apply hoge3.
reflexivity.
apply hoge3.
reflexivity.
apply hoge3.
reflexivity.
reflexivity.
etransitivity.
apply hoge3.
reflexivity.
rewrite <- assoc.
reflexivity.
symmetry.
etransitivity.
rewrite <- assoc.
reflexivity.
symmetry.
etransitivity.
repeat rewrite <- assoc.
reflexivity.
reflexivity.
etransitivity.
apply H.
rewrite Hrhs2.
reflexivity.
repeat rewrite assoc.
reflexivity.
Qed.