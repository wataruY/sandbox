Require Import header.
Require Import List Permutation Sorted.
Require Import Omega.

Set Implicit Arguments.
Generalizable Variable A R.

Section Halve.
  Variable A:Type.
  Fixpoint halve_weak0 (xs:list A) : list A * list A :=
    match xs with
      | nil => (nil,nil)
      | a :: l => let (ys,zs) := halve_weak1 l
                  in (a::ys,zs)
    end
  with halve_weak1 (xs:list A) : list A * list A :=
       match xs with
         | nil => (nil,nil)
         | a :: l => let (ys,zs) := halve_weak0 l
                     in (ys,a::zs)
       end.
  Definition halve_weak := halve_weak0.
  Definition app' : (list A * list A) -> list A.
  intros [xs ys];
  exact (xs++ys).
  Defined.
  
  Theorem halve_perm xs : Permutation (app' (halve_weak0 xs)) (app' (halve_weak1 xs)).
  induction xs.
  constructor.
  simpl.
  destruct (halve_weak1 xs); destruct (halve_weak0 xs); simpl in *.
  apply Permutation_cons_app.
  symmetry.
  assumption.
  Qed.
  Let swap {B C:Type} : B*C->C*B.
  tauto.
  Defined.

  Theorem halve0_res_comm xs : halve_weak0 xs = swap (halve_weak1 xs).
  induction xs.
  reflexivity.
  simpl in *.
  destruct (halve_weak1 xs); destruct (halve_weak0 xs).
  simpl in *.
  injection IHxs; intros; subst; reflexivity.
  Qed.
  Theorem swap_swap {B C:Type} (xs:B*C) : swap (swap xs) = xs.
  destruct xs; reflexivity.
  Qed.
  Theorem halve1_res_comm xs : halve_weak1 xs = swap (halve_weak0 xs).
  rewrite halve0_res_comm.
  rewrite swap_swap.
  reflexivity.
  Qed.
  Lemma swap_move {B C} (x:B*C) y : x = swap y <-> swap x = y.
  unfold swap; destruct x; destruct y; simpl.
  split; intro H; injection H; intros; subst; reflexivity.
  Qed.

  Theorem halve_weak_perm xs :
    let (ys,zs) := halve_weak xs in Permutation xs (ys++zs).
  induction xs.
  constructor.
  simpl.
  remember (halve_weak1 xs) as ws.
  unfold halve_weak in *.
  remember (halve_weak0 xs) as vs.
  destruct ws; destruct vs.
  simpl in *; subst.
  constructor.
  rewrite IHxs.
  clear IHxs.
  rewrite halve0_res_comm in Heqvs.
  apply swap_move in Heqvs.
  simpl in *.
  assert ((l,l0) = (l2,l1)); first congruence.
  injection H; intros; subst.
  apply Permutation_app_comm.
  Qed.

  Inductive MostOneElemL : list A -> list A -> Prop :=
  | LOE0 : MostOneElemL nil nil
  | LOE1 a : MostOneElemL (a::nil) nil
  | LOE2 a b xs ys : MostOneElemL xs ys -> MostOneElemL (a::xs) (b::ys).

  Theorem LOE_length xs ys : MostOneElemL xs ys <-> let (n,m) := (length xs,length ys)
                                                   in n = S m \/ n = m.
  split; intro H.
  induction H.
  by auto with arith.
  simpl in *.
  by auto with arith.
  simpl.
  destruct IHMostOneElemL.
  left.
  auto with arith.
  right; congruence.

  destruct or H.
  revert dependent xs.
  induction ys.
  simpl.
  induction xs.
  constructor.
  simpl.
  destruct xs.
  constructor.
  discriminate.
  simpl.
  intro xs.
  revert dependent ys.
  induction xs.
  simpl.
  discriminate.
  simpl.
  constructor.
  apply IHys.
  apply eq_add_S in H.
  assumption.

  revert dependent ys.
  induction xs.
  simpl.
  destruct ys.
  constructor.
  discriminate.
  simpl.
  intro ys.
  revert dependent a; revert dependent xs.
  induction ys.
  simpl.
  discriminate.
  simpl.
  constructor.
  apply eq_add_S in H.
  apply IHxs; assumption.
  Qed.
  
  Theorem halve_swap xs ys zs vs ws : halve_weak0 xs =(ys,zs) -> halve_weak1 xs = (vs,ws) ->
                                      ys = ws /\ zs = vs.
  intros H0 H1.
  rewrite halve0_res_comm in H0.
  rewrite <- swap_move in H0.
  simpl in *.
  assert (H:(vs,ws) = (zs,ys)); first congruence.
  injection H; intros; split; congruence.
  Qed.

  Theorem halve_weak0_length xs :
    (let (ys,zs) := halve_weak0 xs in MostOneElemL ys zs).

  induction xs.
   lazy beta iota zeta delta; auto with arith.
   do 2 constructor.
   
   remember (halve_weak0 xs) as ws.
   remember (halve_weak1 xs) as vs.
   destruct ws; destruct vs.
   symmetry  in Heqws, Heqvs.
   edestruct (halve_swap xs).
    eassumption.
    
    eassumption.
    
    subst.
    rewrite halve1_res_comm in Heqvs.
    rewrite <- swap_move in Heqvs.
    simpl in Heqws |- *.
    rewrite halve1_res_comm .
    destruct (halve_weak0 xs); simpl in *.
    injection Heqws; intros; subst.
    revert a.
    clear_except IHxs.
    induction IHxs.
     constructor.
     
     constructor.
     constructor.
     
     constructor.
     apply IHIHxs.
  Qed.

  Theorem halve_weak1_length xs :
    (let (ys,zs) := halve_weak1 xs in MostOneElemL zs ys).
  assert (H:=halve_weak0_length xs).
  rewrite halve1_res_comm.
  destruct (halve_weak0 xs).
  simpl; assumption.
  Qed.
