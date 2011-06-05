Require Import ZArith Omega ssreflect.

Open Scope Z_scope.

Section BinaryDivision.


Fixpoint div_bin (n m:positive) : Z*Z :=
  match n with
    | 1%positive => match m with 1%positive => (1,0) | _ => (0,1) end
    | xO n' =>
      let (q',r') := div_bin n' m in 
      match Z_lt_ge_dec (2*r') (Zpos m) with
      | left Hlt => (2*q',2*r')
      | right Hge => (2*q' + 1, 2*r' - (Zpos m))
      end
    | xI n' =>
      let (q',r'):=div_bin n' m in
      match Z_lt_ge_dec (2*r'+1) (Zpos m) with
      | left Hlt => (2*q', 2*r' + 1)
      | right Hge => (2*q' + 1, (2*r' + 1) - (Zpos m))
      end
  end.

Theorem rem_1_1_interval: 0 <= 0 < 1.
omega. Qed.

Theorem rem_1_even_interval m: 0<=1<Zpos (xO m).
split.
  auto with zarith.
  by compute.
Qed.

Theorem rem_1_odd_interval 
: forall m:positive, 0 <= 1 < Zpos (xI m).
by split;[auto with zarith|compute].
Qed.

Theorem rem_even_ge_interval 
: forall m r:Z, 0<=r<m -> 2*r >= m -> 0 <= 2*r - m < m.
 intros; omega.
Qed.

Theorem rem_even_lt_interval 
: forall m r:Z, 0<=r<m -> 2*r < m -> 0 <= 2*r < m.
intros;omega.
Qed.

Theorem rem_odd_ge_interval 
: forall m r:Z, 0<=r<m -> 2*r + 1 >= m -> 2*r+1 - m < m.
intros;omega.
Qed.

Theorem rem_odd_lt_interval 
: forall m r:Z, 0<=r<m -> 2*r+1 < m -> 0<=2*r+1<m.
intros; omega.
Qed.

Hint Resolve rem_odd_ge_interval rem_even_ge_interval
     rem_odd_lt_interval rem_odd_ge_interval rem_1_odd_interval
     rem_1_even_interval rem_1_1_interval.

Ltac div_bin_tac arg1 arg2 :=
  elim arg1;
   [ intros p; lazy beta iota delta [div_bin]; fold div_bin;
       case (div_bin p arg2); unfold snd; intros q' r' Hrec;
       case (Z_lt_ge_dec (2*r'+1) (Zpos arg2)); intros H
   | intros p; lazy beta iota delta [div_bin]; fold div_bin;
       case (div_bin p arg2); unfold snd; intros q' r' Hrec;
       case (Z_lt_ge_dec (2*r') (Zpos arg2)); intros H
   | case arg2; lazy beta iota delta [div_bin]; intros].

Theorem div_bin_rem_lt 
: forall n m:positive, 0 <= snd (div_bin n m) < Zpos m.
  info intros n m; div_bin_tac n m; unfold snd; auto; omega.
Qed.

Theorem div_bin_eq 
: forall n m:positive, Zpos n = fst (div_bin n m)*Zpos m + snd (div_bin n m).
info intros n m; div_bin_tac n m; unfold fst, snd in *|-*;
(try rewrite Zpos_xI;try rewrite Zpos_xO);try rewrite Hrec;
ring.
Qed.

End BinaryDivision.

Section WellSpecifiedBinaryDivision.

Inductive div_data (n m:positive) : Set :=
  div_data_def (q r:Z) : Zpos n = q*(Zpos m)+r -> 0 <= r < Zpos m -> div_data n m.

Definition div_bin2 n m : div_data n m.
elim n.
  intros n' [q r H_eq Hint].
  case (Z_lt_ge_dec (2*r+1) (Zpos m)).
    intros.
    exists (2*q) (2*r+1).
    rewrite Zpos_xI.
    rewrite H_eq.
    ring.
    omega.
    
    intros.
    exists (2*q+1) (2*r + 1 - (Zpos m)).
    rewrite Zpos_xI.
    rewrite H_eq.
    ring.
    omega.
Abort.

End WellSpecifiedBinaryDivision.