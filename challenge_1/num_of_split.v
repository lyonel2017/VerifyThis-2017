(* ---------------------------------------------------------- *)
(* --- Lemma 'num_of_split'                               --- *)
(* ---------------------------------------------------------- *)
Require Import ZArith.
Require Import Reals.
Require Import BuiltIn.
Require Import int.Int.
Require Import int.Abs.
Require Import int.ComputerDivision.
Require Import real.Real.
Require Import real.RealInfix.
Require Import real.FromInt.
Require Import map.Map.
Require Import Qedlib.
Require Import Qed.

(* --- Axiomatic 'num_of'   --- *)
Require Import Vlist.

Parameter L_num_of : (list Z) -> Z -> Z.

Hypothesis Q_num_of_pos_neq: forall (i_1 i : Z), forall (l : (list Z)),
  ((i <> i_1)%Z) ->
  ((((L_num_of l i%Z)) = ((L_num_of ((cons i_1%Z (concat l nil))) i%Z)))%Z).

Hypothesis Q_num_of_pos_eq: forall (i : Z), forall (l : (list Z)),
  (((L_num_of ((cons i%Z (concat l nil))) i%Z)) = (1 + ((L_num_of l i%Z))))%Z.

Hypothesis Q_num_of_zero: forall (i : Z), (0 = ((L_num_of (nil) i%Z)))%Z.

Require Import Axiomatic2.

(* --- Additional Libraries --- *)
Require Import MyList.

(* -------------------------------------------------- *)

Goal
  forall (i : Z),
  forall (l_1 l : (list Z)),
  (((L_num_of ((concat l_1 (concat l nil))) i%Z))
   = (((L_num_of l i%Z)) + ((L_num_of l_1 i%Z))))%Z.

Proof.
  intros. induction l_1 using list_ind.
  - rewrite rw_nil_concat_left, rw_nil_concat_right.
    rewrite <- Q_num_of_zero. omega.
  - rewrite rw_cons_concat.
    destruct (Z.eq_dec i h).
    + subst h.
      pose proof Q_num_of_pos_eq.
      setoid_rewrite rw_nil_concat_right in H.
      rewrite 2!H.
      omega.
    + pose proof Q_num_of_pos_neq.
      setoid_rewrite rw_nil_concat_right in H.
      rewrite <- 2!H; assumption.
Qed.

