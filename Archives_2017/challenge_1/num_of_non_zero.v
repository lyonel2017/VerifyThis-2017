(* ---------------------------------------------------------- *)
(* --- Lemma 'num_of_non_zero'                            --- *)
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

Hypothesis Q_num_of_split: forall (i : Z), forall (l_1 l : (list Z)),
  (((L_num_of ((concat l_1 (concat l nil))) i%Z))
   = (((L_num_of l i%Z)) + ((L_num_of l_1 i%Z))))%Z.

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
  forall (l : (list Z)),
  ((0 < ((L_num_of l i%Z)))%Z) ->
  (exists i_1 : Z, (i%Z = ((nth l i_1%Z))) /\ ((0 <= i_1)%Z) /\
   ((i_1 < ((length l)))%Z)).

Proof.
  intros. induction l using list_ind.
  - rewrite <- Q_num_of_zero in H. omega.
  - destruct (Z.eq_dec i h).
    + subst h.
      exists 0.
      split.
      * rewrite cons_nth1. reflexivity.
      * rewrite Vlist.length_cons.
        pose proof (Vlist.length_pos l). omega.
    + pose proof Q_num_of_pos_neq.
      setoid_rewrite rw_nil_concat_right in H0.
      rewrite <- H0 in H by assumption.
      apply IHl in H. destruct H as (i_1 & H1 & H2).
      exists (1 + i_1). split.
      * rewrite cons_nth2 by omega. replace (1+i_1-1) with i_1 by omega.
        assumption.
      * rewrite Vlist.length_cons. omega.
Qed.

