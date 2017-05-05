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

Hypothesis Q_num_of_cons: forall (i_1 i : Z), forall (l : (list Z)),
  let x := ((L_num_of ((cons i_1%Z (concat l nil))) i%Z))%Z in
  let x_1 := ((L_num_of l i%Z))%Z in itep ((i = i_1)%Z) ((x = (1 + x_1))%Z)
  ((x_1 = x)%Z).

Hypothesis Q_num_of_split: forall (i : Z), forall (l_1 l : (list Z)),
  (((L_num_of ((concat l_1 (concat l nil))) i%Z))
   = (((L_num_of l i%Z)) + ((L_num_of l_1 i%Z))))%Z.

Require Import A_sub_list.

Hypothesis Q_num_of_pos_neq: forall (i : Z), forall (l : (list Z)),
  (i%Z <> ((nth l 0%Z))) -> ((0 < ((length l)))%Z) ->
  ((((L_num_of l i%Z)) = ((L_num_of ((L_tail l)) i%Z)))%Z).

Hypothesis Q_num_of_pos_eq: forall (i : Z), forall (l : (list Z)),
  (i%Z = ((nth l 0%Z))) -> ((0 < ((length l)))%Z) ->
  ((((L_num_of l i%Z)) = (1 + ((L_num_of ((L_tail l)) i%Z))))%Z).

Hypothesis Q_num_of_zero: forall (i : Z), (0 = ((L_num_of (nil) i%Z)))%Z.

Goal
  forall (i : Z),
  forall (l : (list Z)),
  ((0 < ((L_num_of l i%Z)))%Z) ->
  (exists i_1 : Z, (i%Z = ((nth l i_1%Z))) /\ ((0 <= i_1)%Z) /\
   ((i_1 < ((length l)))%Z)).

Proof.
  intros. induction l.
  - fold (@nil int _) in *.
    rewrite <- Q_num_of_zero in H. inversion H.
  - fold (cons a l) in *.
    destruct (Z.eq_dec i a).
    + exists 0. split. destruct (Q_num_of_cons a i l) as (HH & _).
      rewrite rw_nil_concat_right in HH.
      apply HH in e. rewrite e in H.
      
      
    rewrite Q_num_of_pos_eq
(* auto with zarith. *)
Qed.


