(* ---------------------------------------------------------- *)
(* --- Lemma 'update_length'                              --- *)
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

(* --- Axiomatic 'update'   --- *)
Require Import Vlist.

Parameter L_update : (list Z) -> Z -> Z -> (list Z).

Require Import A_sub_list.

Hypothesis Q_update_pos: forall (i_1 i : Z), forall (l : (list Z)),
  ((0 < i_1)%Z) ->
  (((L_update l i_1%Z i%Z)) =
   ((cons ((nth l 0%Z))
      (concat ((L_update ((L_tail l)) (i_1%Z - 1%Z)%Z i%Z)) nil)))).

Hypothesis Q_update_zero: forall (i : Z), forall (l : (list Z)),
  ((L_update l 0%Z i%Z)) = ((cons i%Z (concat ((L_tail l)) nil))).

Goal
  forall (i_1 i : Z),
  forall (l : (list Z)),
  let x := ((length l))%Z in
  ((0 <= i_1)%Z) ->
  ((i_1 < x)%Z) ->
  ((x = ((length ((L_update l i_1%Z i%Z)))))%Z).

Proof.
  intros n k l x H. unfold x. clear x. revert n H k l.
  apply (natlike_ind (fun n =>
    forall k l, n < length l -> length l = length (L_update l n k)));
  intros.
  - rewrite Q_update_zero.
    rewrite Vlist.length_cons, Vlist.length_concat, Vlist.length_nil.
    pose proof (A_sub_list.Q_tail_length l H).
    omega.
  - rewrite Q_update_pos by omega.
    replace (Z.succ x - 1) with x by omega.
    rewrite Vlist.length_cons, Vlist.length_concat, Vlist.length_nil.
    assert (0 < length l) by omega.
    pose proof (A_sub_list.Q_tail_length l H2).
    rewrite <- H0; omega.
Qed.

