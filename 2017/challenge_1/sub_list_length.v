(* ---------------------------------------------------------- *)
(* --- Lemma 'sub_list_length'                            --- *)
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

(* --- Axiomatic 'sub_list' --- *)
Require Import Vlist.

Parameter L_sub_list : (list Z) -> Z -> Z -> (list Z).

Hypothesis Q_sub_list_pos: forall (i_1 i : Z), forall (l : (list Z)),
  let x := (i%Z - 1%Z)%Z in ((i_1 < i)%Z) ->
  (((L_sub_list l i_1%Z i%Z)) =
   ((concat ((L_sub_list l i_1%Z x)) (cons ((nth l x)) nil)))).

Hypothesis Q_sub_list_zero: forall (i_1 i : Z), forall (l : (list Z)),
  ((i <= i_1)%Z) -> ((nil) = ((L_sub_list l i_1%Z i%Z))).

Goal
  forall (i_1 i : Z),
  forall (l : (list Z)),
  ((i_1 <= i)%Z) ->
  ((0 <= i_1)%Z) ->
  ((i <= ((length l)))%Z) ->
  ((i = (i_1 + ((length ((L_sub_list l i_1%Z i%Z))))))%Z).

Proof.
  intros.
  assert (0 <= i) as Ha by omega.
  revert i Ha i_1 l H H0 H1.
  apply (natlike_ind (fun i =>
    forall (i_1 : int) (l : list int),
    i_1 <= i -> 0 <= i_1 -> i <= length l ->
    i = i_1 + length (L_sub_list l i_1 i)));
  intros.
  - assert (i_1 = 0) by omega. subst i_1.
    rewrite <- Q_sub_list_zero by omega.
    reflexivity.
  - assert (i_1 = Z.succ x \/ i_1 <= x) as Ha by omega.
    destruct Ha as [Ha|Ha].
    + subst i_1. rewrite <- Q_sub_list_zero by omega.
      rewrite Vlist.length_nil. omega.
    + rewrite Q_sub_list_pos by omega.
      replace (Z.succ x - 1) with x by omega.
      rewrite Vlist.length_concat, Vlist.length_cons, Vlist.length_nil.
      ring_simplify. f_equal.
      apply H0; omega.
Qed.


