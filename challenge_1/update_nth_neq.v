(* ---------------------------------------------------------- *)
(* --- Lemma 'update_nth_neq'                             --- *)
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

Hypothesis Q_update_length: forall (i_1 i : Z), forall (l : (list Z)),
  let x := ((length l))%Z in ((0 <= i_1)%Z) -> ((i_1 < x)%Z) ->
  ((x = ((length ((L_update l i_1%Z i%Z)))))%Z).

Require Import A_sub_list.

Hypothesis Q_update_pos: forall (i_1 i : Z), forall (l : (list Z)),
  ((0 < i_1)%Z) ->
  (((L_update l i_1%Z i%Z)) =
   ((cons ((nth l 0%Z))
      (concat ((L_update ((L_tail l)) (i_1%Z - 1%Z)%Z i%Z)) nil)))).

Hypothesis Q_update_zero: forall (i : Z), forall (l : (list Z)),
  ((L_update l 0%Z i%Z)) = ((cons i%Z (concat ((L_tail l)) nil))).

Goal
  forall (i_2 i_1 i : Z),
  forall (l : (list Z)),
  let x := ((length l))%Z in
  ((i <> i_2)%Z) ->
  ((0 <= i)%Z) ->
  ((0 <= i_2)%Z) ->
  ((i < x)%Z) ->
  ((i_2 < x)%Z) ->
  (((nth l i%Z)) = ((nth ((L_update l i_2%Z i_1%Z)) i%Z))).

Proof.
  intros n v k l x H H0 H1. unfold x. clear x.
  revert n H1 k l H H0.
  apply (natlike_ind (fun n =>
    forall k l, k <> n -> 0 <= k -> k < length l -> n < length l ->
    nth l k = nth (L_update l n v) k)); intros.
  - rewrite Q_update_zero.
    destruct (Vlist.nth_cons k v (concat (L_tail l) nil)) as (_ & HH).
    rewrite HH by omega.
    destruct (Vlist.nth_concat (L_tail l) nil (k-1)) as (HH2 & _).
    replace (length (L_tail l)) with (length l - 1) in HH2
      by (rewrite A_sub_list.Q_tail_length; omega).
    rewrite HH2 by omega.
    rewrite A_sub_list.Q_tail_nth by omega.
    replace (1+(k-1)) with k by omega. reflexivity.
  - rewrite Q_update_pos by omega.
    assert (k = 0 \/ 0 < k) as Ha by omega.
    destruct Ha as [Ha|Ha].
    + subst k.
      replace (Z.succ x - 1) with x by omega.
      destruct (Vlist.nth_cons 0 (nth l 0)
                                 (concat (L_update (L_tail l) x v) nil))
        as (HH & _).
      rewrite HH; reflexivity.
    + replace (Z.succ x -1) with x by omega.
      destruct (Vlist.nth_cons k (nth l 0)
                                 (concat (L_update (L_tail l) x v) nil))
        as (_ & HH).
      rewrite HH by omega.
      destruct (Vlist.nth_concat
                 (L_update (L_tail l) x v)
                 nil
                 (k-1)) as (HH2 & _).
      assert (0 < length l) as Hb by omega.
      apply A_sub_list.Q_tail_length in Hb.
      rewrite <- Q_update_length in HH2 by omega.
      rewrite HH2 by omega.
      rewrite <- H0 by omega.
      rewrite A_sub_list.Q_tail_nth by omega.
      replace (1+(k-1)) with k by omega.
      reflexivity.
Qed.


