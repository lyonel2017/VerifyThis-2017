(* ---------------------------------------------------------- *)
(* --- Lemma 'update_nth_eq'                              --- *)
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

Hypothesis Q_update_nth_neq: forall (i_2 i_1 i : Z), forall (l : (list Z)),
  let x := ((length l))%Z in ((i <> i_2)%Z) -> ((0 <= i)%Z) ->
  ((0 <= i_2)%Z) -> ((i < x)%Z) -> ((i_2 < x)%Z) ->
  (((nth l i%Z)) = ((nth ((L_update l i_2%Z i_1%Z)) i%Z))).

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
  forall (i_1 i : Z),
  forall (l : (list Z)),
  ((0 <= i_1)%Z) ->
  ((i_1 < ((length l)))%Z) ->
  (i%Z = ((nth ((L_update l i_1%Z i%Z)) i_1%Z))).

Proof.
  intros n v l H. revert n H v l.
  apply (natlike_ind (fun n =>
    forall (v : int) (l : list int), n < length l ->
    v = nth (L_update l n v) n));
  intros.
  - rewrite Q_update_zero.
    destruct (Vlist.nth_cons 0 v (concat (L_tail l) nil)) as (HH & _).
    rewrite HH; omega.
  - rewrite Q_update_pos by omega. replace (Z.succ x - 1) with x by omega.
    destruct (Vlist.nth_cons (Z.succ x)
                             (nth l 0)
                             (concat (L_update (L_tail l) x v) nil))
      as (_ & HH). replace (Z.succ x - 1) with x in HH by omega.
    rewrite HH by omega.
    destruct (Vlist.nth_concat (L_update (L_tail l) x v) nil x) as (HH2 & _).
    assert (0 < length l) as Ha by omega.
    apply A_sub_list.Q_tail_length in Ha.
    rewrite <- Q_update_length in HH2 by omega.
    rewrite HH2 by omega.
    apply H0. omega.
Qed.

