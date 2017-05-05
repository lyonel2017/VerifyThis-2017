(* ---------------------------------------------------------- *)
(* --- Lemma 'sub_list_nth'                               --- *)
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

Hypothesis Q_sub_list_length: forall (i_1 i : Z), forall (l : (list Z)),
  ((i_1 <= i)%Z) -> ((0 <= i_1)%Z) -> ((i <= ((length l)))%Z) ->
  ((i = (i_1 + ((length ((L_sub_list l i_1%Z i%Z))))))%Z).

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
  (forall (i_2 : Z), let x := (i_2%Z + i_1%Z)%Z in ((0 <= i_2)%Z) ->
   ((x < i)%Z) -> (((nth l x)) = ((nth ((L_sub_list l i_1%Z i%Z)) i_2%Z)))).

Proof.
  intros begin en l H Hbeg_en Hen_len k x. unfold x. clear x.
  revert en H l Hen_len k.
  apply (Zlt_lower_bound_ind (fun en =>
    forall l : list int,
    en <= length l -> forall k : int, 0 <= k -> k + begin < en ->
    nth l (k + begin) = nth (L_sub_list l begin en) k));
  intros.
  assert (k+begin + 1 = x \/ k+begin < x - 1) as Ha by omega.
  destruct Ha as [Ha|Ha].
  - subst x.
    rewrite Q_sub_list_pos by omega.
    replace (k+begin + 1 -1) with (k+begin) by omega.
    destruct (Vlist.nth_concat
               (L_sub_list l begin (k+begin))
               (cons (nth l (k+begin)) nil)
               k) as (_ & HH).
    assert (length (L_sub_list l begin (k+begin)) = k) as Hb.
    { assert (k + begin = begin + length (L_sub_list l begin (k + begin))).
      { apply Q_sub_list_length; omega. }
      omega.
    }
    rewrite Hb in HH.
    rewrite HH by omega.
    replace (k-k) with 0 by omega.
    destruct (Vlist.nth_cons 0 (nth l (k+begin)) nil) as (HH2 & _).
    symmetry. apply HH2; reflexivity.
  - rewrite Q_sub_list_pos by omega.
    destruct (Vlist.nth_concat
               (L_sub_list l begin (x - 1))
               (cons (nth l (x - 1)) nil)
               k) as (HH & _).
    assert (length (L_sub_list l begin (x - 1)) = x - 1 - begin) as Hb.
    { assert (x - 1 = begin + length (L_sub_list l begin (x - 1))).
      { apply Q_sub_list_length; omega. }
      omega.
    }
    rewrite Hb in HH.
    rewrite HH by omega.
    apply H; omega.
Qed.


