(* ---------------------------------------------------------- *)
(* --- Lemma 'list_of_array_length'                       --- *)
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

(* --- Axiomatic 'list_of_array' --- *)
Require Import Memory.
Require Import Vlist.

Parameter L_list_of_array : farray addr Z -> addr -> Z -> (list Z).

Require Import Compound.

Hypothesis Q_list_of_array_pos: forall (i : Z), forall (t : farray addr Z),
  forall (a : addr), let x := (i%Z - 1%Z)%Z in ((0 < i)%Z) ->
  (((L_list_of_array t a i%Z)) =
   ((concat ((L_list_of_array t a x))
      (cons (t.[ (shift_sint32 a x) ])%Z nil)))).

Hypothesis Q_list_of_array_zero: forall (t : farray addr Z),
  forall (a : addr), (nil) = ((L_list_of_array t a 0%Z)).

Goal
  forall (i : Z),
  forall (t : farray addr Z),
  forall (a : addr),
  ((0 <= i)%Z) ->
  ((i = ((length ((L_list_of_array t a i%Z)))))%Z).

Proof.
  intros i t a H. revert i H t a.
  apply (natlike_ind (fun i =>
    forall (t : farray addr int) (a : addr),
    i = length (L_list_of_array t a i)));
  intros.
  - rewrite <- Q_list_of_array_zero. reflexivity.
  - rewrite Q_list_of_array_pos by omega.
    rewrite Vlist.length_concat.
    rewrite Vlist.length_cons.
    rewrite Vlist.length_nil.
    replace (Z.succ x -1) with x by omega.
    rewrite <- H0. omega.
Qed.

