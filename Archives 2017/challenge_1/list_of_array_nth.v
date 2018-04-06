(* ---------------------------------------------------------- *)
(* --- Lemma 'list_of_array_nth'                          --- *)
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

Hypothesis Q_list_of_array_length: forall (i : Z),
  forall (t : farray addr Z), forall (a : addr), ((0 <= i)%Z) ->
  ((i = ((length ((L_list_of_array t a i%Z)))))%Z).

Require Import Compound.

Hypothesis Q_list_of_array_pos: forall (i : Z), forall (t : farray addr Z),
  forall (a : addr), let x := (i%Z - 1%Z)%Z in ((0 < i)%Z) ->
  (((L_list_of_array t a i%Z)) =
   ((concat ((L_list_of_array t a x))
      (cons (t.[ (shift_sint32 a x) ])%Z nil)))).

Hypothesis Q_list_of_array_zero: forall (t : farray addr Z),
  forall (a : addr), (nil) = ((L_list_of_array t a 0%Z)).

Goal
  forall (i_1 i : Z),
  forall (t : farray addr Z),
  forall (a : addr),
  ((0 <= i)%Z) ->
  ((i < i_1)%Z) ->
  (((nth ((L_list_of_array t a i_1%Z)) i%Z)) =
   (t.[ (shift_sint32 a i%Z) ])%Z).

Proof.
  intros n k. intros.
  assert (0 <= n) as Ha by omega.
  revert n Ha k t a H H0.
  apply (natlike_ind (fun n =>
    forall (k : int) (t : farray addr int) (a : addr),
    0 <= k -> k < n -> nth (L_list_of_array t a n) k = t .[ shift_sint32 a k]));
  intros.
  - omega.
  - assert (k = x \/ k < x) as Ha by omega.
    destruct Ha.
    + subst x. rewrite Q_list_of_array_pos by omega.
      replace (Z.succ k - 1) with k by omega.
      destruct (Vlist.nth_concat
                 (L_list_of_array t a k)
                 (cons (t .[ shift_sint32 a k]) nil)
                 k) as (_ & HH).
      rewrite <- Q_list_of_array_length in HH by omega.
      rewrite HH by omega.
      replace (k - k) with 0 by omega.
      destruct (Vlist.nth_cons 0 (t .[ shift_sint32 a k]) nil)
        as (HH2 & _).
      apply HH2. reflexivity.
    + rewrite Q_list_of_array_pos by omega.
      replace (Z.succ x - 1) with x by omega.
      destruct (Vlist.nth_concat
                 (L_list_of_array t a x)
                 (cons (t .[ shift_sint32 a x]) nil)
                 k) as (HH & _).
      rewrite <- Q_list_of_array_length in HH by omega.
      rewrite HH by omega. apply H0; omega.
Qed.

