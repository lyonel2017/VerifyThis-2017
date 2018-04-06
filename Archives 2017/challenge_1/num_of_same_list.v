(* ---------------------------------------------------------- *)
(* --- Lemma 'num_of_same_list'                           --- *)
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

Parameter L_num_of : (list Z) -> Z -> Z -> Z -> Z.

Hypothesis Q_num_of_pos_neq: forall (i_2 i_1 i : Z), forall (l : (list Z)),
  let x := (i_1%Z - 1%Z)%Z in (i%Z <> ((nth l x))) -> ((i_2 < i_1)%Z) ->
  ((((L_num_of l i_2%Z i_1%Z i%Z)) = ((L_num_of l i_2%Z x i%Z)))%Z).

Hypothesis Q_num_of_pos_eq: forall (i_2 i_1 i : Z), forall (l : (list Z)),
  let x := (i_1%Z - 1%Z)%Z in (i%Z = ((nth l x))) -> ((i_2 < i_1)%Z) ->
  ((((L_num_of l i_2%Z i_1%Z i%Z)) = (1 + ((L_num_of l i_2%Z x i%Z))))%Z).

Hypothesis Q_num_of_zero: forall (i_2 i_1 i : Z), forall (l : (list Z)),
  ((i_1 <= i_2)%Z) -> ((0 = ((L_num_of l i_2%Z i_1%Z i%Z)))%Z).

Require Import Axiomatic3.

Goal
  forall (i_2 i_1 i : Z),
  forall (l_1 l : (list Z)),
  ((P_same_list l_1 l i_2%Z i_1%Z)) ->
  ((((L_num_of l i_2%Z i_1%Z i%Z)) = ((L_num_of l_1 i_2%Z i_1%Z i%Z)))%Z).

Proof.
  intros. destruct (Z.le_gt_cases i_2 i_1).
  - revert i_1 H0 l l_1 H.
    apply (Zlt_lower_bound_ind (fun i_1 =>
      forall l l_1 : list int,
      P_same_list l_1 l i_2 i_1 ->
      L_num_of l i_2 i_1 i = L_num_of l_1 i_2 i_1 i));
    intros.
    + apply Zle_lt_or_eq in H0. destruct H0.
      * destruct (Z.eq_dec (nth l (x-1)) i).
        -- rewrite Q_num_of_pos_eq by omega.
           rewrite Q_num_of_pos_eq with (l:=l_1); try omega.
           ++ f_equal. apply H; [omega|].
              unfold P_same_list; intros. apply H1; omega.
           ++ rewrite <- e. symmetry. apply H1; omega.
        -- rewrite Q_num_of_pos_neq by omega.
           rewrite Q_num_of_pos_neq with (l:=l_1); try omega.
           ++ apply H; [omega|].
              unfold P_same_list; intros. apply H1; omega.
           ++ specialize (H1 (x-1)). rewrite H1; omega.
      * subst x. rewrite <- 2!Q_num_of_zero; omega.
  - rewrite <- 2!Q_num_of_zero; omega.
Qed.

