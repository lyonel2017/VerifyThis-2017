(* ---------------------------------------------------------- *)
(* --- Lemma 'swap_list_same_elements_alpha'              --- *)
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

(* --- Global Definitions (continued #4) --- *)
Require Import Vlist.

Definition P_swap_list (l1_0 : (list Z)) (l2_0 : (list Z)) (i : Z) (j : Z)
    : Prop :=
    let x := ((length l1_0))%Z in ((x = ((length l2_0)))%Z) /\
      (((nth l1_0 i%Z)) = ((nth l2_0 j%Z))) /\
      (((nth l1_0 j%Z)) = ((nth l2_0 i%Z))) /\ ((0 <= i)%Z) /\ ((i < j)%Z) /\
      ((j < x)%Z) /\
      (forall (i_1 : Z), ((i <> i_1)%Z) -> ((j <> i_1)%Z) ->
       ((0 <= i_1)%Z) -> ((i_1 < x)%Z) ->
       (((nth l1_0 i_1%Z)) = ((nth l2_0 i_1%Z)))).

Require Import A_sub_list.

Hypothesis Q_swap_split2: forall (i_1 i : Z), forall (l_1 l : (list Z)),
  let a := (L_sub_list l_1 0%Z i_1%Z) in
  let a_1 := (cons ((nth l_1 i%Z)) nil) in
  let a_2 := (L_sub_list l_1 (1%Z + i_1%Z)%Z i%Z) in
  let a_3 := (cons ((nth l_1 i_1%Z)) nil) in
  let a_4 := (L_sub_list l_1 (1%Z + i%Z)%Z ((length l_1))%Z) in
  ((P_swap_list l_1 l i_1%Z i%Z)) ->
  ((l =
    ((concat a
       (cons ((nth l_1 i%Z))
         (concat a_2 (cons ((nth l_1 i_1%Z)) (concat a_4 nil))))))) /\
   (l_1 =
    ((concat a
       (cons ((nth l_1 i_1%Z))
         (concat a_2 (cons ((nth l_1 i%Z)) (concat a_4 nil)))))))).

Hypothesis Q_swap_split: forall (i_1 i : Z), forall (l_1 l : (list Z)),
  ((P_swap_list l_1 l i_1%Z i%Z)) ->
  (l_1 =
   ((concat ((L_sub_list l_1 0%Z i_1%Z))
      (cons ((nth l_1 i_1%Z))
        (concat ((L_sub_list l_1 (1%Z + i_1%Z)%Z i%Z))
          (cons ((nth l_1 i%Z))
            (concat ((L_sub_list l_1 (1%Z + i%Z)%Z ((length l_1))%Z)) nil))))))).

Hypothesis Q_swap_sym: forall (i_1 i : Z), forall (l_1 l : (list Z)),
  ((P_swap_list l_1 l i_1%Z i%Z)) -> ((P_swap_list l l_1 i_1%Z i%Z)).

Require Import A_num_of.

Definition P_same_elements_list (l1_0 : (list Z)) (l2_0 : (list Z)) : Prop :=
    ((((length l1_0)) = ((length l2_0)))%Z) /\
      (forall (i : Z), (((L_num_of l1_0 i%Z)) = ((L_num_of l2_0 i%Z)))%Z).

Hypothesis Q_same_elements_list_trans: forall (l_2 l_1 l : (list Z)),
  ((P_same_elements_list l_1 l)) -> ((P_same_elements_list l_2 l_1)) ->
  ((P_same_elements_list l_2 l)).

Hypothesis Q_same_elements_list_refl: forall (l : (list Z)),
  (P_same_elements_list l l).

Goal
  forall (i_1 i : Z),
  forall (l_2 l_1 l : (list Z)),
  let a := (cons i_1%Z nil) in
  let a_1 := (cons i%Z nil) in
  (P_same_elements_list
    ((concat l_2 (cons i_1%Z (concat l_1 (cons i%Z (concat l nil))))))
    ((concat l_2 (cons i%Z (concat l_1 (cons i_1%Z (concat l nil))))))).

Proof.
 assert (forall l i j, 0 <= i -> i <= j -> j <= length l -> length (L_sub_list l i j) = j - i) as Ha.
  { intros. pose proof (A_sub_list.Q_sub_list_length i j l H0 H H1).
    omega.
  }
  assert (forall l1 l2 v,
    L_num_of (concat l1 l2) v = L_num_of l1 v + L_num_of l2 v) as Hb.
  { intros. pose proof A_num_of.Q_num_of_split.
    setoid_rewrite rw_nil_concat_right in H. rewrite H. omega.
  }
  assert (forall x l v,
    L_num_of (cons x l) v = if x =? v then 1+ L_num_of l v else L_num_of l v) as Hc.
  { intros. destruct (A_num_of.Q_num_of_cons x v l).
    destruct (Z.eq_dec v x).
    subst x. rewrite (Z.eqb_refl v). rewrite Vlist.rw_nil_concat_right in H.
    auto.
    rewrite Vlist.rw_nil_concat_right in H0.
    apply Z.eqb_neq in n as n1. rewrite Z.eqb_sym in n1. rewrite n1.
    symmetry.
    auto.
  }
  intros. unfold P_same_elements_list; intros.
  split.
  - repeat (rewrite Vlist.length_concat || rewrite Vlist.length_cons || rewrite Vlist.length_nil).
    omega.
  - intros.
    rewrite !Hb. rewrite !Hc. rewrite !Hb. rewrite !Hc. rewrite !Hb.
    destruct (i_1 =? i0), (i =? i0); omega.
Qed.


