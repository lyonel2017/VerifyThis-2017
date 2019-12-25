  intros n t2 t a H. revert n H t2 t a.
  apply (natlike_ind (fun n => forall (t2 t : farray addr int) (a : addr),
    P_same_elements_list (L_list_of_array t a n) (L_list_of_array t2 a n) ->
    P_same_elements t2 t a a 0 n)); intros.
  - apply Q_refl. unfold P_same_array; intros; omega.
  - destruct H1 as (H1 & H2).
    rewrite 2!A_list_of_array.Q_list_of_array_pos with (i:=Z.succ x)
      in H2 by omega.
    pose proof A_num_of.Q_num_of_split as Ha.
    setoid_rewrite Vlist.rw_nil_concat_right in Ha.
    setoid_rewrite Ha in H2.
    pose proof (H2 (t2 .[ shift_sint32 a (Z.succ x - 1)])) as H3.
    destruct (A_num_of.Q_num_of_cons (t2 .[ shift_sint32 a (Z.succ x - 1)])
                                     (t2 .[ shift_sint32 a (Z.succ x - 1)]) nil)
      as (HH & _).
    rewrite Vlist.rw_nil_concat_left in HH.
    rewrite HH in H3 by reflexivity.
    clear HH.
    destruct (Z.le_lt L_num_of
    destruct (A_num_of.Q_num_of_cons (t .[ shift_sint32 a (Z.succ x - 1)])
                                     (t2 .[ shift_sint32 a (Z.succ x - 1)]) nil)
      as (HH1 & HH2).
    
    rewrite Q_tail_nth
(* auto with zarith. *)
Qed.


