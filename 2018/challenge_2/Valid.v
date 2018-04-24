Require Import List.
Import ListNotations.
Require Import Arith.
Import Bool.
Require Import set.
Require Import sets.
Require Import Omega.
Require Import Setoid.

Module coq.
(* red = true; black = false *)
Fixpoint valid_aux acc (l : list bool) :=
  match l with
  | [] => (acc =? 0) || (3 <=? acc)
  | x :: l => if x then valid_aux (acc+1) l else ((acc =? 0) || (3 <=? acc)) && valid_aux 0 l
  end.

Definition valid l := valid_aux 0 l.

Instance list_bool_dec : DecidableType (list bool).
Proof.
  split.
  apply list_eq_dec.
  apply bool_dec.
Defined.

Fixpoint enumerate_all n : set (list bool) :=
  match n with
  | 0 => set_add [] empty_set
  | S n => let s := enumerate_all n in
             (set_map (fun l => true::l) s) \cup
             (set_map (fun l => false::l) s)
  end.

Functional Scheme enumerate_all_ind := Induction for enumerate_all Sort Prop.

Lemma enumerate_all_length_n : forall n l, set_In l (enumerate_all n) ->
  List.length l = n.
Proof.
  intros n. functional induction (enumerate_all n).
  - intros. apply set_singleton_In in H. subst. reflexivity.
  - intros. apply set_union_In in H. destruct H.
    + apply set_map_In in H. destruct H as (a & H & H0).
      subst l. simpl. apply f_equal. auto.
    + apply set_map_In in H. destruct H as (a & H & H0).
      subst l. simpl. apply f_equal. auto.
Qed.

Lemma length_n_enumerate_all :
  forall n l, List.length l = n -> set_In l (enumerate_all n).
Proof.
  intros n. induction n; intros.
  - simpl. left. destruct l; [reflexivity|discriminate].
  - destruct l; [discriminate|]. simpl in H. simpl.
    apply set_union_In. destruct b.
    + left. apply set_map_In. exists l.
      split; [|reflexivity]. auto.
    + right. apply set_map_In. exists l.
      split; [|reflexivity]. auto.
Qed.

Lemma enumerate_all_length_n_iff : forall n l,
  l \in (enumerate_all n) <-> List.length l = n.
Proof.
  split.
  - apply enumerate_all_length_n.
  - apply length_n_enumerate_all.
Qed.

Definition filter n := set_filter valid (enumerate_all n).

Fixpoint prefix_red (s : list bool) :=
  match s with
  | [] => []
  | b::s' => if b then true::prefix_red s' else []
  end.

Lemma prefix_red_length : forall s,
  List.length (prefix_red s) <= List.length s.
Proof.
  intros. induction s.
  - simpl. reflexivity.
  - simpl. destruct a. simpl. apply le_n_S. assumption.
    apply le_0_n.
Qed.

Lemma prefix_red_only_red : forall s,
  prefix_red s = repeat true (List.length (prefix_red s)).
Proof.
  intros. induction s.
  - reflexivity.
  - simpl. destruct a.
    + simpl. rewrite IHs at 1. reflexivity.
    + reflexivity.
Qed.

Lemma prefix_red_prefix : forall n l,
  List.length (prefix_red l) = n ->
  0 < n -> n < List.length l ->
  l = repeat true n ++ false :: skipn (S n) l.
Proof.
  intros. revert dependent n. induction l; intros.
  - simpl in H. omega.
  - simpl in H. destruct a.
    + destruct n.
      * omega.
      * simpl repeat.
        replace (skipn (S (S n)) (true::l)) with (skipn (S n) l) by reflexivity.
        rewrite <- app_comm_cons. f_equal.
        destruct n.
        -- simpl. destruct l.
           ++ simpl in H1. omega.
           ++ simpl in H. destruct b.
              ** discriminate.
              ** reflexivity.
        -- apply IHl.
           ++ simpl in H. omega.
           ++ omega.
           ++ simpl in H1. omega.
    + simpl in H. omega.
Qed.

Section test.

Context (n : nat).

Fixpoint seq N :=
  match N with
  | 0 => []
  | S N => N :: seq N
  end.

Lemma seq_in_iff : forall N x,
  In x (seq N) <-> x < N.
Proof.
  split; intros.
  - induction N.
    + inversion H.
    + simpl in H. destruct H.
      * subst x. apply le_n.
      * rewrite IHN. apply le_n. assumption.
  - induction N.
    + inversion H.
    + simpl. inversion H.
      * left; reflexivity.
      * right; auto.
Qed.

Lemma seq_nth : forall k N,
  nth k (seq N) 0 = N-k-1.
Proof.
  intros. revert k. induction N; intros.
  - simpl. destruct k; reflexivity.
  - destruct k.
    + simpl. rewrite <- Minus.minus_n_O. reflexivity.
    + simpl. rewrite IHN. reflexivity.
Qed.

Lemma seq_length : forall N, length (seq N) = N.
Proof.
  induction N.
  - reflexivity.
  - simpl. apply f_equal. assumption.
Qed.

Definition l := seq (S n).
Definition bla := List.map (fun k =>
  set_filter (fun l => List.length (prefix_red l) =? k) (enumerate_all n)) l.

Lemma test : enumerate_all n \equiv fold_union bla.
Proof.
  unfold bla. unfold l.
  apply set_same_In_iff; intros.
  rewrite fold_union_In.
  split; intros.
  - remember (List.length (prefix_red a)) as N.
    eexists.
    rewrite in_map_iff. split.
    exists N. split.
    reflexivity.
    apply seq_in_iff. rewrite HeqN. pose proof (prefix_red_length a).
    rewrite enumerate_all_length_n_iff in H. rewrite H in H0. omega.
    rewrite set_filter_In. split. assumption.
    apply Nat.eqb_eq. congruence.
  - destruct H as (s & H & H0).
    apply in_map_iff in H. destruct H as (x & H1 & H2).
    rewrite <- H1 in H0. rewrite set_filter_In in H0.
    apply H0.
Qed.

Import Sorted.

Lemma bla_pairwise_disjoint :
  StronglySorted (fun s1 s2 => set_inter s1 s2 \equiv \emptyset) bla.
Proof.
  apply StronglySorted_alt with (a:=\emptyset).
  intros. unfold bla.
  apply set_same_In_iff.
  split; intros.
  - rewrite set_inter_In in H1. destruct H1.
      set (f:=fun k : nat => set_filter
        (fun l : list bool => length (prefix_red l) =? k) (enumerate_all n)) in *.
    rewrite nth_indep with
      (d':=f 0) in H1, H2.
    rewrite map_nth in H1, H2.
    unfold f in H1, H2.
    rewrite set_filter_In in H1, H2.
    destruct H1 as (HH & H1).
    destruct H2 as (_ & H2).
    apply Nat.eqb_eq in H1. apply Nat.eqb_eq in H2.
    unfold l in H1, H2.
    rewrite seq_nth in H1, H2.
    assert (length bla = S n).
    { unfold bla. rewrite List.map_length. unfold l. rewrite seq_length. reflexivity. }
    omega. assumption. rewrite H. assumption.
  - inversion H1.
Qed.

Lemma test2 : filter n \equiv fold_union (List.map (set_filter valid) bla).
Proof.
  rewrite <- fold_union_set_filter.
  rewrite <- test. reflexivity.
Qed.

Lemma bla_pairwise_disjoint_bis :
  StronglySorted (fun s1 s2 => set_inter s1 s2 \equiv \emptyset) (List.map (set_filter valid) bla).
Proof.
  apply StronglySorted_alt with (a:=\emptyset).
  intros.
  apply set_same_In_iff; split; intros.
  - apply set_inter_In in H1. destruct H1.
    replace \emptyset with (set_filter valid \emptyset) in H1, H2.
    rewrite map_nth in H1, H2.
    pose proof (bla_pairwise_disjoint).
    rewrite StronglySorted_alt with (a0:=\emptyset) in H3.
    rewrite set_filter_In in H1, H2.
    destruct H1 as (H1 & _). destruct H2 as (H2 & _).
    rewrite <- H3 with (i:=i) (j:=j); try assumption.
    apply set_inter_In; split; assumption.
    rewrite map_length in H0. assumption.
    reflexivity.
  - inversion H1.
Qed.

Lemma test18 : filter n \equiv
  fold_union
    (List.map (fun k => set_filter valid
       (set_filter (fun l => length (prefix_red l) =? k) (enumerate_all n))) l).
Proof.
  rewrite <- map_map. apply test2.
Qed.

Lemma test19 : set_size (filter n) =
  List.fold_left Nat.add
    (List.map set_size
      (List.map (fun l => set_filter valid l) bla)) 0.
Proof.
  rewrite test2.
  apply fold_union_disjoint_size.
  apply bla_pairwise_disjoint_bis.
Qed.

Definition f m :=
  set_map (fun l => repeat true m ++ false :: l) (filter (n-(S m))).

Lemma injective_f : forall m, injective (fun l => repeat true m ++ false :: l).
Proof.
  intros. unfold injective; intros.
  apply app_inv_head in H. inversion H; reflexivity.
Qed.

Lemma skipn_length : forall {A} k (m:list A),
  k <= List.length m ->
  length (skipn k m) = List.length m - k.
Proof.
  intros. pose proof (firstn_skipn k m).
  apply (f_equal (@length _)) in H0.
  rewrite app_length in H0.
  pose proof (firstn_length_le _ H).
  omega.
Qed.

Lemma skipn_app : forall {A} k (l1 l2 : list A),
  skipn k (l1 ++ l2) = skipn k l1 ++ skipn (k - length l1) l2.
Proof.
  intros. revert k. induction l1; intros.
  - simpl. rewrite <- Minus.minus_n_O. destruct k; reflexivity.
  - simpl. destruct k.
    + simpl. reflexivity.
    + simpl. apply IHl1.
Qed.

Lemma skipn_all : forall {A} k (m:list A),
  length m <= k ->
  skipn k m = [].
Proof.
  intros A k m. revert k. induction m; intros.
  - destruct k; reflexivity.
  - destruct k.
    + simpl in H. inversion H.
    + simpl. apply IHm. simpl in H. omega.
Qed.

Lemma test21 : forall s acc,
  valid_aux acc s = true <->
    Forall (fun x => x = true) s /\ (acc + length s = 0 \/ 3 <= acc + length s) \/
    List.nth 0 s true = false /\ (acc = 0 \/ 3 <= acc) /\ valid (skipn 1 s) = true
    \/ exists n, s = repeat true n ++ false :: skipn (S n) s
       /\ 3 <= n + acc /\ valid (skipn (S n) s) = true.
Proof.
  split; intros.
  - revert dependent acc. induction s; intros.
    + unfold valid_aux in H. left. split; [constructor|].
      apply orb_true_iff in H. rewrite Nat.eqb_eq, Nat.leb_le in H.
      simpl. omega.
    + simpl in H. destruct a.
      * apply IHs in H as H1. destruct H1 as [H1 |[H1|H1]].
        -- left. split. constructor. reflexivity. apply H1.
           destruct s.
           ++ unfold valid_aux in H. apply orb_true_iff in H. destruct H.
              ** apply Nat.eqb_eq in H. omega.
              ** apply Nat.leb_le in H. simpl. omega.
           ++ destruct b. simpl in H. destruct s. unfold valid_aux in H.
              apply orb_true_iff in H. destruct H.
              ** apply Nat.eqb_eq in H. omega.
              ** apply Nat.leb_le in H. simpl. omega.
              ** simpl. omega.
              ** destruct H1 as (H1 & _). inversion H1. congruence.
        -- right; right. exists 1.
           destruct H1. destruct s. discriminate.
           simpl. simpl in H0. subst b. split; [reflexivity|].
           split. omega. simpl in H. apply andb_true_iff in H.
           apply H.
        -- destruct H1 as (m & H11 & H12 & H13).
           right; right.
           exists (S m).
           repeat split.
           ++ rewrite H11 at 1. reflexivity.
           ++ omega.
           ++ assumption.
      * apply andb_true_iff in H. destruct H.
        apply orb_true_iff in H. destruct H.
        -- right; left. split; [reflexivity|]. split. left. apply Nat.eqb_eq in H.
           assumption. assumption.
        -- right; left. split; [reflexivity|]. split. right.
           do 3 (try destruct acc); try discriminate. omega. assumption.
  - revert dependent acc. induction s; intros.
    + destruct H as [H|[H|H]].
      * unfold valid_aux. apply orb_true_iff.
        rewrite Nat.eqb_eq, Nat.leb_le. simpl in H. omega.
      * unfold valid_aux. rewrite orb_true_iff, Nat.eqb_eq, Nat.leb_le.
        omega.
      * destruct H as (m & H1 & H2 & H3).
        destruct m; discriminate H1.
    + destruct H as [H|[H|H]].
      * destruct H. inversion H; subst. simpl. apply IHs.
        left. split. assumption. simpl in H0. omega.
      * destruct H. destruct H0; simpl in H. subst a. unfold valid_aux.
        apply andb_true_iff. split.
        rewrite orb_true_iff, Nat.eqb_eq, Nat.leb_le.
        assumption. apply H1.
      * destruct H as (m & H1 & H2 & H3).
        destruct a.
        -- simpl. apply IHs. destruct m. discriminate.
           right; right. exists m.
           split. simpl repeat in H1. rewrite <- app_comm_cons in H1.
           apply (f_equal (@List.tl _)) in H1. assumption.
           split. omega. assumption.
        -- destruct m.
           ++ simpl in H3. unfold valid_aux. apply andb_true_iff.
              split.
              ** rewrite orb_true_iff, Nat.leb_le. right; assumption.
              ** apply H3.
           ++ discriminate.
Qed.

Lemma test22 : forall s,
  valid s = true <->
    Forall (fun x => x = true) s /\ (length s = 0 \/ 3 <= length s) \/
    List.nth 0 s true = false /\ valid (skipn 1 s) = true
    \/ exists n, s = repeat true n ++ false :: skipn (S n) s /\ 3 <= n
       /\ valid (skipn (S n) s) = true.
Proof.
  intros. split; intros.
  - apply test21 in H. destruct H as [H|[H|H]].
    + left. split; [apply H|]. omega.
    + right; left. destruct H. destruct H0. split; assumption.
    + right; right. destruct H as (m & H1 & H2 & H3).
      exists m. repeat split; try assumption. omega.
  - apply test21.
    destruct H as [H|[H|H]].
    + left. split; [apply H|]. omega.
    + right; left. split; [apply H|]. split; [omega|].
      apply H.
    + right; right. destruct H as (m & H1 & H2 & H3).
      exists m. repeat split; try assumption. omega.
Qed.

Lemma test3 : forall m, 3 <= m -> m < n ->
  set_filter valid (set_filter (fun l => length (prefix_red l) =? m) (enumerate_all n))
  \equiv f m.
Proof.
  intros m lt_m le_mn. apply set_same_In_iff.
  split; intros.
  - rewrite set_filter_In in H. destruct H as (H & H0).
    rewrite set_filter_In in H. destruct H as (H & H1).
    unfold f. rewrite set_map_In.
    exists (skipn (S m) a).
    split.
    apply set_filter_In. split.
    apply enumerate_all_length_n_iff.
    rewrite skipn_length.
    apply enumerate_all_length_n in H. omega.
    apply enumerate_all_length_n in H. omega.
    apply Nat.eqb_eq in H1.
    apply test22 in H0. destruct H0 as [H0|[H0|H0]].
    + apply prefix_red_prefix in H1. destruct H0 as (H0 & _).
      rewrite H1 in H0. rewrite Forall_forall in H0.
      specialize (H0 false).
      assert (false <> true) by discriminate.
      contradiction H2. apply H0. rewrite in_app_iff. right.
      left; reflexivity.
      omega. apply enumerate_all_length_n_iff in H. omega.
    + destruct m. inversion lt_m. destruct a.
      * simpl in H1. discriminate.
      * simpl in H1. destruct b. simpl in H0. destruct H0; discriminate.
        simpl in H1; discriminate.
    + destruct H0 as (z & H01 & H02 & H03).
      apply prefix_red_prefix in H1.
      rewrite H1 in H01 at 1.
      assert (m = z).
      { assert (m < z \/ z < m \/ z = m) as Ha by omega.
        destruct Ha as [Ha|[Ha|Ha]].
        - apply (f_equal (fun l => List.nth m l true)) in H01.
          rewrite app_nth2 in H01.
          rewrite app_nth1 in H01.
          rewrite repeat_length in H01. replace (m-m) with 0 in H01 by omega.
          simpl in H01.
          pose proof (repeat_spec z true false).
          rewrite H01 in H0 at 1.
          assert (false <> true) by discriminate.
          contradiction H2. apply H0.
          apply nth_In. rewrite repeat_length. assumption.
          rewrite repeat_length. assumption.
          rewrite repeat_length. omega.
        - apply (f_equal (fun l => List.nth z l true)) in H01.
          rewrite app_nth1 in H01.
          rewrite app_nth2 in H01.
          rewrite repeat_length in H01. replace (z-z) with 0 in H01 by omega.
          simpl in H01.
          pose proof (repeat_spec m true false).
          rewrite <- H01 in H0 at 1.
          assert (false <> true) by discriminate.
          contradiction H2. apply H0.
          apply nth_In. rewrite repeat_length. assumption.
          rewrite repeat_length. omega.
          rewrite repeat_length. omega.
        - congruence.
      }
      subst z.
      apply H03.
      omega.
      apply enumerate_all_length_n_iff in H. omega.
    + apply prefix_red_prefix; try assumption.
      apply enumerate_all_length_n in H. apply Nat.eqb_eq in H1. assumption.
      apply enumerate_all_length_n_iff in H. omega.
      apply enumerate_all_length_n_iff in H. omega.
  - unfold f in H. rewrite set_map_In in H.
    destruct H as (b & H0 & H1).
    rewrite set_filter_In. split.
    + rewrite set_filter_In. split.
      * apply enumerate_all_length_n_iff. rewrite H1.
        rewrite app_length. rewrite repeat_length.
        apply set_filter_In in H0. destruct H0.
        apply enumerate_all_length_n_iff in H. simpl. omega.
      * apply Nat.eqb_eq. rewrite H1.
        clear dependent n. clear dependent a.
        clear lt_m. induction m.
        simpl. reflexivity.
        simpl. f_equal. assumption.
    + apply test22. right; right.
      exists m. split. rewrite H1 at 2.
      rewrite skipn_app.
      rewrite repeat_length.
      replace (S m - m) with 1 by omega.
      rewrite skipn_all. assumption.
      rewrite repeat_length. omega.
      split. assumption. rewrite H1.
      rewrite skipn_app.
      rewrite repeat_length.
      replace (S m - m) with 1 by omega.
      rewrite skipn_all. apply set_filter_In in H0. apply H0.
      rewrite repeat_length. omega.
Qed.

Lemma test31 : 1 < n ->
  set_filter valid (set_filter (fun l => length (prefix_red l) =? 1) (enumerate_all n))
  \equiv \emptyset.
Proof.
  intros.
  apply set_same_In_iff; split; intros.
  - apply set_filter_In in H0. destruct H0.
    apply set_filter_In in H0. destruct H0.
    apply test22 in H1.
    destruct H1 as [H1 | [H1|H1]].
    + destruct a. simpl in H2. discriminate.
      destruct a.
      apply enumerate_all_length_n_iff in H0. simpl in H0. omega.
      simpl in H2.
      destruct b.
      destruct b0.
      simpl in H2. discriminate.
      destruct H1. inversion H1; subst.
      inversion H7; discriminate.
      simpl in H2. discriminate.
    + destruct a. simpl in H2. discriminate.
      simpl in H2. destruct b. simpl in H1. destruct H1. discriminate.
      simpl in H2. discriminate.
    + destruct H1 as (m & H11 & H12 & H13).
      rewrite H11 in H2.
      destruct m. simpl in H2. discriminate.
      destruct m. omega.
      simpl in H2. discriminate.
  - inversion H0.
Qed.

Lemma test32 : 2 < n ->
  set_filter valid (set_filter (fun l => length (prefix_red l) =? 2) (enumerate_all n))
  \equiv \emptyset.
Proof.
  intros.
  apply set_same_In_iff; split; intros.
  - apply set_filter_In in H0. destruct H0.
    apply set_filter_In in H0. destruct H0.
    apply test22 in H1.
    destruct H1 as [H1 | [H1|H1]].
    + destruct a. simpl in H2. discriminate.
      destruct a.
      apply enumerate_all_length_n_iff in H0. simpl in H0. omega.
      simpl in H2.
      destruct b.
      destruct b0.
      destruct a. apply enumerate_all_length_n_iff in H0. simpl in H0. omega.
      destruct b. simpl in H2. discriminate.
      destruct H1 as (H1 & _).
      rewrite Forall_forall in H1.
      assert (false <> true) by discriminate.
      contradiction H3. apply H1. right; right; left; reflexivity.
      simpl in H2. discriminate.
      simpl in H2. discriminate.
    + destruct a. simpl in H2. discriminate.
      simpl in H2. destruct b. simpl in H1. destruct H1. discriminate.
      simpl in H2. discriminate.
    + destruct H1 as (m & H11 & H12 & H13).
      rewrite H11 in H2.
      destruct m. simpl in H2. discriminate.
      destruct m. omega.
      destruct m. omega.
      simpl in H2. discriminate.
  - inversion H0.
Qed.

Lemma test33 : 0 < n ->
  set_filter valid (set_filter (fun l => length (prefix_red l) =? 0) (enumerate_all n))
  \equiv f 0.
Proof.
  intros. apply set_same_In_iff; split; intros.
  - rewrite set_filter_In in H0. destruct H0.
    rewrite set_filter_In in H0. destruct H0.
    unfold f. apply set_map_In.
    destruct a. apply enumerate_all_length_n_iff in H0.
    simpl in H0. omega.
    exists a.
    simpl in H2. destruct b.
    + simpl in H2. discriminate.
    + split; [|reflexivity].
      apply set_filter_In. split.
      * apply enumerate_all_length_n_iff. apply enumerate_all_length_n_iff in H0.
        simpl in H0. omega.
      * apply test22 in H1. destruct H1 as [H1 | [H1 | H1]].
        -- destruct H1. inversion H1. discriminate.
        -- apply H1.
        -- destruct H1 as (m & H11 & H12 & H13).
           destruct m. inversion H12.
           discriminate.
  - unfold f in H0.
    apply set_map_In in H0. destruct H0 as (b & H01 & H02).
    simpl in H02. apply set_filter_In in H01.
    destruct H01.
    rewrite set_filter_In. split.
    + rewrite set_filter_In. split.
      * rewrite H02. apply enumerate_all_length_n_iff. simpl.
        apply enumerate_all_length_n_iff in H0.
        omega.
      * rewrite H02. reflexivity.
    + rewrite H02. apply test22.
      right; left. split.
      reflexivity. assumption.
Qed.

Lemma test34 : n >= 3 -> set_filter valid (set_filter (fun l => length (prefix_red l) =? n) (enumerate_all n))
  \equiv \sin (repeat true n).
Proof.
  intros ge_n.
  apply set_same_In_iff; split; intros.
  - apply set_singleton_In. apply set_filter_In in H.
    destruct H. apply set_filter_In in H.
    destruct H.
    apply Nat.eqb_eq in H1.
    apply enumerate_all_length_n_iff in H. clear H0.
    rename n into m. clear ge_n.
    revert dependent m. induction a; intros.
    + simpl in H. subst. reflexivity.
    + destruct m.
      * simpl in H. discriminate.
      * simpl in H1. destruct a.
        -- simpl. apply f_equal. auto.
        -- simpl in H1. discriminate.
  - apply set_singleton_In in H.
    rewrite set_filter_In.
    split.
    + rewrite set_filter_In. split.
      * rewrite H. apply enumerate_all_length_n_iff.
        rewrite repeat_length. reflexivity.
      * rewrite H. apply Nat.eqb_eq.
        clear dependent a. clear ge_n.
        induction n.
        -- reflexivity.
        -- simpl. omega.
    + subst a. apply test22.
      left. split.
      clear ge_n. induction n.
      constructor. simpl. constructor. reflexivity.
      assumption.
      right. rewrite repeat_length. omega.
Qed.

Definition g n m :=
  if m =? 0 then set_size (filter (n - 1))
  else if (3 <=? m) && (m <? n) then set_size (filter (n-m-1))
  else if m =? n then 1 else 0.

Lemma list_eq_nth : forall {A} (a:A) (l1 l2:list A),
  (length l1 = length l2) ->
  (forall i, i < length l1 -> nth i l1 a = nth i l2 a) -> l1 = l2.
Proof.
  intros A a l1. induction l1; intros.
  - simpl in H. destruct l2; [reflexivity|discriminate].
  - destruct l2; [discriminate|].
    pose proof (H0 0).
    simpl in H1. rewrite H1 by omega. f_equal.
    apply IHl1. simpl in H. omega. intros. apply (H0 (S i)).
    simpl. omega.
Qed.

Require Import Psatz.
Lemma test40 : 3 < n -> set_size (filter n) = fold_left Nat.add (map (g n) (seq (S n))) 0.
Proof.
  intros. rewrite test19. f_equal.
  apply list_eq_nth with (a:=0).
  - rewrite 2!map_length. unfold bla.
    rewrite 2!map_length. unfold l.
    reflexivity.
  - intros.
    rewrite nth_indep with (d':=set_size (empty_set)).
    rewrite map_nth.
    rewrite nth_indep with (d:=0) (d':=g n 0).
    rewrite map_nth.
    rewrite nth_indep with (d':=set_filter valid \emptyset).
    rewrite map_nth. rewrite seq_nth.
    unfold bla.
    set (z:=(fun k : nat => set_filter
      (fun l0 : list bool => length (prefix_red l0) =? k) (enumerate_all n))).
    rewrite nth_indep with (d':=z 0).
    rewrite map_nth.
    unfold l. rewrite seq_nth.
    unfold g.
    unfold z.
    assert (S n -i - 1 = 0 \/ S n - i - 1 > 0) by lia.
    destruct H1.
    + rewrite H1. simpl. rewrite test33 by lia. unfold f.
      rewrite set_size_inj. reflexivity. apply injective_f.
    + assert (S n - i - 1 = 1 \/ S n - i - 1  =2 \/ 3 <= S n - i - 1) by lia.
      destruct H2 as [H2|[H2|H2]].
      * rewrite H2. assert (1 <> n) by lia. apply Nat.eqb_neq in H3.
        rewrite H3. simpl.
        rewrite test31 by lia. reflexivity.
      * rewrite H2. assert (2 <> n) by lia. apply Nat.eqb_neq in H3.
        rewrite H3. simpl. rewrite test32 by lia. reflexivity.
      * assert (S n - i - 1 < n \/ S n - i - 1 = n) by lia.
        destruct H3.
        -- rewrite test3.
           unfold f. rewrite set_size_inj.
           assert (S n - i - 1 <> 0) by lia.
           apply Nat.eqb_neq in H4. rewrite H4.
           apply Nat.leb_le in H2 as H5. rewrite H5.
           apply Nat.ltb_lt in H3 as H6. rewrite H6.
           simpl andb.
           cbv iota. f_equal. f_equal. clear H1 H2 H5 H4 H6. lia.
           apply injective_f. assumption. assumption.
        -- rewrite H3. assert (n<>0) by lia. apply Nat.eqb_neq in H4. rewrite H4.
           rewrite test34 by lia.
           assert (3 <= n) by lia. apply Nat.leb_le in H5. rewrite H5.
           assert (~ n < n) by lia. apply Nat.ltb_nlt in H6. rewrite H6.
           simpl. rewrite Nat.eqb_refl. reflexivity.
    + unfold z. rewrite map_length.
      unfold bla in H0. rewrite 3!map_length in H0. assumption.
    + rewrite map_length in H0. assumption.
    + unfold g. unfold bla, l in H0. rewrite 3!map_length in H0.
      rewrite map_length. assumption.
    + assumption.
Qed.

Lemma seq_list_seq : forall n,
  seq n = List.rev (List.seq 0 n).
Proof.
  intros. apply list_eq_nth with (a:=0).
  rewrite List.rev_length. rewrite seq_length.
  rewrite List.seq_length. reflexivity.
  intros.
  rewrite seq_nth. rewrite List.rev_nth.
  rewrite List.seq_nth.
  rewrite List.seq_length. omega.
  rewrite List.seq_length. rewrite seq_length in H. omega.
  rewrite List.seq_length. rewrite seq_length in H. assumption.
Qed.

Lemma fold_add_last_simpl : forall (l : list nat) a (acc : nat),
  fold_left Nat.add (l++[a]) acc = acc + a + fold_left Nat.add l 0.
Proof.
  intros l. induction l; intros.
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - simpl. rewrite IHl. rewrite fold_add_simpl with (acc:=a).
    omega.
Qed.

Lemma fold_add_rev : forall l acc,
  fold_left Nat.add l acc = fold_left Nat.add (List.rev l) acc.
Proof.
  intros l. induction l; intros.
  - simpl. reflexivity.
  - simpl. rewrite fold_add_last_simpl.
    rewrite fold_add_simpl. f_equal. apply IHl.
Qed.

Lemma seq_l : forall start len, 1 <= len ->
  List.seq start len = List.seq start (len - 1) ++ [start + len - 1].
Proof.
  intros start len. revert start. induction len; intros.
  - inversion H.
  - destruct len. simpl. f_equal; omega.
    replace (List.seq start (S (S len)))
      with (start :: List.seq (S start) (S len))
      by reflexivity.
    simpl List.seq at 2.
    simpl app.
    f_equal.
    rewrite IHlen by omega.
    f_equal. f_equal. omega. f_equal. omega.
Qed.

Lemma test41 : 3 < n -> set_size (filter n) = set_size (filter (n-1)) +
  fold_left Nat.add (map (g n) (List.seq 3 (n-3))) 0 + 1.
Proof.
  intros. rewrite test40 by assumption.
  rewrite seq_list_seq. rewrite fold_add_rev.
  rewrite <- map_rev. rewrite rev_involutive.
  simpl. rewrite fold_add_simpl. unfold g at 1. simpl.
  rewrite <- Nat.add_assoc. f_equal.
  destruct n. omega. simpl.
  destruct n0. omega. simpl.
  rewrite fold_add_simpl.
  assert (g (S (S n0)) 2 = 0).
  { destruct n0. omega. reflexivity. }
  rewrite H0. simpl.
  destruct n0. omega.
  rewrite seq_l. rewrite map_app.
  simpl.
  rewrite fold_add_last_simpl. simpl. rewrite Nat.add_comm.
  f_equal. unfold g; simpl. rewrite Nat.ltb_irrefl.
  rewrite Nat.eqb_refl. reflexivity. omega.
Qed.

End test.

Lemma test00 : filter 0 \equiv [[]].
Proof.
  apply set_same_In_iff; split; intros.
  - unfold filter in H. unfold enumerate_all in H.
    apply set_filter_In in H. destruct H.
    apply set_add_elim in H. destruct H.
    subst a. repeat constructor.
    inversion H.
  - inversion H. subst a. repeat constructor. inversion H0.
Qed.

Lemma tests00 : set_size (filter 0) = 1.
Proof.
  reflexivity.
Qed.

Lemma test01 : filter 1 \equiv [[false]].
Proof.
  apply set_same_In_iff; split; intros.
  - unfold filter in H. rewrite set_filter_In in H.
    destruct H.
    apply enumerate_all_length_n_iff in H.
    destruct a. discriminate.
    destruct a.
    unfold valid in H0.
    simpl in H0. destruct b. discriminate.
    repeat constructor.
    discriminate.
  - inversion H; try contradiction. subst a. repeat constructor.
Qed.

Lemma tests01 : set_size (filter 1) = 1.
Proof.
  reflexivity.
Qed.

Lemma test02 : filter 2 \equiv [[false; false]].
Proof.
  apply set_same_In_iff; split; intros.
  - unfold filter in H. apply set_filter_In in H. destruct H.
    apply enumerate_all_length_n_iff in H.
    do 3 (try destruct a; try discriminate).
    unfold valid in H0.
    simpl in H0.
    destruct b. destruct b0; discriminate.
    destruct b0; try discriminate. repeat constructor.
  - inversion H; try contradiction.
    subst a. repeat constructor.
Qed.

Lemma tests02 : set_size (filter 2) = 1.
Proof.
  reflexivity.
Qed.

Lemma test03 : filter 3 \equiv [[false; false; false];[true;true;true]].
Proof.
  apply set_same_In_iff; split; intros.
  - unfold filter in H. apply set_filter_In in H. destruct H.
    apply enumerate_all_length_n_iff in H.
    do 4 (try destruct a; try discriminate).
    unfold valid in H0. simpl in H0. destruct b.
    destruct b0. destruct b1. right; left. reflexivity.
    discriminate.
    discriminate.
    destruct b0. destruct b1. discriminate. discriminate.
    destruct b1. discriminate. left. reflexivity.
  - destruct H.
    subst a.
    right; left. reflexivity.
    destruct H. left; congruence. inversion H.
Qed.

Lemma tests03 : set_size (filter 3) = 2.
Proof.
  reflexivity.
Qed.

End coq.
Import coq.
Definition card s := Z.of_nat (set_size s).
Definition filter n := filter (Z.to_nat n).
