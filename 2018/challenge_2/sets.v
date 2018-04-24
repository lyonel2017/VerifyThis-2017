Require Import set.
Require Import Setoid.
Require Import Omega.

Section DS.

Context `{DS:DecidableType}.
(* 
Global Instance DS_set : DecidableType (set A).
Proof.
  split. intros.
  apply (List.list_eq_dec DS_decide x).
Defined. *)

Fixpoint fold_union l :=
  List.fold_left set_union l empty_set.

(* Global Add Parametric Morphism : fold_union
  with signature set_same ==> set_same as set_same_fold_union.
Proof.
  intros. induction x.
  - simpl. *)

Lemma fold_union_simpl : forall l acc,
  List.fold_left set_union l acc \equiv acc \cup fold_union l.
Proof.
  intros l. induction l; intros.
  - simpl. rewrite set_same_union_empty_r.
    reflexivity.
  - simpl. rewrite 2!IHl. rewrite set_same_union_empty_l.
    rewrite set_union_assoc. reflexivity.
Qed.

Lemma fold_union_cons : forall a l,
  fold_union (a::l) \equiv a \cup fold_union l.
Proof.
  intros. simpl. rewrite fold_union_simpl. rewrite set_same_union_empty_l.
  reflexivity.
Qed.

Lemma fold_union_union : forall l1 l2,
  fold_union (l1 ++ l2) \equiv (fold_union l1) \cup (fold_union l2).
Proof.
  intros. induction l1; intros.
  - simpl.
    rewrite set_same_union_empty_l. reflexivity.
  - simpl app. rewrite 2!fold_union_cons.
    rewrite set_union_assoc. rewrite IHl1. reflexivity.
Qed.

Lemma set_same_remove_not_In : forall a s,
  ~ a \in s -> set_remove a s \equiv s.
Proof.
  intros. apply set_same_In_iff. intros. rewrite set_remove_not_In.
  split; intros.
  - apply H0.
  - split; congruence.
Qed.

Lemma set_remove_union : forall a s1 s2,
  set_remove a (s1 \cup s2) \equiv (set_remove a s1) \cup (set_remove a s2).
Proof.
  intros. apply set_same_In_iff; split; intros.
  - apply set_remove_not_In in H. destruct H. apply set_union_In in H.
    apply set_union_In. destruct H; [left|right]; apply set_remove_not_In;
      split; assumption.
  - apply set_union_In in H. apply set_remove_not_In. rewrite set_union_In.
    destruct H; rewrite set_remove_not_In in H.
    + destruct H. split.
      * left; assumption.
      * assumption.
    + destruct H; split.
      * right; assumption.
      * assumption.
Qed.

Lemma set_remove_inter : forall a s1 s2,
  set_remove a (s1 \cap s2) \equiv (set_remove a s1) \cap (set_remove a s2).
Proof.
  intros. apply set_same_In_iff; intros. rewrite set_inter_In.
  rewrite !set_remove_not_In. rewrite set_inter_In. split; intros.
  - destruct H as ((H0 & H1) & H2).
    repeat split; congruence.
  - destruct H as ((H0 & H1) & H2 & H3). repeat split; congruence.
Qed.

Lemma set_size_disjoint_union : forall s1 s2,
  s1 \cap s2 \equiv \emptyset ->
  set_size (s1 \cup s2) = set_size s1 + set_size s2.
Proof.
  intros s1. functional induction (set_size s1); intros.
  - rewrite set_same_union_empty_l. reflexivity.
  - setoid_replace ((a::x')%list \cup s2)
      with (a :: (x' \cup s2))%list.
    rewrite set_size_equation. rewrite set_remove_union.
    rewrite IHn. rewrite PeanoNat.Nat.add_assoc.
    rewrite set_same_remove_not_In with (s:=s2). reflexivity.
    intros contra.
    assert (a \in (a::x')%list \cap s2).
    { apply set_inter_In. split; [|assumption].
      left. reflexivity.
    }
    rewrite H in H0. inversion H0.
    rewrite <- set_remove_inter.
    assert (x' \cap s2 \equiv \emptyset).
    { apply set_same_In_iff; split; intros.
      - rewrite <- H. apply set_inter_In. apply set_inter_In in H0.
        split. right; apply H0. apply H0.
      - inversion H0.
    }
    apply set_same_In_iff; split; intros.
    apply set_remove_not_In in H1. destruct H1 as (H1 & _). rewrite H0 in H1.
    inversion H1. inversion H1.
    apply set_same_In_iff; split; intros.
    apply set_union_In in H0. destruct H0.
    Transparent set_In.
    destruct H0. left. assumption.
    right. rewrite set_union_In. left; assumption.
    right. rewrite set_union_In. right; assumption.
    rewrite set_union_In.
    destruct H0.
    left; left; assumption.
    rewrite set_union_In in H0. destruct H0.
    left; right; assumption.
    right; assumption.
    Opaque set_In.
Qed.

Require Import Sorted.

Lemma fold_add_simpl : forall l acc,
  List.fold_left Nat.add l acc = acc + List.fold_left Nat.add l 0.
Proof.
  intros l. induction l; intros.
  - simpl. rewrite PeanoNat.Nat.add_0_r.
    reflexivity.
  - simpl. rewrite IHl. rewrite IHl with (acc:=a).
    rewrite PeanoNat.Nat.add_assoc. reflexivity.
Qed.

Lemma set_same_inter_empty_l : forall s, \emptyset \cap s \equiv \emptyset.
Proof.
  intros. apply set_same_In_iff; intros. rewrite set_inter_In.
  split; intros.
  - apply H.
  - inversion H.
Qed.

Lemma set_same_inter_empty_r : forall s, s \cap \emptyset \equiv \emptyset.
Proof.
  intros. apply set_same_In_iff; intros. rewrite set_inter_In.
  split; intros.
  - apply H.
  - inversion H.
Qed.

Lemma StronglySorted_alt : forall (a:A) P l,
  StronglySorted P l <->
    (forall i j, i < j -> j < List.length l -> P (List.nth i l a) (List.nth j l a)).
Proof.
  split.
  - intros H. induction H; intros.
    + simpl in H0. inversion H0.
    + assert (i = 0 \/ 0 < i) by omega. destruct H3.
      * subst i. simpl List.nth at 1.
        rewrite List.Forall_forall in H0. apply H0.
        destruct j. inversion H1. simpl in H2. apply le_S_n in H2.
        simpl. apply List.nth_In. assumption.
      * destruct i. inversion H3. destruct j. inversion H1. simpl.
        apply IHStronglySorted. apply le_S_n in H1. assumption.
        simpl in H2. apply le_S_n in H2. assumption.
  - induction l; intros.
    + constructor.
    + constructor.
      * apply IHl. intros. apply (H (S i) (S j)).
        apply le_n_S. assumption. simpl. apply le_n_S. assumption.
      * rewrite List.Forall_forall. intros.
        apply List.In_nth with (d:=a) in H0.
        destruct H0 as (j & H0 & H1).
        rewrite <- H1.
       apply (H 0 (S j)). omega. simpl. apply le_n_S. assumption.
Qed.

Lemma fold_union_disjoint_size : forall l,
  StronglySorted (fun s1 s2 => set_inter s1 s2 \equiv \emptyset) l ->
  set_size (fold_union l) = List.fold_left Nat.add (List.map set_size l) 0.
Proof.
  intros. induction H.
  - simpl. reflexivity.
  - rewrite fold_union_cons. simpl. rewrite fold_add_simpl.
    rewrite set_size_disjoint_union.
    f_equal. apply IHStronglySorted.
    clear IHStronglySorted H. induction H0.
    + simpl. rewrite set_same_inter_empty_r. reflexivity.
    + rewrite fold_union_cons. rewrite set_inter_comm.
      rewrite set_inter_union_distr_l.
      rewrite 2!set_inter_comm with (y:=a).
      rewrite IHForall.
      rewrite H. rewrite set_same_union_empty_l. reflexivity.
Qed.

Lemma fold_union_In : forall x l,
  x \in fold_union l <-> exists s, List.In s l /\ x \in s.
Proof.
  split; intros.
  - induction l.
    + simpl in H. inversion H.
    + rewrite fold_union_cons in H. rewrite set_union_In in H.
      destruct H.
      * exists a. split; [|assumption]. left; reflexivity.
      * apply IHl in H. destruct H as (s & H & H0).
        exists s. split; [|assumption]. right; assumption.
  - destruct H as (s & H &  H0).
    induction l.
    + inversion H.
    + rewrite fold_union_cons. rewrite set_union_In. destruct H.
      * left; congruence.
      * right; auto.
Qed.

Lemma set_filter_union : forall f s1 s2,
  set_filter f (s1 \cup s2) \equiv set_filter f s1 \cup set_filter f s2.
Proof.
  intros. apply set_same_In_iff; split; intros.
  - rewrite set_union_In. rewrite set_filter_In in H.
    destruct H. rewrite set_union_In in H.
    destruct H.
    + left; rewrite set_filter_In; split; assumption.
    + right; rewrite set_filter_In; split; assumption.
  - rewrite set_union_In in H. rewrite set_filter_In.
    destruct H.
    + rewrite set_filter_In in H. split; [rewrite set_union_In; left|]; apply H.
    + rewrite set_filter_In in H. split; [rewrite set_union_In; right|]; apply H.
Qed.

Lemma fold_union_set_filter : forall P l,
  set_filter P (fold_union l) \equiv fold_union (List.map (set_filter P) l).
Proof.
  intros. induction l.
  - simpl. apply set_same_In_iff. split; intros.
    + apply set_filter_In in H. destruct H; assumption.
    + inversion H.
  - simpl List.map. rewrite 2!fold_union_cons.
    rewrite set_filter_union. rewrite IHl. reflexivity.
Qed.

End DS.

Definition injective {A B} (f:A->B) := forall x y, f x = f y -> x = y.

Lemma set_size_inj : forall {A B} {DSA:DecidableType A} {DSB:DecidableType B} f s
  (inj : injective f),
  set_size (set_map f s) = set_size s.
Proof.
  intros. functional induction (set_size s).
  - reflexivity.
  - assert (f a \in set_map f (a :: x')%list).
    { apply set_map_In. exists a. split; [|reflexivity].
      left. reflexivity.
    }
    pose proof (set_size_In_remove _ _ H).
    assert (set_size (set_map f (a :: x')%list) >= 1).
    { apply set_size_ge_1_In. exists (f a). assumption. }
    assert (set_remove (f a) (set_map f (a :: x')%list) \equiv (set_map f (set_remove a x'))).
    { apply set_same_In_iff. split; intros.
      - rewrite set_remove_not_In in H2. destruct H2 as (H21 & H22).
        rewrite set_map_In in H21. destruct H21 as (b & H211 & H212).
        rewrite set_map_In. exists b. split; [|assumption].
        Transparent set_In.
        destruct H211. congruence. rewrite set_remove_not_In. split.
        assumption. congruence.
        Opaque set_In.
      - rewrite set_map_In in H2. destruct H2 as (b & H21 & H22).
        rewrite set_remove_not_In in H21. rewrite set_remove_not_In.
        split.
        + rewrite set_map_In. exists b. split; [|assumption].
          Transparent set_In. right; apply H21. Opaque set_In.
        + destruct H21. intros contra. rewrite contra in H22. apply inj in H22.
          congruence.
    }
    rewrite H2 in H0. omega.
Qed.

