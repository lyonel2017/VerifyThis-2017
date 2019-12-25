Require Import Arith.
Require Import List. Import ListNotations.
Require Import Omega.

Fixpoint nb_occ (l:list nat) (n:nat) : nat :=
  match l with
  | [] => 0
  | h :: t => if h =? n then 1 + nb_occ t n else nb_occ t n
  end.

Lemma nb_occ_app : forall l1 l2 v,
  nb_occ (l1++l2) v = nb_occ l1 v + nb_occ l2 v.
Proof.
  intros l1. induction l1; intros.
  - simpl. reflexivity.
  - simpl. destruct (a =? v); [simpl; f_equal|]; auto.
Qed.

Definition same_elements (l1 l2 : list nat) :=
  forall n, nb_occ l1 n = nb_occ l2 n.

Lemma same_elements_refl : forall l,
  same_elements l l.
Proof.
  unfold same_elements; intros; reflexivity.
Qed.

Definition swap l1 l2 i j :=
  i < length l1 /\ i < j /\ j < length l1 /\
  nth i l1 0 = nth j l2 0 /\
  nth j l1 0 = nth i l2 0 /\
  forall k, k <> i -> k <> j ->
  nth k l1 0 = nth k l2 0.

Lemma list_eq_nth : forall (l1 l2 : list nat),
  length l1 = length l2 ->
  (forall k, k < length l1 -> nth k l1 0 = nth k l2 0) ->
  l1 = l2.
Proof.
  intros l1. induction l1; intros.
  - destruct l2; [reflexivity|discriminate].
  - destruct l2; [discriminate|].
    pose proof (H0 0). simpl in H1. rewrite H1 by omega. f_equal.
    apply IHl1.
    + simpl in H. omega.
    + intros. specialize (H0 (S k)). simpl in H0. apply H0; omega.
Qed.

Lemma swap_decompose : forall l1 l2 i j,
  length l1 = length l2 ->
  swap l1 l2 i j ->
  exists m1 a m2 b m3,
  l1 = m1 ++ a :: m2 ++ b :: m3 /\
  l2 = m1 ++ b :: m2 ++ a :: m3.
Proof.
  intros.
  - destruct H0 as (H1 & H2 & H3 & H4 & H5 & H6).
    destruct (nth_split l1 0 H1) as (m1 & m21 & Heq & Hlen).
    pose proof (f_equal (@length nat) Heq) as Heq_len.
    rewrite app_length in Heq_len. simpl in Heq_len.
    destruct (nth_split m21 0 (n:=j-i-1)) as (m2 & m3 & Heq2 & Hlen2);
      [omega|].
    replace (nth (j-i-1) m21 0) with (nth j l1 0) in Heq2.
    exists m1, (nth i l1 0), m2, (nth j l1 0), m3.
    split.
    + rewrite Heq, Heq2 at 1. reflexivity.
    + apply list_eq_nth. rewrite app_length. simpl.
      rewrite app_length. simpl.
      pose proof (f_equal (@length nat) Heq2).
      rewrite app_length in H0. simpl in H0. omega.
      intros.
      destruct (Nat.lt_ge_cases k i).
      * rewrite app_nth1 by omega.
        rewrite <- H6 by omega. rewrite Heq.
        rewrite app_nth1 by omega. reflexivity.
      * destruct (le_lt_or_eq _ _ H7).
        -- destruct (Nat.lt_ge_cases k j).
           ++ rewrite app_nth2 by omega.
              simpl nth. destruct (k-length m1) eqn:HH; [omega|].
              rewrite app_nth1 by omega.
              rewrite <- H6 by omega. rewrite Heq. rewrite Heq2 at 1.
              rewrite app_nth2 by omega.
              simpl. rewrite HH. rewrite app_nth1 by omega. reflexivity.
           ++ rewrite app_nth2 by omega. simpl. destruct (k-length m1) eqn:HH; [omega|].
              rewrite app_nth2 by omega.
              destruct (le_lt_or_eq _ _ H9).
              ** simpl.
                 destruct (n-length m2) eqn:HH2; [omega|].
                 rewrite <- H6 by omega. rewrite Heq.
                 rewrite app_nth2 by omega. simpl. rewrite HH.
                 rewrite Heq2. rewrite app_nth2 by omega.
                 simpl. rewrite HH2. omega.
              ** simpl. destruct (n-length m2) eqn:HH2; [|omega].
                 rewrite H4. subst j; reflexivity.
        -- rewrite app_nth2 by omega. destruct (k-length m1) eqn:HH; [|omega].
           simpl. rewrite H5. subst k; reflexivity.
    + rewrite Heq. rewrite app_nth2 by omega. simpl.
      destruct (j-length m1) eqn:HH; [omega|]. f_equal. omega.
Qed.

Lemma nb_occ_swap : forall l1 l2 i j,
  length l1 = length l2 ->
  swap l1 l2 i j ->
  forall v, nb_occ l1 v = nb_occ l2 v.
Proof.
  intros. apply swap_decompose in H0; try assumption.
  destruct H0 as (m1 & a & m2 & b & m3 & H01 & H02).
  rewrite H01, H02.
  rewrite !nb_occ_app. simpl.
  rewrite !nb_occ_app. simpl.
  destruct (a=?v), (b=?v); omega.
Qed.

Lemma same_elements_swap :
  forall l1 l2 i j, length l1 = length l2 ->
  i < length l1 -> j < length l1 ->
  swap l1 l2 i j -> same_elements l1 l2.
Proof.
  intros. unfold same_elements; intros.
  eapply nb_occ_swap; eassumption.
Qed.

Fixpoint update (l:list nat) (k v : nat) : list nat :=
  match k with
  | 0 => v :: tl l
  | S k => (hd 0 l) :: update (tl l) k v
  end.

Lemma tl_length : forall {A} (l:list A), l <> [] ->
  length (tl l) = length l - 1.
Proof.
  intros. destruct l; simpl; omega.
Qed.

Lemma update_zero : forall l v, update l 0 v = v:: tl l.
Proof.
  intros. destruct l; reflexivity.
Qed.

Lemma update_pos : forall l n v, 0 < n ->
  update l n v = (hd 0 l) :: (update (tl l) (n-1) v).
Proof.
  intros. destruct n; [inversion H|].
  simpl. f_equal. f_equal. rewrite <- Minus.minus_n_O. reflexivity.
Qed.

Lemma update_length : forall l k v, 0 < length l -> 0 <= k -> k < length l ->
  length (update l k v) = length l.
Proof.
  intros l k. revert l. induction k; intros.
  - simpl. rewrite tl_length. omega. destruct l; [inversion H|discriminate].
  - simpl.
    assert (l <> []) as Ha by (intros contra; subst; inversion H).
    apply tl_length in Ha. rewrite IHk; omega.
Qed.

Lemma update_neq : forall l n v, 0 < length l -> 0 <= n -> n < length l ->
  forall k, 0 <= k -> k < length l -> n <> k ->
  nth k (update l n v) 0 = nth k l 0.
Proof.
  intros l n. revert l.
  induction n; intros.
  - destruct k; [contradiction H4; reflexivity|].
    simpl.
    destruct l; [inversion H3|].
    simpl. reflexivity.
  - destruct k.
    + simpl. destruct l; [inversion H3|]. reflexivity.
    + simpl. destruct l; [inversion H3|]. simpl.
      apply IHn. simpl in H3. omega. omega. simpl in H1. omega.
      simpl in H3. omega. simpl in H3. omega. omega.
Qed.

Lemma update_eq : forall l n v, 0 < length l -> 0 <= n -> n < length l ->
  nth n (update l n v) 0 = v.
Proof.
  intros l n. revert l.
  induction n; intros.
  - simpl. reflexivity.
  - destruct l; [inversion H1|]. simpl. apply IHn.
    simpl in H1. omega.
    omega. simpl in H1. omega.
Qed.
