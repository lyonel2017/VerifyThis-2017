Require Import List. Import ListNotations.
Require Import Sorting.
From Equations Require Import Equations.
Require Import Arith.
Require Import Lia.

Section test.

Variable A : Type.
Variable dflt : A.

Definition size := @List.length A.

Inductive tree :=
| Leaf : tree
| Node : tree -> A -> tree -> tree.

Obligation Tactic := intros; auto using Nat.lt_div2; Lia.lia.

Equations dll_to_bst_rec (l : list A) (n:nat) : tree * list A by wf n lt :=
  dll_to_bst_rec l n with le_lt_dec n 0 := {
  | left _ => (Leaf, l);
  | right _ => let (left, root) := dll_to_bst_rec l (Nat.div2 n) in
    let (temp, right) := dll_to_bst_rec (tl root) (n - Nat.div2 n - 1) in
    (Node left (hd dflt root) temp, right)
  }.

Definition dll_to_bst (l : list A) :=
  let n := size l in
  let (root, _) := dll_to_bst_rec l n in
  root.

Variable R : A -> A -> Prop.
Hypothesis R_trans : RelationClasses.Transitive R.

Inductive Forall_tree (P : A -> Prop) : tree -> Prop :=
| Forall_leaf : Forall_tree P Leaf
| Forall_node : forall l a r, Forall_tree P l -> P a -> Forall_tree P r ->
  Forall_tree P (Node l a r).

Inductive is_bst : tree -> Prop :=
| is_bst_leaf : is_bst Leaf
| is_bst_node : forall l a r,
  is_bst l -> Forall_tree (fun x => R x a) l ->
  is_bst r -> Forall_tree (fun x => R a x) r ->
  is_bst (Node l a r).

Lemma dll_to_bst_rec_length l n :
  let (t, l2) := dll_to_bst_rec l n in
  length l2 = length l - n.
Proof.
  funelim (dll_to_bst_rec l n).
  - rewrite <- Heqcall. lia.
  - rewrite <- Heqcall.
    destruct (dll_to_bst_rec l (Nat.div2 n)) as [left root] eqn:Hrec1.
    destruct (dll_to_bst_rec (tl root) (n - Nat.div2 n - 1)) as [temp right] eqn:Hrec2.
    specialize (H0 Leaf root).
    rewrite Hrec2 in H0.
    rewrite H0.
    destruct root.
    + simpl. simpl in H. pose proof (Nat.lt_div2 n). lia.
    + simpl. simpl in H. pose proof (Nat.lt_div2 n). lia.
Qed.

Lemma Forall_tree_impl (P1 P2 : A -> Prop) :
  (forall a, P1 a -> P2 a) ->
  forall t,
  Forall_tree P1 t ->
  Forall_tree P2 t.
Proof.
  intros Himpl t HForall1.
  induction HForall1.
  - constructor.
  - constructor; auto.
Qed.

Lemma Sorted_app_r l1 l2 :
  Sorted R (l1 ++ l2) -> Sorted R l2.
Proof.
  intros H.
  induction l1.
  - assumption.
  - apply IHl1. inversion H; assumption.
Qed.

Lemma sorted_dll_to_bst_rec l n : Sorted R l ->
  n <= length l ->
  let (t, l2) := dll_to_bst_rec l n in
  is_bst t /\
  Forall_tree (fun x => Forall (R x) l2) t /\
  exists l1, Forall_tree (fun x => In x l1) t /\ l = l1 ++ l2.
Proof.
  intros Hsorted Hle.
  funelim (dll_to_bst_rec l n).
  - rewrite <- Heqcall.
    split; [constructor|].
    split; [constructor|].
    exists []; split; constructor.
  - pose proof (Nat.lt_div2 n).
    destruct (dll_to_bst_rec l (Nat.div2 n)) as [left root] eqn:Hrec1.
    specialize (H0 Leaf root).
    destruct (dll_to_bst_rec (tl root) (n - Nat.div2 n - 1)) as [temp right] eqn:Hrec2.
    rewrite <- Heqcall.
    assert (Nat.div2 n <= length l) as Ha by lia.
    specialize (H Hsorted Ha).
    destruct H as (H01 & H02 & (l1' & H03 & H04)).
    assert (Sorted R (tl root)) as Ha2.
    { destruct root.
      - constructor.
      - simpl. rewrite H04 in Hsorted. apply Sorted_app_r in Hsorted.
        inversion Hsorted; assumption.
    }
    assert (n - Nat.div2 n - 1 <= length (tl root)) as Ha3.
    { pose proof (dll_to_bst_rec_length l (Nat.div2 n)).
      rewrite Hrec1 in H.
      destruct root; simpl in H |- *; lia.
    }
    specialize (H0 Ha2 Ha3).
    destruct H0 as (H11 & H12 & l3 & H14 & H15).
    repeat split.
    + constructor.
      * assumption.
      * destruct root.
        -- simpl in Ha3.
           pose proof (dll_to_bst_rec_length l (Nat.div2 n)).
           rewrite Hrec1 in H. simpl in H.
           lia.
        -- eapply Forall_tree_impl; try apply H02; simpl.
           intros x ?.
           inversion H. assumption.
      * assumption.
      * destruct root.
        -- simpl in Ha3.
           replace (n - Nat.div2 n - 1) with 0 in Hrec2 by lia.
           simpl in Hrec2. simp dll_to_bst_rec in Hrec2.
           simpl in Hrec2. inversion Hrec2. constructor.
        -- destruct root.
           ++ simpl in Ha3.
              replace (n - Nat.div2 n - 1) with 0 in Hrec2 by lia.
              simpl in Hrec2. simp dll_to_bst_rec in Hrec2.
              simpl in Hrec2. inversion Hrec2. constructor.
           ++ simpl. simpl in *.
              eapply Forall_tree_impl; try apply H14.
              intros x ?. simpl in H.
              rewrite H15 in H04.
              rewrite H04 in Hsorted.
              apply Sorted_app_r in Hsorted.
              apply Sorted_StronglySorted in Hsorted; try assumption.
              inversion Hsorted.
              rewrite Forall_forall in H4. apply H4.
              apply in_app_iff. left; assumption.
    + constructor.
      * admit.
      * destruct root.
        -- simpl in Ha3.
           replace (n - Nat.div2 n - 1) with 0 in Hrec2 by lia.
           simpl in Hrec2. simp dll_to_bst_rec in Hrec2.
           simpl in Hrec2. inversion Hrec2. constructor.
        -- simpl. simpl in H15. rewrite H15 in H04.
           rewrite H04 in Hsorted.
           apply Sorted_app_r in Hsorted.
           apply Sorted_StronglySorted in Hsorted; try assumption.
           inversion Hsorted.
           apply Forall_app in H3. apply H3.
     * assumption.
    + destruct root.
      -- simpl in Ha3.
         pose proof (dll_to_bst_rec_length l (Nat.div2 n)).
         rewrite Hrec1 in H. simpl in H.
         lia.
      -- simpl in H15. exists (l1' ++ a :: l3).
         split.
         ++ admit.
         ++ rewrite app_assoc_reverse. simpl.
            rewrite <- H15. assumption.
Admitted.

(* Main theorem *)
Lemma sorted_bst l : Sorted R l -> is_bst (dll_to_bst l).
Proof.
  intros Hsorted.
  unfold dll_to_bst.
  pose proof (sorted_dll_to_bst_rec l (size l)).
  destruct (dll_to_bst_rec l (size l)) as [t l2].
  apply H.
  assumption.
  reflexivity.
Qed.

End test.

(*
Goal dll_to_bst_rec _ 0 [1;2;3;4;5] 10 = (Leaf _, []).
Proof.
  repeat (simp dll_to_bst_rec; simpl).
  simp dll_to_bst_rec. simpl.
*)
