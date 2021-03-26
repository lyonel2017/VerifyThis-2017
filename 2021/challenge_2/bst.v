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

Lemma sorted_dll_to_bst_rec l n : Sorted R l ->
  n <= length l ->
  let (t, l2) := dll_to_bst_rec l n in
  is_bst t /\
  Forall_tree (fun x => R (hd dflt l) x) t /\
  Forall_tree (fun x => R x (hd dflt l2)) t /\
  Sorted R l2. (*
(*  exists l1, Forall_tree (fun x => In x l1) t /\ l = l1 ++ l2. *)
  match l2 with
  | [] => True
  | a :: l2 => Forall_tree (fun x => R a x) t
  end. *)
Proof.
  intros Hsorted Hle.
  funelim (dll_to_bst_rec l n).
  - rewrite <- Heqcall.
    split; [constructor|].
    split; [constructor|].
    split; [constructor|].
    assumption.
  - pose proof (Nat.lt_div2 n).
    destruct (dll_to_bst_rec l (Nat.div2 n)) as [left root] eqn:Hrec1.
    specialize (H0 Leaf root).
    destruct (dll_to_bst_rec (tl root) (n - Nat.div2 n - 1)) as [temp right] eqn:Hrec2.
    rewrite <- Heqcall.
    assert (Nat.div2 n <= length l) as Ha by lia.
    specialize (H Hsorted Ha).
    destruct H as (H01 & H02 & H03 & H04).
    assert (Sorted R (tl root)) as Ha2.
    { destruct root.
      - constructor.
      - simpl. inversion H04; assumption.
    }
    assert (n - Nat.div2 n - 1 <= length (tl root)) as Ha3.
    { pose proof (dll_to_bst_rec_length l (Nat.div2 n)).
      rewrite Hrec1 in H.
      destruct root; simpl in H |- *; lia.
    }
    specialize (H0 Ha2 Ha3).
    destruct H0 as (H11 & H12 & H13 & H14).
    split.
    + constructor.
      * assumption.
      * assumption.
      * assumption.
      * apply Forall_tree_impl.
    
    split.
    + constructor.
      * apply H; try assumption.
        lia.
      * apply H; try assumption.
        lia.
      * specialize (H0 Leaf root).
        rewrite Hrec2 in H0.
        apply H0.
        -- admit.
        -- pose proof (dll_to_bst_rec_length l (Nat.div2 n)).
           rewrite Hrec1 in H2.
           destruct root.
           simpl in H2 |- *. lia.
           simpl in H2 |- *. lia.
      * specialize (H0 Leaf root).
        rewrite Hrec2 in H0.
        apply H0.
      
       pose proof (dll_to_bst_rec_length l (Nat.div2 n)).
        rewrite Hrec1 in H2.
        assert (0 < length root) by lia.
        destruct root; [inversion H3|].
        simpl.
        
        
        le_lt_dec
        lia.
      *
Abort.

End test.
(*
Lemma sorted_bst {A} (a:A) (R : A -> A -> Prop) l : Sorted R l ->
  is_bst _ R (dll_to_bst _ a l).
Proof.
  unfold dll_to_bst.
  remember (size A l) as n.
  assert (n >= size A l).
  { lia. }
  clear Heqn.
  funelim (dll_to_bst_rec A a l n).
  - intros.
  rewrite <- Heqcall. constructor.
  - rewrite <- Heqcall.
*)

Goal dll_to_bst_rec _ 0 [1;2;3;4;5] 10 = (Leaf _, []).
Proof.
  repeat (simp dll_to_bst_rec; simpl).
  simp dll_to_bst_rec. simpl.

Function dll_to_bst_rec (l : list A) n {measure (fun n => n) n} : tree * list A :=
  if 0 <? n then
    let (left, root) := dll_to_bst_rec l (Nat.div2 n) in
    let (temp, right) := dll_to_bst_rec (tl root) (n - Nat.div2 n - 1) in
    (Node left (hd dflt root) temp, right)
  else
    (Leaf, l).
Proof.
  - intros _ n H _ _ _ _.
    apply Nat.ltb_lt in H.
    lia.
  - intros _ n H. apply Nat.ltb_lt in H.
    apply Nat.lt_div2; assumption.
Defined.

End test.

Eval compute in dll_to_bst_rec _ 0 [1;2;3;4;5] 3.