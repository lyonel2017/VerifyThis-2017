(*  Relaxed Slicing
    Copyright (C) 2016 CEA LIST

    Contact: Jean-Christophe Léchenet <jean-christophe.lechenet@cea.fr>

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

    It is distributed for noncommercial use only.
    Noncommercial use relates only to educational, research,
    personal or evaluation purposes. Any other use is commercial use.
    You may not use the Software in connection with any activities
    which purpose is to procure a commercial gain to you or others.
*)

(** Defines sets as lists allowing redundancy.
    This allows to benefit from the power of typeclasses.
    Standard implementations of sets (MSets) does not
    suit our needs.
*)

Require Import ListSet.
Require Import Setoid.
Require Recdef.

Class DecidableType A := {
  DS_decide : forall (x y : A), {x = y} + {x <> y}
}.

Definition set A {DS:DecidableType A} := list A.

Section DS.
Context `{DS:DecidableType}.
Definition empty_set : set A := nil.
Definition set_add : A -> set A -> set A := set_add DS_decide.
Definition set_mem :  A -> set A -> bool := set_mem DS_decide.
Definition set_inter : set A -> set A -> set A := set_inter DS_decide.
Definition set_union : set A -> set A -> set A := set_union DS_decide.
Definition set_diff : set A -> set A -> set A := set_diff DS_decide.

Definition set_In : A -> set A -> Prop := set_In (A:=A).

Lemma set_In_dec : forall (a:A) (x:set A), {set_In a x} + {~ set_In a x}.
Proof. apply set_In_dec. apply DS_decide.
Qed.

Lemma set_mem_ind :
 forall (B:Type) (P:B -> Prop) (y z:B) (a:A) (x:set A),
   (set_In a x -> P y) -> P z -> P (if set_mem a x then y else z).
Proof. apply set_mem_ind.
Qed.

Lemma set_mem_ind2 :
 forall (B:Type) (P:B -> Prop) (y z:B) (a:A) (x:set A),
   (set_In a x -> P y) ->
   (~ set_In a x -> P z) -> P (if set_mem a x then y else z).
Proof. apply set_mem_ind2.
Qed.

Lemma set_mem_correct1 :
 forall (a:A) (x:set A), set_mem a x = true -> set_In a x.
Proof. apply set_mem_correct1.
Qed.

Lemma set_mem_correct2 :
  forall (a:A) (x:set A), set_In a x -> set_mem a x = true.
Proof. apply set_mem_correct2.
Qed.

Lemma set_mem_complete1 :
  forall (a:A) (x:set A), set_mem a x = false -> ~ set_In a x.
Proof. apply set_mem_complete1.
Qed.

Lemma set_mem_complete2 :
  forall (a:A) (x:set A), ~ set_In a x -> set_mem a x = false.
Proof. apply set_mem_complete2.
Qed.

Lemma set_mem_correct_iff : forall `{DS : DecidableType} (a : A) (x : set A),
  set_mem a x = true <-> set_In a x.
Proof.
  split; intros.
  - apply set_mem_correct1; assumption.
  - apply set_mem_correct2; assumption.
Qed.

Lemma set_mem_complete_iff : forall `{DS : DecidableType} (a : A) (x : set A),
  set_mem a x = false <-> ~ set_In a x.
Proof.
  split; intros.
  - apply set_mem_complete1; assumption.
  - apply set_mem_complete2; assumption.
Qed.

Lemma set_add_intro1 :
  forall (a b:A) (x:set A), set_In a x -> set_In a (set_add b x).
Proof. apply set_add_intro1.
Qed.

Lemma set_add_intro2 :
  forall (a b:A) (x:set A), a = b -> set_In a (set_add b x).
Proof. apply set_add_intro2.
Qed.

Lemma set_add_intro :
  forall (a b:A) (x:set A), a = b \/ set_In a x -> set_In a (set_add b x).
Proof. apply set_add_intro.
Qed.

Lemma set_add_elim :
  forall (a b:A) (x:set A), set_In a (set_add b x) -> a = b \/ set_In a x.
Proof. apply set_add_elim.
Qed.

Lemma set_add_elim2 :
  forall (a b:A) (x:set A), set_In a (set_add b x) -> a <> b -> set_In a x.
Proof. apply set_add_elim2.
Qed.

Lemma set_add_not_empty : forall (a:A) (x:set A), set_add a x <> empty_set.
Proof. apply set_add_not_empty.
Qed.

Lemma set_union_intro1 :
  forall (a:A) (x y:set A), set_In a x -> set_In a (set_union x y).
Proof. apply set_union_intro1.
Qed.

Lemma set_union_intro2 :
  forall (a:A) (x y:set A), set_In a y -> set_In a (set_union x y).
Proof. apply set_union_intro2.
Qed.

Lemma set_union_intro :
  forall (a:A) (x y:set A),
    set_In a x \/ set_In a y -> set_In a (set_union x y).
Proof. apply set_union_intro.
Qed.

Lemma set_union_elim :
  forall (a:A) (x y:set A),
    set_In a (set_union x y) -> set_In a x \/ set_In a y.
Proof. apply set_union_elim.
Qed.

Lemma set_union_emptyL :
  forall (a:A) (x:set A), set_In a (set_union empty_set x) -> set_In a x.
Proof. apply set_union_emptyL.
Qed.

Lemma set_union_emptyR :
  forall (a:A) (x:set A), set_In a (set_union x empty_set) -> set_In a x.
Proof. apply set_union_emptyR.
Qed.

Lemma set_inter_intro :
  forall (a:A) (x y:set A),
    set_In a x -> set_In a y -> set_In a (set_inter x y).
Proof. apply set_inter_intro.
Qed.

Lemma set_inter_elim1 :
  forall (a:A) (x y:set A), set_In a (set_inter x y) -> set_In a x.
Proof. apply set_inter_elim1.
Qed.

Lemma set_inter_elim2 :
  forall (a:A) (x y:set A), set_In a (set_inter x y) -> set_In a y.
Proof. apply set_inter_elim2.
Qed.

Lemma set_inter_elim :
 forall (a:A) (x y:set A),
   set_In a (set_inter x y) -> set_In a x /\ set_In a y.
Proof. apply set_inter_elim.
Qed.

Lemma set_diff_intro :
 forall (a:A) (x y:set A),
   set_In a x -> ~ set_In a y -> set_In a (set_diff x y).
Proof. apply set_diff_intro.
Qed.

Lemma set_diff_elim1 :
 forall (a:A) (x y:set A), set_In a (set_diff x y) -> set_In a x.
Proof. apply set_diff_elim1.
Qed.

Lemma set_diff_elim2 :
 forall (a:A) (x y:set A), set_In a (set_diff x y) -> ~ set_In a y.
Proof. apply set_diff_elim2.
Qed.

Lemma set_diff_trivial : forall (a:A) (x:set A), ~ set_In a (set_diff x x).
Proof. apply set_diff_trivial.
Qed.

End DS.

Section DS_sequel.

Context `{DS:DecidableType}.

Fixpoint set_remove (a:A) (x:set A) : set A :=
  match x with
  | nil => empty_set
  | cons a1 x1 =>
      match DS_decide a a1 with
      | left _ => set_remove a x1
      | right _ => cons a1 (set_remove a x1)
      end
  end.

Definition set_test_empty (x : set A) :=
  match x with
  | nil => true
  | cons a x' => false
  end.

Definition set_filter : (A -> bool) -> set A -> set A := List.filter (A:=A).

Definition set_size_bound : set A -> nat := List.length (A:=A).

Lemma set_remove_decrease : forall (x:set A) (a:A),
  set_size_bound (set_remove a x) <= set_size_bound x.
Proof.
  intros x. induction x; intros.
  - constructor.
  - simpl. destruct (DS_decide a0 a).
    apply le_S. apply IHx.
    simpl. apply le_n_S. apply IHx.
Qed.

Function set_size (x :set A) {measure set_size_bound} :=
  match x with
  | nil => 0
  | cons a x' => 1+set_size(set_remove a x')
  end.
Proof.
  intros.
  simpl. apply le_n_S.
  apply set_remove_decrease.
Defined.

Lemma set_not_empty_In : forall (x:set A), set_test_empty x = false <->
  exists a, set_In a x.
Proof.
  split; intros. destruct x.
  inversion H. exists a. simpl. left; reflexivity.
  inversion H as [a H0]. destruct x. inversion H0.
  reflexivity.
Qed.

Lemma set_empty_not_In : forall (x:set A), set_test_empty x = true <->
  forall a, ~ set_In a x.
Proof.
  split; intros. destruct x.
  intros contra. inversion contra.
  inversion H.
  destruct x. reflexivity.
  exfalso. apply (H a). simpl; left; reflexivity.
Qed.

Lemma set_filter_In : forall (x:set A) (f:A -> bool) (a:A),
  set_In a (set_filter f x) <-> set_In a x /\ f a = true.
Proof.
  intros.
  unfold set_filter. unfold set_In. apply List.filter_In.
Qed.

Lemma set_bound_0_empty : forall (x : set A),
  set_size_bound x = 0 -> set_test_empty x = true.
Proof. intros.
  destruct x.
  reflexivity.
  inversion H.
Qed.

Lemma set_bound_1_singleton : forall (x : set A),
  set_size_bound x = 1 -> exists a, set_In a x /\
    forall a', set_In a' x -> a = a'.
Proof.
  intros. destruct x.
  inversion H. destruct x.
  exists a. split. simpl. left; reflexivity.
  intros. inversion H0. assumption. inversion H1.
  inversion H.
Qed.

Lemma set_size_le_set_bound : forall (x:set A),
  set_size x <= set_size_bound x.
Proof. intros.
  functional induction (set_size x).
  apply le_n. simpl.
  apply le_n_S. transitivity (set_size_bound (set_remove a x')).
  assumption. apply set_remove_decrease.
Qed.

Lemma set_size_0_empty : forall (x:set A),
  set_size x = 0 -> set_test_empty x = true.
Proof.
  intros.
  destruct x. reflexivity.
  rewrite set_size_equation in H. inversion H.
Qed.

Lemma set_remove_not_In : forall a x b,
  set_In b (set_remove a x) <-> set_In b x /\ b <> a.
Proof.
  intros a x. revert a.
  induction x.
  - split; intros.
    + inversion H.
    + destruct H. inversion H.
  - split; intros.
    + simpl in H. destruct (DS_decide a0 a).
      * apply IHx in H. split. simpl; right. apply H. apply H. 
      * simpl in H. destruct H.
        subst. split. simpl; left; reflexivity. auto. apply IHx in H.
        split. simpl; right. apply H. apply H.
    + destruct H. simpl in H. simpl. destruct H. destruct (DS_decide a0 a).
      subst. exfalso. apply H0; reflexivity.
      subst. simpl; left; reflexivity.
      destruct (DS_decide a0 a).
      apply IHx. split; assumption.
      simpl. right. apply IHx. split; assumption.
Qed.

Lemma set_size_1_singleton : forall (x : set A),
  set_size x = 1 -> exists a, set_In a x /\
    forall a', set_In a' x -> a = a'.
Proof.
  intros. destruct x.
  inversion H.
  destruct x. exists a. split. simpl; left; reflexivity.
  intros. inversion H0. assumption.
  inversion H1.
  rewrite set_size_equation in H. apply eq_add_S in H.
  apply set_size_0_empty in H. rewrite set_empty_not_In in H.
  exists a.
  split.
  simpl. left; reflexivity.
  intros. simpl in H0. destruct H0.
  assumption.
  simpl in H.
  destruct (DS_decide a a0).
  destruct H0. subst; reflexivity.
  destruct (DS_decide a a'). assumption.
  pose proof (H a'). contradiction H1. apply set_remove_not_In.
  split. assumption. auto.
  pose proof (H a0). contradiction H1. simpl; left; reflexivity.
Qed.

Lemma set_size_ge_1_In : forall (x:set A),
  set_size x >= 1 <-> exists a, set_In a x.
Proof.
  split; intros. destruct x.
  inversion H. exists a. simpl; left; reflexivity.
  inversion H as [a H0].
  destruct x. inversion H0. rewrite set_size_equation.
  apply le_n_S. apply le_0_n.
Qed.

Lemma set_size_not_In_remove_aux : forall (a:A) (x:set A),
  (~ set_In a x -> set_size (set_remove a x) = set_size x) /\
  (set_In a x -> set_size (set_remove a x) = set_size x - 1).
Proof.
  intros a x.
  remember (length x) as n.
  assert(length x <= n). rewrite Heqn; apply le_n.
  clear Heqn. revert a x H.
  induction n; intros.
  - destruct x; now inversion H.
  - destruct x; try now inversion H.
    simpl in H. apply le_S_n in H.
    split; intros.
    + simpl. destruct (DS_decide a a0).
      contradiction H0. subst. simpl; left; reflexivity.
      assert(~ set_In a x). { intros contra. apply H0. simpl; right; assumption. }
      rewrite set_size_equation.
      symmetry. rewrite set_size_equation.
      f_equal.
      pose proof (set_In_dec a0 x).
      destruct H2. assert(set_In a0 (set_remove a x)).
      { apply set_remove_not_In. split; auto. }
      apply IHn in s. apply IHn in H2.
      rewrite s. rewrite H2. f_equal. symmetry. apply IHn; assumption.
      rewrite set_remove_decrease. assumption. assumption.
      assert (~set_In a0 (set_remove a x)).
      { intros contra. apply n1. apply set_remove_not_In in contra.
        apply contra. }
      apply IHn in n1. apply IHn in H2.
      rewrite n1. rewrite H2. symmetry. apply IHn; assumption.
      rewrite set_remove_decrease. assumption. assumption.
    + simpl. destruct (DS_decide a a0).
      symmetry. rewrite set_size_equation. simpl. symmetry. subst.
      apply Minus.minus_n_O.
      rewrite set_size_equation. symmetry. rewrite set_size_equation.
      simpl. rewrite <- Minus.minus_n_O.
      destruct H0. symmetry in H0; contradiction.
      pose proof (set_In_dec a0 x).
      destruct H1. assert(set_In a0 (set_remove a x)).
      { apply set_remove_not_In. split; auto. }
      pose proof H1.
      apply IHn in s. apply IHn in H1.
      rewrite s. rewrite H1.
      apply IHn in H0. rewrite <- H0.
      assert(set_size (set_remove a x) >= 1).
      { apply set_size_ge_1_In. exists a0. assumption. }
      destruct (set_size (set_remove a x)). inversion H3.
      simpl. f_equal. apply Minus.minus_n_O.
      assumption. rewrite set_remove_decrease.
      assumption. assumption.
      assert(~set_In a0 (set_remove a x)).
      { intros contra. apply n1. apply set_remove_not_In in contra.
        apply contra. }
      apply IHn in n1. apply IHn in H1.
      rewrite n1. rewrite H1.
      assert (set_size x >= 1). { apply set_size_ge_1_In.
        exists a; assumption. }
      apply IHn in H0. rewrite H0.
      destruct (set_size x). inversion H2. simpl. f_equal.
      apply Minus.minus_n_O. assumption.
      rewrite set_remove_decrease. assumption. assumption.
Qed.

Lemma set_size_not_In_remove : forall (a:A) (x:set A),
  ~ set_In a x -> set_size (set_remove a x) = set_size x.
Proof.
  intros a x. intros. assert(set_remove a x = x).
  induction x. reflexivity.
  simpl. destruct (DS_decide a a0). contradiction H. subst; simpl; left; reflexivity.
  rewrite IHx. reflexivity. intros contra. apply H. simpl; right; assumption.
  rewrite H0. reflexivity.
Fail simpl. (* no more subgoals *)
Abort.

Lemma set_size_not_In_remove : forall (a:A) (x:set A),
  ~ set_In a x -> set_size (set_remove a x) = set_size x.
Proof. apply set_size_not_In_remove_aux.
Qed.

Lemma set_size_In_remove : forall (a:A) (x:set A),
  set_In a x -> set_size (set_remove a x) = set_size x - 1.
Proof.
  intros a x. remember (length x) as n.
  assert(length x <= n). rewrite Heqn; apply le_n.
  clear Heqn. revert a x H.
  induction n; intros.
  - destruct x; now inversion H.
  - destruct x; try now inversion H.
    simpl in H. apply le_S_n in H.
    simpl. symmetry. rewrite set_size_equation. destruct (DS_decide a a0).
    + symmetry. subst. apply Minus.minus_n_O.
    + symmetry. rewrite set_size_equation.
      destruct (set_In_dec a0 x) as [H1|H1].
      * { rewrite 3!IHn; try assumption.
        - destruct (set_size x) eqn:Heqsize.
          + apply set_size_0_empty in Heqsize.
            rewrite set_empty_not_In in Heqsize. specialize (Heqsize a0).
            contradiction.
          + destruct n1.
            * { inversion H0.
              - symmetry in H2; contradiction.
              - apply set_size_1_singleton in Heqsize.
                destruct Heqsize as (a1 & H3 & H4).
                apply H4 in H2. apply H4 in H1. subst. contradiction. }
            * simpl. f_equal. symmetry. apply Minus.minus_n_O.
        - inversion H0. symmetry in H2; contradiction.
          assumption.
        - rewrite set_remove_decrease. assumption.
        - apply set_remove_not_In. split. assumption. auto. }
      * rewrite set_size_not_In_remove. symmetry.
        rewrite set_size_not_In_remove. symmetry.
        simpl. rewrite IHn; try assumption.
        destruct (set_size x) eqn:Heqsize.
        apply set_size_0_empty in Heqsize.
        rewrite set_empty_not_In in Heqsize. pose proof (Heqsize a).
        inversion H0. subst. contradiction n0; reflexivity.
        contradiction. simpl. symmetry. f_equal. apply Minus.minus_n_O.
        inversion H0. subst. contradiction n0; reflexivity.
        assumption.
        assumption.
        intros contra. apply H1. apply set_remove_not_In in contra.
        apply contra.
Fail Fail Qed.
Abort.

Lemma set_size_In_remove : forall (a:A) (x:set A),
  set_In a x -> set_size (set_remove a x) = set_size x - 1.
Proof. apply set_size_not_In_remove_aux.
Qed.

End DS_sequel.

Section DS_sequel_map. (* set_add_intro needed for another type than A *)

Context {A B} {DS:DecidableType A} {DS':DecidableType B}.

Definition set_map (f:A -> B) : set A -> set B := set_map DS_decide f.

Lemma set_map_In : forall (x:set A) (f:A->B) (b:B),
  set_In b (set_map f x) <-> exists a, set_In a x /\ b = f a.
Proof.
  split; intros.
  - induction x.
    + simpl in H. inversion H.
    + simpl in H. apply set_add_elim in H.
      destruct H.
      * exists a. split. simpl. left; reflexivity. rewrite H; reflexivity.
      * apply IHx in H. inversion H as [a0 [H0 H1]].
        exists a0. split. simpl. right; assumption. assumption.
  - inversion H as [a0 [H0 H1]]; clear H. induction x.
    + inversion H0.
    + simpl. fold set_add. apply set_add_intro. simpl in H0.
      destruct H0.
      * subst. left; reflexivity.
      * right; apply IHx; assumption.
Qed.

End DS_sequel_map.

Global Opaque set.
Global Opaque empty_set.
Global Opaque set_add.
Global Opaque set_mem.
Global Opaque set_remove.
Global Opaque set_inter.
Global Opaque set_union.
Global Opaque set_diff.
Global Opaque set_In.
Global Opaque set_test_empty.
Global Opaque set_filter.
Global Opaque set_size_bound.

Notation "x '\cup' y" := (set_union x y) (right associativity, at level 63).
Notation "x '∪' y" := (set_union x y) (right associativity, at level 63).
Notation "x '\cap' y" := (set_inter x y) (right associativity, at level 62).
Notation "x '∩' y" := (set_inter x y) (right associativity, at level 62).
Notation "x '\' y" := (set_diff x y) (left associativity, at level 61).
Notation "a '\in' x" := (set_In a x) (at level 75).
Notation "a '∈' x" := (set_In a x) (at level 75).
Notation "a '\in?' x" := (set_mem a x) (at level 68).
Notation "a '∈?' x" := (set_mem a x) (at level 68).
Notation "'\emptyset'" := empty_set.
Notation "'∅'" := empty_set.
Notation "a '\oplus' x" := (set_add a x) (at level 65).
Notation "a '⊕' x" := (set_add a x) (at level 65).

Section theorems.

Context `{DS : DecidableType}.

(* from list *)
Definition set_incl (x y : set A) := forall a : A, a \in x -> a \in y.
Definition set_same (x y : set A) := set_incl x y /\ set_incl y x.

Definition set_singleton (a:A) := set_add a empty_set.

Lemma set_incl_refl : forall (x:set A), set_incl x x.
Proof.
  unfold set_incl. intros. assumption.
Qed.

Lemma set_incl_trans : forall (x y z : set A), set_incl x y -> set_incl y z -> set_incl x z.
Proof.
  unfold set_incl. intros.
  apply H0; apply H; assumption.
Qed.

Lemma set_inter_not_mem_empty : forall (x:set A) (a:A),
  ~ set_In a x -> set_same (set_inter (set_singleton a) x) empty_set.
Proof.
  intros. unfold set_same. unfold set_incl.
  split; intros.
  - apply set_inter_elim in H0. destruct H0.
    unfold set_singleton in H0.
    apply set_add_elim in H0.
    destruct H0.
    + subst. contradiction.
    + inversion H0.
  - inversion H0.
Qed.

Lemma set_inter_mem_singleton : forall (x:set A) (a:A),
  set_In a x -> set_same (set_inter (set_singleton a) x) (set_singleton a).
Proof.
  intros. unfold set_same. unfold set_incl.
  split; intros.
  - apply set_inter_elim in H0. destruct H0.
    unfold set_singleton in H0.
    apply set_add_elim in H0.
    destruct H0.
    + subst. apply set_add_intro2; reflexivity.
    + inversion H0.
  - inversion H0.
    + subst. apply set_inter_intro; assumption.
    + inversion H1.
Qed.

Lemma set_same_union_empty_l : forall (x : set A),
  set_same (set_union empty_set x) x.
Proof.
  intros. unfold set_same.
  unfold set_incl; split; intros.
  apply set_union_emptyL in H. apply H.
  apply set_union_intro2. assumption.
Qed.

Lemma set_same_union_empty_r : forall (x : set A),
  set_same (set_union x empty_set) x.
Proof.
  intros. unfold set_same.
  unfold set_incl; split; intros.
  apply set_union_emptyR in H. apply H.
  apply set_union_intro1. assumption.
Qed.

Lemma set_inter_union_distr_l : forall (x y z:set A),
  set_same (set_inter (set_union y z) x) (set_union (set_inter y x)
                                               (set_inter z x)).
Proof.
  intros. unfold set_same. unfold set_incl. split; intros.
  - apply set_inter_elim in H. destruct H.
    apply set_union_elim in H. apply set_union_intro.
    destruct H; [ left | right]; apply set_inter_intro; assumption.
  - apply set_union_elim in H.
    destruct H; apply set_inter_elim in H; destruct H; (apply set_inter_intro;
      [ apply set_union_intro1 + apply set_union_intro2 | ]); assumption.
Qed.

Lemma set_union_In : forall `{DS : DecidableType} (a : A) (x y : set A),
  a \in x \cup y <-> a \in x \/ a \in y.
Proof.
  split.
  - apply set_union_elim.
  - apply set_union_intro.
Qed.

Lemma set_inter_In : forall `{DS : DecidableType} (a : A) (x y : set A),
  a \in x \cap y <-> a \in x /\ a \in y.
Proof.
  split.
  - apply set_inter_elim.
  - intros. destruct H. apply set_inter_intro; assumption.
Qed.

Lemma set_union_assoc : forall (x y z : set A),
  set_same ((x \cup y) \cup z) (x \cup y \cup z).
Proof.
  intros.
  unfold set_same, set_incl; split; intros;
    rewrite 2!set_union_In in H; rewrite 2!set_union_In;
    apply or_assoc; assumption.
Qed.

Lemma set_union_comm : forall (x y : set A),
  set_same (x \cup y) (y \cup x).
Proof.
  intros.
  unfold set_same. unfold set_incl. split; intros;
   apply set_union_elim in H; apply set_union_intro; apply or_comm; assumption.
Qed.

Lemma set_inter_comm : forall (x y : set A),
  set_same (set_inter x y) (set_inter y x).
Proof.
  intros.
  unfold set_same. unfold set_incl. split; intros;
    apply set_inter_elim in H; apply set_inter_intro; apply H.
Qed.

Lemma set_inter_incl : forall x y z,
  set_incl x z -> set_incl (set_inter x y) z.
Proof.
  intros.
  unfold set_incl; intros. apply set_inter_elim in H0. destruct H0.
  apply H. assumption.
Qed.

Lemma set_incl_inter : forall x y z,
  set_incl x y -> set_incl x z -> set_incl x (set_inter y z).
Proof.
  intros. unfold set_incl; intros.
  apply set_inter_intro. apply H; assumption. apply H0; assumption.
Qed.

Lemma set_inter_same : forall x y,
  set_incl x y -> set_same (set_inter x y) x.
Proof.
  intros. unfold set_same; split.
  apply set_inter_incl. apply set_incl_refl.
  apply set_incl_inter. apply set_incl_refl. assumption.
Qed. 

(* it seems like the definition of set_union... *)
Lemma set_same_union_add_singleton : forall (a:A) (x:set A),
  set_same (set_union (set_singleton a) x) (set_add a x).
Proof.
  intros. unfold set_same. unfold set_incl. split; intros.
  - apply set_union_elim in H. destruct H.
    + unfold set_singleton in H. apply set_add_elim in H.
      destruct H.
      * subst; apply set_add_intro2; reflexivity.
      * inversion H.
    + apply set_add_intro1. assumption.
  - apply set_add_elim in H. apply set_union_intro.
    destruct H.
    + subst. left. unfold set_singleton. apply set_add_intro2; reflexivity.
    + right; assumption.
Qed.

Lemma set_test_empty_correct : forall (x:set A),
  set_test_empty x = true <-> set_same x empty_set.
Proof.
  split; intros.
  - unfold set_same; unfold set_incl; split; intros.
    absurd (set_In a x). apply set_empty_not_In. assumption.
    assumption.
    inversion H0.
  - destruct (set_test_empty x) eqn:Heqset.
    + reflexivity.
    + apply set_not_empty_In in Heqset. inversion Heqset. apply H in H0.
      inversion H0.
Qed.

Lemma set_test_empty_complete : forall (x:set A),
  set_test_empty x = false <-> ~ set_same x empty_set.
Proof.
  split; intros.
  intros contra. apply Bool.not_true_iff_false in H.
  apply H. apply set_test_empty_correct; assumption.
  apply Bool.not_true_iff_false. intros contra. apply H.
  apply set_test_empty_correct; assumption.
Qed.

Lemma set_singleton_In : forall (a a' : A),
  set_In a' (set_singleton a) <-> a' = a.
Proof. unfold set_singleton.
  split; intros.
  apply set_add_elim in H. destruct H.
  subst; reflexivity. inversion H.
  subst. apply set_add_intro2. reflexivity.
Qed.

Lemma set_same_bound_1_singleton : forall (x:set A),
  set_size_bound x = 1 -> exists a, set_same x (set_singleton a).
Proof.
  intros. apply set_bound_1_singleton in H.
  inversion H as [a H0].
  exists a. destruct H0.
  unfold set_same; unfold set_incl; split; intros.
  apply H1 in H2. subst. apply set_singleton_In; reflexivity.
  apply set_singleton_In in H2; subst. assumption.
Qed.

Lemma set_diff_incl : forall x y, set_incl (set_diff x y) x.
Proof. unfold set_incl; intros.
  apply set_diff_elim1 in H. assumption.
Qed.

Lemma set_incl_union : forall x y z, set_incl x z -> set_incl y z ->
  set_incl (x \cup y) z.
Proof.
  intros.
  unfold set_incl; intros.
  rewrite set_union_In in H1. destruct H1. apply H; assumption.
  apply H0; assumption.
Qed.

Lemma set_diff_emptyset_l : forall x, set_same (set_diff \emptyset x) \emptyset.
Proof.
  intros. unfold set_same, set_incl; split; intros.
  - apply set_diff_elim1 in H. inversion H.
  - inversion H.
Qed.

Lemma set_diff_emptyset_r : forall x, set_same (set_diff x \emptyset) x.
Proof.
  intros. unfold set_same, set_incl; split; intros.
  - apply set_diff_elim1 in H; assumption.
  - apply set_diff_intro.
    + assumption.
    + intros contra; inversion contra.
Qed.

Lemma set_diff_same : forall x, set_same (set_diff x x) \emptyset.
Proof.
  intros. unfold set_same, set_incl; split; intros.
  - pose proof (set_diff_trivial a x). contradiction.
  - inversion H.
Qed.

Lemma set_diff_union : forall x y, set_same (set_diff x y \cup y) (x \cup y).
Proof.
  intros. unfold set_same, set_incl; split; intros.
  - rewrite set_union_In. rewrite set_union_In in H.
    destruct H. apply set_diff_elim1 in H; left; assumption.
    right; assumption.
  - rewrite set_union_In in H. rewrite set_union_In.
    destruct H. destruct (set_In_dec a y). right; assumption.
    left. apply set_diff_intro; assumption.
    right; assumption.
Qed.

Lemma set_diff_empty : forall x y, set_same (set_diff x y) \emptyset <-> set_incl x y.
Proof.
  split; intros.
  - unfold set_incl; intros. destruct (set_In_dec a y).
    + assumption.
    + assert (~ a \in \emptyset). { intros contra. inversion contra. }
      contradiction H1. apply H. apply set_diff_intro; assumption.
  - unfold set_same, set_incl; split; intros.
    + pose proof H0. apply set_diff_elim1 in H0. apply set_diff_elim2 in H1.
      apply H in H0. contradiction.
    + inversion H0.
Qed.

Lemma set_diff_union_distr_r : forall x y z,
  set_same (set_diff x (y \cup z)) (set_diff x y \cap set_diff x z).
Proof.
  intros. unfold set_same, set_incl; split; intros.
  - rewrite set_inter_In. split.
    + apply set_diff_intro.
      * apply set_diff_elim1 in H; assumption.
      * apply set_diff_elim2 in H. intros contra. apply H. rewrite set_union_In.
        left; assumption.
    + apply set_diff_intro.
      * apply set_diff_elim1 in H; assumption.
      * apply set_diff_elim2 in H. intros contra. apply H. rewrite set_union_In.
        right; assumption.
  - rewrite set_inter_In in H. destruct H.
    apply set_diff_intro.
    + apply set_diff_elim1 in H. assumption.
    + intros contra. rewrite set_union_In in contra. destruct contra.
      * apply set_diff_elim2 in H; contradiction.
      * apply set_diff_elim2 in H0; contradiction.
Qed.

Lemma set_diff_union_distr_l : forall x y z,
  set_same ((x \cup y) \ z) (x \ z \cup y \ z).
Proof.
  intros.
  unfold set_same, set_incl; split; intros.
  - rewrite set_union_In. pose proof H. apply set_diff_elim1 in H.
    apply set_diff_elim2 in H0. apply set_union_In in H. destruct H.
    + left. apply set_diff_intro; assumption.
    + right. apply set_diff_intro; assumption.
  - rewrite set_union_In in H. destruct H.
    + apply set_diff_intro.
      * rewrite set_union_In; left. apply set_diff_elim1 in H; assumption.
      * apply set_diff_elim2 in H; assumption.
    + apply set_diff_intro.
      * rewrite set_union_In; right. apply set_diff_elim1 in H; assumption.
      * apply set_diff_elim2 in H; assumption.
Qed.

Lemma set_diff_In : forall x y a, a \in set_diff x y <-> a \in x /\ ~ a \in y.
Proof.
  split; intros.
  - split.
    + apply set_diff_elim1 in H; assumption.
    + apply set_diff_elim2 in H; assumption.
  - apply set_diff_intro; apply H.
Qed.

End theorems.

Notation "x '\equiv' y" := (set_same x y) (at level 70).
Notation "x '≡' y" := (set_same x y) (at level 70).
Notation "'\sin' a" := (set_singleton a) (at level 55).
Notation "'〈' a '〉'" := (set_singleton a) (at level 55, format "'〈' a '〉'").
Notation "x '\subseteq' y" := (set_incl x y) (at level 70).
Notation "x '⊆' y" := (set_incl x y) (at level 70).

Section equivalence.

(* Morphisms: https://coq.inria.fr/refman/Reference-Manual029.html *)

Context `{DS:DecidableType}.

Lemma set_same_refl : forall (x:set A), x \equiv x.
Proof.
  intros. split; apply set_incl_refl.
Qed.

Lemma set_same_sym : forall (x y:set A), x \equiv y -> y \equiv x.
Proof. unfold set_same.
  intros. apply and_comm. assumption.
Qed.

Lemma set_same_trans : forall (x y z:set A), x \equiv y ->
  y \equiv z -> x \equiv z.
Proof. unfold set_same.
  intros. destruct H, H0. split;
  apply (set_incl_trans _ y); assumption.
Qed.

Global Add Parametric Relation : (set A) set_same
  reflexivity proved by set_same_refl
  symmetry proved by set_same_sym
  transitivity proved by set_same_trans as set_same_rel.

Global Add Parametric Morphism : set_add
  with signature eq ==> set_same ==> set_same as set_same_add.
Proof.
  intros. unfold set_same; unfold set_incl. split; intros.
  - apply set_add_elim in H0. apply set_add_intro.
    destruct H0.
    + left; assumption.
    + right. apply H. assumption.
  - apply set_add_elim in H0. apply set_add_intro.
    destruct H0.
    + left; assumption.
    + right. apply H. assumption.
Qed.

Global Add Parametric Morphism : set_incl
  with signature set_same ==> set_same ==> iff as set_same_set_incl.
Proof.
  unfold set_same.
  split; intros.
  apply (set_incl_trans _ x). apply H. apply (set_incl_trans _ x0).
  apply H1. apply H0.
  apply (set_incl_trans _ y). apply H. apply (set_incl_trans _ y0).
  apply H1. apply H0.
Qed.

Global Add Parametric Morphism : set_union
  with signature (set_same ==> set_same ==> set_same) as set_same_union.
Proof.
  intros. unfold set_same; unfold set_incl.
  split; intros; apply set_union_elim in H1; apply set_union_intro;
    (destruct H1;
      [ left; apply H; assumption | right; apply H0; assumption ]).
Qed.

Global Add Parametric Morphism : set_inter
  with signature set_same ==> set_same ==> set_same as set_same_inter.
Proof.
  intros. split; intros; unfold set_incl; intros;
    apply set_inter_elim in H1; destruct H1; apply H in H1; apply H0 in H2;
    apply set_inter_intro; assumption.
Qed.

Global Add Parametric Morphism : set_size
  with signature set_same ==> eq as set_same_size.
Proof.
  intros. remember (set_size x) as n. symmetry in Heqn. symmetry.
  revert x y H Heqn.
  induction n; intros.
  apply set_size_0_empty in Heqn.
  assert(~set_size y >= 1). intros contra. apply set_size_ge_1_In in contra.
  inversion contra as [a H0]. apply set_test_empty_correct in Heqn.
  apply H in H0. apply Heqn in H0. inversion H0.
  apply Compare_dec.not_ge in H0. destruct (set_size y).
  reflexivity. inversion H0. inversion H2.
  assert(set_size x >= 1). rewrite Heqn. apply le_n_S. apply le_0_n.
  apply set_size_ge_1_In in H0.
  inversion H0 as [a H1].
  assert(set_size (set_remove a x) = n). rewrite set_size_In_remove.
  rewrite Heqn. simpl. symmetry. apply Minus.minus_n_O.
  assumption.
  assert (set_same (set_remove a x) (set_remove a y)).
  unfold set_same; unfold set_incl; split; intros.
  apply set_remove_not_In.   apply set_remove_not_In in H3.
  destruct H3. split. apply H. assumption. assumption.
  apply set_remove_not_In.   apply set_remove_not_In in H3.
  destruct H3. split. apply H. assumption. assumption.
  apply IHn in H3. rewrite set_size_In_remove in H3.
  apply eq_S in H3.
  destruct (set_size y) eqn:Heqsize. apply set_size_0_empty in Heqsize.
  apply set_test_empty_correct in Heqsize. apply H in H1. apply Heqsize in H1.
  inversion H1. simpl in H3. rewrite <- Minus.minus_n_O in H3. assumption.
  apply H. assumption.
  assumption.
Qed.

Global Add Parametric Morphism : set_In
  with signature eq ==> set_same ==> iff as set_same_In.
Proof.
  split; intros; apply H; assumption.
Qed.

Lemma set_same_In_iff : forall `{DecidableType} (x y:set A),
  x \equiv y <-> (forall a, a \in x <-> a \in y).
Proof.
  split; intros.
  - rewrite H0. reflexivity.
  - unfold set_same, set_incl; split; intros; apply H0; assumption.
Qed.

Global Add Parametric Morphism : set_filter
  with signature eq ==> set_same ==> set_same as set_same_filter.
Proof.
  intros.
  apply set_same_In_iff; intros.
  rewrite 2!set_filter_In.
  rewrite H. reflexivity.
Qed.

Global Add Parametric Morphism : set_test_empty
  with signature set_same ==> eq as set_same_test_empty.
Proof.
  intros. destruct (set_test_empty x) eqn:Heqempty.
  - apply set_test_empty_correct in Heqempty. rewrite H in Heqempty.
    apply set_test_empty_correct in Heqempty. symmetry. assumption.
  - apply set_test_empty_complete in Heqempty. rewrite H in Heqempty.
    apply set_test_empty_complete in Heqempty. symmetry. assumption.
Qed.

Global Add Parametric Morphism : set_diff
  with signature set_same ==> set_same ==> set_same as set_same_diff.
Proof.
  intros. apply set_same_In_iff; intros. split; intros.
  - apply set_diff_intro.
    + apply H. apply set_diff_elim1 in H1; assumption.
    + rewrite <- H0. apply set_diff_elim2 in H1; assumption.
  - apply set_diff_intro.
    + apply H. apply set_diff_elim1 in H1; assumption.
    + rewrite H0. apply set_diff_elim2 in H1; assumption.
Qed.

End equivalence.

Section equivalence_map.

Context {A B} {DS:DecidableType A} {DS':DecidableType B}.

Global Add Parametric Morphism : (set_map (A:=A) (B:=B))
  with signature eq ==> set_same ==> set_same as set_same_map.
Proof.
  intros.
  apply set_same_In_iff; intros.
  rewrite 2!set_map_In.
  split; intros.
  - destruct H0 as [a0 [H0 H1]].
    exists a0. split.
    + rewrite <- H. assumption.
    + assumption.
  - destruct H0 as [a0 [H0 H1]].
    exists a0. split.
    + rewrite H. assumption.
    + assumption.
Qed.

End equivalence_map.
