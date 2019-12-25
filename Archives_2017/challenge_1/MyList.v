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

Require Import Vlist.

Lemma app_nth1 : forall {a : Type} {a_WT : WhyType a} (u v : list a) (k : int),
  k < length u -> nth (concat u v) k = nth u k.
Proof.
  intros.
  apply Vlist.nth_concat; assumption.
Qed.

Lemma app_nth2 : forall {a : Type} {a_WT : WhyType a} (u v : list a) (k : int),
  ~ k < length u -> nth (concat u v) k = nth v (k - length u).
Proof.
  intros.
  apply Vlist.nth_concat; assumption.
Qed.

Lemma cons_nth1 :
  forall {a : Type} {a_WT : WhyType a} (x : a) (w : list a),
  nth (cons x w) 0 = x.
Proof.
  intros.
  apply Vlist.nth_cons; reflexivity.
Qed.

Lemma cons_nth2 :
  forall {a : Type} {a_WT : WhyType a} (k : int) (x : a) (w : list a),
  k <> 0 -> nth (cons x w) k = nth w (k - 1).
Proof.
  intros.
  apply Vlist.nth_cons; assumption.
Qed.

Lemma list_dec :
  forall {a : Type} {a_WT : WhyType a} (l : list a),
  l = nil \/ exists h t, l = cons h t.
Proof.
  intros. destruct l.
  - left; reflexivity.
  - right; do 2 eexists; reflexivity.
Qed.

Lemma list_ind :
  forall {a : Type} {a_WT : WhyType a} (P : list a -> Prop),
  P nil ->
  (forall (h : a) (l : list a), P l -> P (cons h l)) ->
  forall l : list a, P l.
Proof.
  intros.
  apply list_ind; assumption.
Qed.