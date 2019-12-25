Require Import List. Import ListNotations.
Require Import Arith.
Require Import Psatz.

(* B and B2 are the naive and the second implementations respectively.
   Predicate is_eq relates buffers in the first implementation (B)
   and in the second one (B2).
*)

Fixpoint take {A} n (xs:list A) :=
  match n, xs with
  | 0, _ | _, [] => []
  | S n, x::xs => x::take n xs
  end.

Module Type Buf.
  Parameter buf : Type -> Type.
  Parameter empty : forall {A}, nat -> buf A.
  Parameter add : forall {A}, A -> buf A -> buf A.
  Parameter get : forall {A}, buf A -> list A.
End Buf.

Module B <: Buf.
  Record buf_aux A := {
    h : nat;
    xs : list A
  }.
  Arguments h {_}.
  Arguments xs {_}.
  Definition buf A := buf_aux A.
  Definition empty {A} h : buf A :=
    {|h:=h; xs:=[]|}.
  Definition add {A} (x:A) (b:buf A) : buf A :=
    {|h:=h b; xs:=x::xs b|}.
  Definition get {A} (b:buf A) :=
    take (h b) (xs b).
End B.

Module B2 <: Buf.
  Record buf_aux A := {
    h : nat;
    xs : list A;
    xs_len : nat;
    ys : list A
  }.
  Arguments h {_}.
  Arguments xs {_}.
  Arguments xs_len {_}.
  Arguments ys {_}.
  Definition buf := buf_aux.
  Definition empty {A} h : buf A :=
    {|h:=h; xs:=[]; xs_len:=0; ys:=[]|}.
  Definition add {A} x (b:buf A) :=
    match b with
    {| h := h; xs := xs; xs_len := xs_len; ys := ys|} => 
    if Nat.eqb xs_len (h - 1) then {|h:=h; xs:=[]; xs_len:=0; ys:=x::xs|}
                          else {|h:=h; xs:=x::xs; xs_len:=xs_len+1; ys:=ys|}
    end.
  Definition get {A} (b:buf A) :=
    match b with
    {| h := h; xs := xs; xs_len := xs_len; ys := ys|} =>
    take h (xs++ys)
    end.
End B2.

Definition is_well_formed {A} (b2:B2.buf A) :=
  B2.xs_len b2 = List.length (B2.xs b2). (* /\
  B2.xs_len b2 <= B2.h b2 - 1. *)

Definition is_eq {A} (b:B.buf A) (b2:B2.buf A) :=
  is_well_formed b2
  /\ B.h b = B2.h b2
  /\ B.get b = B2.get b2.

Lemma empty_eq : forall A n,
  @is_eq A (B.empty n) (B2.empty n).
Proof.
  intros; repeat split; reflexivity.
Qed.

Lemma take_decrease : forall {A} n (l1 l2 : list A),
  take (S n) l1 = take (S n) l2 ->
  take n l1 = take n l2.
Proof.
  intros A n. induction n; intros.
  - reflexivity.
  - destruct l1, l2.
    + reflexivity.
    + discriminate.
    + discriminate.
    + simpl in H. simpl. inversion H. f_equal. auto.
Qed.

Lemma take_too_long : forall {A} n (l1 l2 : list A),
  n <= List.length l1 ->
  take n (l1 ++ l2) = take n l1.
Proof.
  intros A n. induction n; intros.
  - reflexivity.
  - destruct l1; [inversion H|].
    simpl. f_equal. simpl in H. apply le_S_n in H. auto.
Qed.

Lemma add_eq : forall A x (b:B.buf A) b2,
  is_eq b b2 ->
  is_eq (B.add x b) (B2.add x b2).
Proof.
  intros. destruct H as (H & H0 & H1). destruct b, b2.
  unfold B.get in *. unfold is_well_formed in H.
  simpl in *. subst h0. subst.
  destruct (length xs0 =? h - 1) eqn:Heq.
  - repeat split; simpl.
    unfold B.get. simpl. destruct h.
    + reflexivity.
    + simpl; f_equal. apply take_decrease in H1.
      rewrite take_too_long in H1.
      * assumption.
      * rewrite Nat.eqb_eq in Heq. nia.
  - repeat split; simpl.
    + unfold is_well_formed; simpl. Psatz.nia.
    + unfold B.get. simpl. destruct h.
      * reflexivity.
      * simpl; f_equal. apply take_decrease in H1. assumption.
Qed.
