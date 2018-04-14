Require Import List. Import ListNotations.
Require Import Arith. Require Import Bool.
Require Import ListSet.

(* red = true; black = false *)
Fixpoint valid_aux acc (l : list bool) :=
  match l with
  | [] => (acc =? 0) || (3 <=? acc)
  | x :: l => if x then valid_aux (acc+1) l else ((acc =? 0) || (3 <=? acc)) && valid_aux 0 l
  end.

Definition valid l := valid_aux 0 l.

Definition set_filter {A} : (A -> bool) -> set A -> set A := List.filter (A:=A).

Fixpoint enumerate_all n : set (list bool) :=
  match n with
  | 0 => empty_set (list bool)
  | S n => let s := enumerate_all n in
           set_union (list_eq_dec bool_dec)
             (set_map (list_eq_dec bool_dec) (fun l => true::l) s)
             (set_map (list_eq_dec bool_dec) (fun l => false::l) s)
  end.

Definition enumerate n := set_filter valid (enumerate_all n).

Definition card := List.length.
