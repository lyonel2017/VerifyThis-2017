From mathcomp Require Import all_ssreflect.

Check [tuple [:: 2;1]].

Fixpoint valid_aux acc (l : list bool) :=
  match l with
  | [::] => (acc == 0) || (3 <= acc)
  | x :: l => if x then valid_aux (acc+1) l else ((acc == 0) || (3 <= acc)) && valid_aux 0 l
  end.

Definition valid l := valid_aux 0 l.

Check (10 .-tuple).

Definition a n := [set t : n .-tuple bool | valid t].

Definition count n := #|a n|.

Fixpoint prefix_red s :=
  match s with
  | [::] => [::]
  | true::s' => true::prefix_red s'
  | _ => [::]
  end.

Definition prefix_red_tuple n (t: n .-tuple bool) := prefix_red t.

Fact prim n : partition (preim_partition (prefix_red_tuple n) (a n)) (a n).
Proof. apply preim_partitionP.
Qed.

(*
Lemma zsodsfdpk : forall n, n >= 4 ->
  a n == \bigcup_(0 <= i < n) [set x in (a n) | size (prefix_red x) == n].
Proof.
  intros. Search (_ == _). Search "\in".
  Search ":|:".
  apply bigop_
  rewrite big_ltn.
  Search (\bigcup_ (_ in _) _). admit. disjoint
  card
*)

Lemma terqseq : forall n, n >= 4 ->
  count n = count (n-1) + \sum_(0 <= i < n - 4) (count i) + 1.
Proof.
  intros. unfold count at 1.
  unfold a.
  rewrite (card_partition (prim n)).
  Search "|:".
  rewrite big_setU1.
  assert (\sum_(i <- [::1;2]) (i+1) = 0).
  rewrite big_split.
  
  fold 
  big_mkcond
  mathcomp.ssreflect.bigop
  Search (\sum_(_ in (_ :|: _)) _).
  
partition

Definition equiv t1 t2 := prefix_red t1 = prefix_red t2.
preim_partition
equivalence_partition
partition
Search (set _ |- _).

Locate "[ set _ | _ ]".

Lemma test2 : forall (s:{set bool}) p,
  s == [set x in s | p x] :|: [set x in s| negb (p x)].
Proof.
  intros.
  setU
  Locate "_ :|: _".

SetDef.finset

Definition count_0 : count 0 = 1.
Proof.
  unfold count.
  Search "#| _ |".
  destruct (cards1P (A:=a 0)).
  destruct e. rewrite H. apply cards1.
  contradiction n. exists [tuple].
  simpl.
  
  Search "\in".
  apply in_setT.
  Show Proof.
  compute.
  
  simpl.
  trivial.
Compute #|a|.
card