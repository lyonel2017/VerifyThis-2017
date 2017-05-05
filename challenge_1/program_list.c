// Command: frama-c -wp -wp-rte program.c
// Frama-c version : Silicon (last release)
// The algorithm is proved to sort, but does not ensure the preservation of the elements of the initial array

// swap and same_elements are adapted from http://nikolai.kosmatov.free.fr/publications/tutorial_2013_06_18_tap2013_slides.pdf
// (also in acsl-implementation-Silicon-20161101.pdf)

/*@ axiomatic list_of_array {
      logic \list<integer> list_of_array (int* a, integer n) reads a[0..n-1];
      axiom list_of_array_zero{L} : \forall int* a; list_of_array (a, 0) == [| |];
      axiom list_of_array_pos{L} : \forall int* a, integer n; n > 0 ==>
        list_of_array (a, n) == (list_of_array (a, n-1) ^ [| a[n-1] |]);

      lemma list_of_array_length{L} : \forall int *a, integer n; 0 <= n ==>
        \length (list_of_array (a, n)) == n;
      lemma list_of_array_nth{L} : \forall int *a, integer n, k; 0 <= k < n ==>
        \nth (list_of_array (a, n), k) == a[k];
    }

    axiomatic sub_list {
      logic \list<integer> sub_list (\list<integer> l, integer begin, integer end);
      axiom sub_list_zero : \forall \list<integer> l, integer begin, end;
        begin >= end ==> sub_list (l, begin, end) == [| |];
      axiom sub_list_pos : \forall \list<integer> l, integer begin, end;
        begin < end ==> sub_list (l, begin, end) == (sub_list (l, begin, end-1) ^ [| \nth (l, end-1) |]);
      lemma sub_list_length : \forall \list<integer> l, integer begin, end;
        0 <= begin <= end <= \length (l) ==> \length (sub_list (l, begin, end)) == end - begin;
      lemma sub_list_nth : \forall \list<integer> l, integer begin, end;
        0 <= begin <= end <= \length (l) ==> \forall integer k;
        0 <= k < end-begin ==> \nth (sub_list (l, begin, end), k) == \nth (l, begin+k);
        logic \list<integer> tail (\list<integer> l) = sub_list (l, 1, \length (l));
      lemma tail_length : \forall \list<integer> l;
        0 < \length (l) ==> \length (tail (l)) == \length (l) - 1;
      lemma tail_nth : \forall \list<integer> l; 0 < \length (l) ==>
        \forall integer k; 0 <= k < \length (l) - 1 ==>
        \nth (tail (l), k) == \nth (l, k+1);
      lemma sub_list_split : \forall \list<integer> l, integer i, j;
        0 <= i < j < \length(l) ==>
        l == (sub_list (l, 0, i) ^ [| \nth (l, i) |] ^ sub_list (l, i+1, j) ^ [| \nth (l, j) |] ^ sub_list (l, j+1, \length (l)));
      lemma sub_list_split2 : \forall \list<integer> l, integer begin, i, j, end;
        0 <= begin <= i < j < end <= \length (l) ==>
        sub_list (l, begin, end) == (sub_list (l, begin, i) ^ [| \nth (l, i) |] ^ sub_list (l, i+1, j) ^ [| \nth (l, j) |] ^ sub_list (l, j+1, end));
    }

    axiomatic update {
      logic \list<integer> update (\list<integer> l, integer n, integer v);
      axiom update_zero : \forall \list<integer> l, integer v;
        update (l, 0, v) == \Cons (v, tail (l));
      axiom update_pos : \forall \list<integer> l, integer n, v;
        n > 0 ==>
        update (l, n, v) == \Cons (\nth(l,0), update (tail(l), n-1, v));
      lemma update_length : \forall \list<integer> l, integer n, v;
        0 <= n < \length (l) ==>
        \length (update (l, n, v)) == \length (l);
      lemma update_nth_neq : \forall \list<integer> l, integer n, v, k;
        0 <= n < \length (l) ==>
        0 <= k < \length (l) ==>
        k != n ==>
        \nth (update (l, n, v), k) == \nth (l, k);
      lemma update_nth_eq : \forall \list<integer> l, integer n, v;
        0 <= n < \length (l) ==>
        \nth (update (l, n, v), n) == v;
    }

    predicate same_list (\list<integer> l1, \list<integer> l2, integer begin, integer end) =
      \forall integer k; begin <= k < end ==> \nth (l1, k) == \nth (l2, k);

    axiomatic num_of {
      logic integer num_of (\list<integer> l, integer value);
      axiom num_of_zero : \forall integer value;
        num_of ([| |], value) == 0;
      axiom num_of_pos_eq : \forall \list<integer> l, integer value;
        0 < \length(l) ==> \nth (l, 0) == value ==>
        num_of(l, value) == 1 + num_of (tail(l), value);
      axiom num_of_pos_neq : \forall \list<integer> l, integer value;
        0 < \length(l) ==> \nth (l, 0) != value ==>
        num_of (l, value) == num_of (tail(l), value);
      lemma num_of_split : \forall \list<integer> l1, l2, integer value;
        num_of (l1 ^ l2, value) == num_of (l1, value) + num_of (l2, value);
      lemma num_of_cons : \forall \list<integer> l1, integer x, integer value;
        num_of (\Cons (x, l1), value) == (x == value ? 1 + num_of (l1, value) : num_of (l1, value));
      lemma num_of_non_zero : \forall \list<integer> l, integer value;
        num_of (l, value) > 0 ==>
        \exists integer k; 0 <= k < \length (l) && \nth (l, k) == value;
    }

    predicate same_elements_list (\list<integer> l1, \list<integer> l2) =
      \length (l1) == \length (l2) &&
      \forall integer value; num_of (l1, value) == num_of (l2, value);
    lemma same_elements_list_refl : \forall \list<integer> l1;
      same_elements_list (l1, l1);
    lemma same_elements_list_trans : \forall \list<integer> l1, l2, l3, integer begin, end;
      same_elements_list (l1, l2) ==> same_elements_list (l2, l3) ==>
      same_elements_list (l1, l3);

    predicate swap_list(\list<integer> l1, \list<integer> l2, integer i, integer j) =
      \length(l1) == \length (l2) &&
      0 <= i < j < \length (l1) &&
      \nth (l1, i) == \nth (l2, j) &&
      \nth (l1, j) == \nth (l2, i) &&
      \forall integer k; 0 <= k < \length(l1) && k != i && k != j ==> \nth (l1, k) == \nth (l2, k);
    lemma swap_sym : \forall \list<integer> l1, l2, integer i, j;
      swap_list (l1, l2, i, j) ==> swap_list (l2, l1, i, j);
    lemma swap_split : \forall \list<integer> l1, l2, integer i, j;
        swap_list (l1, l2, i, j) ==>
        l1 == (sub_list (l1, 0, i) ^ [| \nth (l1, i) |] ^ sub_list (l1, i+1, j) ^ [| \nth (l1, j) |] ^ sub_list (l1, j+1, \length(l1)));
    lemma swap_split2 : \forall \list<integer> l1, l2, integer i, j;
        swap_list (l1, l2, i, j) ==>
        l1 == (sub_list (l1, 0, i) ^ [| \nth (l1, i) |] ^ sub_list (l1, i+1, j) ^ [| \nth (l1, j) |] ^ sub_list (l1, j+1, \length(l1))) &&
        l2 == (sub_list (l1, 0, i) ^ [| \nth (l1, j) |] ^ sub_list (l1, i+1, j) ^ [| \nth (l1, i) |] ^ sub_list (l1, j+1, \length(l1)));
    lemma swap_list_same_elements_aux_1 : \forall \list<integer> m1, m2, m3, integer a, b, v;
      num_of (m1 ^ [| a |] ^ m2 ^ [| b |] ^ m3, v) == num_of (m1, v) + num_of ([| a |] ^ m2 ^ [| b |] ^ m3, v);
    lemma swap_list_same_elements_aux_2 : \forall \list<integer> m2, m3, integer a, b, v;
      num_of ([| a |] ^ m2 ^ [| b |] ^ m3, v) == num_of ([| a |], v) + num_of (m2 ^ [| b |] ^ m3, v);
    lemma swap_list_same_elements_aux_3 : \forall \list<integer> m2, m3, integer b, v;
      num_of (m2 ^ [| b |] ^ m3, v) == num_of (m2, v) + num_of ([| b |] ^ m3, v);
    lemma swap_list_same_elements_aux_4 : \forall \list<integer> m2, m3, integer b, v;
      num_of ([| b |] ^ m3, v) == num_of ([| b |], v) + num_of (m3, v);
    lemma swap_list_same_elements_aux : \forall \list<integer> m1, m2, m3, integer a, b;
        same_elements_list (m1 ^ [| a |] ^ m2 ^ [| b |] ^ m3, m1 ^ [| b |] ^ m2 ^ [| a |] ^ m3);
    lemma swap_list_same_elements : \forall \list<integer> l1, l2, integer i, j;
      swap_list (l1, l2, i, j) ==>
      same_elements_list (l1, l2);
    lemma update_swap_list : \forall \list<integer> l1, l2, integer i, j;
      0 <= i < j < \length (l1) ==>
      l2 == update (l1, j, \nth (l1, i)) ==>
      swap_list (l1, update (l2, i, \nth (l1, j)), i, j);
 */

/*@ predicate swap{L1, L2}(int *a, int *b, integer begin, integer i, integer j, integer end) =
      begin <= i < j < end &&
      \at(a[i], L1) == \at(b[j], L2) &&
      \at(a[i], L2) == \at(b[j], L1) &&
      \forall integer k; begin <= k < end && k != i && k != j ==>
        \at(a[k], L1) == \at(b[k], L2);

    predicate same_array{L1,L2}(int *a, int *b, integer begin, integer end) =
      \forall integer k; begin <= k < end ==> \at(a[k],L1) == \at(b[k],L2);

    inductive same_elements{L1, L2}(int *a, int *b, integer begin, integer end) {
      case refl{L1, L2}:
        \forall int *a, int *b, integer begin, end;
        same_array{L1,L2}(a, b, begin, end) ==>
        same_elements{L1, L2}(a, b, begin, end);
      case swap{L1, L2}: \forall int *a, int *b, integer begin, i, j, end;
        swap{L1, L2}(a, b, begin, i, j, end) ==>
        same_elements{L1, L2}(a, b, begin, end);
      case trans{L1, L2, L3}: \forall int* a, int *b, integer begin, end;
        same_elements{L1, L2}(a, b, begin, end) ==>
        same_elements{L2, L3}(a, b, begin, end) ==>
        same_elements{L1, L3}(a, b, begin, end);
    }
*/

/*@ predicate same_array_list{L} (int* a, \list<integer> b, integer begin, integer end) =
      \forall integer k; begin <= k < end ==> a[k] == \nth (b, k);
    lemma same_elements_list_array{L1,L2} : \forall int* a, integer n; 0 <= n ==>
      same_elements_list(list_of_array{L1}(a, n), list_of_array{L2}(a, n)) ==>
      same_elements{L1,L2} (a, a, 0, n);
*/

/* lemma num_of_list_not_zero : \forall \list<integer> a, integer begin, end, value;
      num_of_list (a, begin, end, value) > 0 ==>
      \exists integer k; begin <= k < end && \nth (a, k) == value;
//    lemma list_test : \forall \list<integer> l1, l2;
//      l1 == l2  <==> \length (l1) == \length (l2) && same_list (l1, l2, 0, \length (l1));
    lemma num_of_list_update_new : \forall \list<integer> a, integer begin, k, end, value;
      begin <= k < end ==> \nth (a, k) != value ==>
      num_of_list (update (a, k, value), begin, end, value) == num_of_list (a, begin, end, value) + 1;
    lemma num_of_list_update_old : \forall \list<integer> a, integer begin, k, end, value;
      begin <= k < end ==> \nth (a, k) != value ==>
      num_of_list (update (a, k, value), begin, end, \nth (a, k)) == num_of_list (a, begin, end, \nth (a, k)) - 1;
    lemma num_of_list_update_other : \forall \list<integer> a, integer begin, k, end, value;
      begin <= k < end ==>
      \forall integer value2; value2 != value ==> value2 != \nth (a, k) ==>
      num_of_list (update (a, k, value), begin, end, value2) == num_of_list (a, begin, end, value2);
    predicate same_elements_list2 (\list<integer> a, \list<integer> b, integer begin, integer end) =
      \forall integer value; num_of_list (a, begin, end, value) == num_of_list (b, begin, end, value);
    lemma split_same_elements_list :
      \forall \list<integer> l1, l2, integer begin, i, end; 0 <= begin <= i <= end ==>
      same_elements_list(l1,l2,begin,i) ==>
      same_elements_list(l1,l2,i,end) ==>
      same_elements_list(l1,l2,begin,end);
    //lemma same_elements_list_array{L1, L2} : \forall int *a, integer n;
    //  same_elements_list (list_of_array{L1} (a, n), list_of_array{L2} (a, n), 0, n)
    //  <==> same_elements{L1,L2} (a, a, 0, n);
    lemma same_elements_list2_swap : \forall \list<integer> l1, l2, integer begin, i, j, end;
        swap_list(l1, l2, begin, i, j, end) ==>
        same_elements_list2(l1, l2, begin, end);
    lemma same_elements_list2_list : \forall \list<integer> a, b, integer begin, end;
      same_elements_list2 (a, b, begin, end) ==> same_elements_list (a, b, begin, end);
*/

/*@ requires n >= 0;
    requires \valid(a+(0..n-1));
    assigns a[0..n-1];
    ensures sorted: \forall integer i, j; 0 <= i <= j < n ==> a[i] <= a[j]; // the final array is sorted (proved!)
    ensures same_elements: same_elements{Pre, Here}(a, a, 0, n); // the array contains the same elements at the end as in the beginning (not proved)
*/
void pair_sort(int a[], int n) {
  int i = 0; // i is running index (inc by 2 every iteration)

  /*@ loop invariant \forall integer k, l; 0 <= k <= l < i ==> a[k] <= a[l]; // the sub-array a[0..i-1] is sorted
      loop invariant same_elements_list (list_of_array{Pre} (a, n), list_of_array{Here}(a, n));
      loop invariant 0 <= i <= n;
      loop assigns i, a[0..n-1];
      loop variant n - 1 - i;
  */
  while (i < n-1) {
    //@ ghost LC1:
    int x = a[i];	// let x and y hold the next to elements in A
    int y = a[i+1];
    
    if (x < y) {	// ensure that x is not smaller than y
        int tmp = x;
        x = y;
        y = tmp;
    }
    // assert x >= y ==> same_list (list_of_array{LoopCurrent} (a, n), update (update (list_of_array (a, n), i+1, x), i, y), 0, i+2);
    // assert x < y ==> swap_list (list_of_array{LC1} (a, n), update (update (list_of_array (a, n), i+1, x), i, y), 0, i, i+1, i+2);
    // assert a[i] < a[i+1] ==> x == a[i+1] && y == a[i];
    // assert a[i] < a[i+1] ==> x == \nth (list_of_array{LC1}(a, n), i+1) && y == \nth (list_of_array{LC1}(a, n), i);
    //@ assert \length (list_of_array(a, n)) >= 0 ==> a[i] < a[i+1] ==> list_of_array{LC1} (a, n) == update (update (list_of_array (a, n), i+1, x), i, y);
    // assert a[i] >= a[i+1] ==> x == a[i] && y == a[i+1];
    //@ assert a[i] >= a[i+1] ==> swap_list (list_of_array{LC1} (a, n), update (update (list_of_array (a, n), i+1, x), i, y), i, i+1);
    // assert same_elements_list (list_of_array{LC1} (a, n), list_of_array (a, n), 0, i+2);
    //@ assert same_elements_list (list_of_array{LC1} (a, n), update (update (list_of_array (a, n), i+1, x), i, y));
    //@ assert same_elements_list (list_of_array{Pre} (a, n), update (update (list_of_array (a, n), i+1, x), i, y));
    int z = a[0];
    // assert same_elements_list (list_of_array{Pre} (a, n), update (update (list_of_array (a, n), i+1, x), i, y), 0, i+2);
    int j = i - 1;	// j is the index used to find the insertion point
    /*@ loop invariant \forall integer k, l; 0 <= k <= l <= j ==> a[k] <= a[l]; // the sub-array a[0..j] is sorted
        loop invariant \forall integer k, l; j+2 < k <= l <= i+1 ==> a[k] <= a[l]; // the sub-array a[j+3..i+1] is sorted
        loop invariant \forall integer k, l; 0 <= k <= j && j +2 < l <= i+1 ==> a[k] <= a[l]; // every element in a[0..j] is no more then every element in a[j+3..i+1]
        loop invariant \forall integer k; j+2 < k <= i+1 ==> x < a[k]; // every element in a[j+3..i+1] is more than x
	//loop invariant \forall integer k; 0 <= k <= j ==> swap{LoopEntry,Here}(a,k,k+2,n);
	loop invariant same_elements_list (list_of_array{Pre} (a, n), update (update (list_of_array (a, n), j+2, x), j+1, y));
	//loop invariant j < i - 2 ==> same_list{Pre} (a, update (update (list_of_array (a, n), j+1, x), j, y), 0, i);
        loop invariant -1 <= j <= i - 1;
        loop assigns a[0..n-1], j;
	loop variant j;
    */
    while (j >= 0 && a[j] > x)	{// find the insertion point for x
       //@ ghost LC2:
       a[j+2] = a[j];	// shift existing content by 2
       //@ assert list_of_array (a, n) == update (list_of_array{LC2}(a,n), j+2, \nth(list_of_array{LC2}(a, n), j));
       //@ assert swap_list (list_of_array{LC2} (a, n), update (list_of_array(a, n), j, x), j, j+2);
       // assert update (list_of_array{LC2} (a, n), j+2, \nth(list_of_array{LC2}(a, n), j)) == list_of_array (a, n);
       // assert swap_list (update (list_of_array{LC2} (a, n), j+2, x), update (list_of_array (a, n), j, x), j, j+2);
       // assert swap_list (update (update (list_of_array{LC2} (a, n), j+2, x), j+1, y), update (update (list_of_array (a, n), j, x), j+1, y), j, j+2);
       // assert swap_list (update (update (list_of_array (a, n), j, x), j+1, y), update (update (list_of_array (a, n), j+1, x), j, y), j, j+1);
       // assert same_elements_list (list_of_array {Pre} (a, n), update (update (list_of_array (a, n), j, y), j+1, x), 0, j, j+1, n)
       //list_of_array{LC1} (a, n), update (update (list_of_array (a, n), j+2, x), i, y), 0, i, i+1, n);
       j = j - 1;
    }

    //@ ghost L1:
    a[j+2] = x;	// store x at its insertion place
    //@ assert update (list_of_array{L1} (a, n), j+2, x) == list_of_array (a, n);
    //@ assert update (update (list_of_array{L1} (a, n), j+2, x), j+1, y) == update (list_of_array (a, n), j+1, y);
	// A[j+1] is an available space now

    /*@ loop invariant \forall integer k, l; 0 <= k <= l <= j ==> a[k] <= a[l]; // the sub-array a[0..j] is sorted
        loop invariant \forall integer k, l; j+1 < k <= l <= i+1 ==> a[k] <= a[l]; // the sub-array a[j+2..i+1] is sorted
        loop invariant \forall integer k, l; 0 <= k <= j && j +1 < l <= i+1 ==> a[k] <= a[l]; // every element in a[0..j] is no more then every element in a[j+2..i+1]
        loop invariant \forall integer k; j+1 < k <= i+1 ==> y <= a[k]; // every element in a[j+2..i+1] is more than x
	loop invariant same_elements_list (list_of_array{Pre} (a, n), update (list_of_array (a, n), j+1, y));
        loop invariant -1 <= j <= \at(j, LoopEntry); // j varies between -1 and its value at the loop entry
        loop assigns a[0..n-1], j;
	loop variant j;
    */
    while (j >= 0 && a[j] > y) {	// find the insertion point for y
        //@ ghost LC3:
        a[j+1] = a[j];	// shift existing content by 1
        //@ assert update (list_of_array{LC3} (a, n), j+1, \nth (list_of_array{LC3} (a, n), j)) == list_of_array (a, n);
        //@ assert swap_list (update (list_of_array{LC3} (a, n), j+1, y), update (list_of_array (a, n), j, y), j, j+1);
        j = j - 1;
    }
    //@ ghost L2:
    a[j+1] = y;	// store y at its insertion place
    //@ assert update (list_of_array{L2} (a, n), j+1, y) == list_of_array (a, n);
    //@ assert same_elements_list (list_of_array{Pre} (a, n), list_of_array (a, n));

    i = i+2;
  }
  //@ ghost L3:
  if (i == n-1) {	// if length(A) is odd, an extra
    int y = a[i];	// single insertion is needed for 
    int j = i - 1;	// the last element
    //@ assert \length (list_of_array (a, n)) >= 0 ==> list_of_array{L3} (a, n) == update (list_of_array (a, n), j+1, y);
    /*@ loop invariant \forall integer k, l; 0 <= k <= l <= j ==> a[k] <= a[l]; // every element in a[0..j] is more than x
        loop invariant \forall integer k, l; j+1 < k <= l < n ==> a[k] <= a[l]; // every element in a[j+2..n-1] is more than x
        loop invariant \forall integer k, l; 0 <= k <= j && j +1 < l < n ==> a[k] <= a[l]; // every element in a[0..j] is no more then every element in a[j+2..n-1]
        loop invariant \forall integer k; j+1 < k < n ==> y <= a[k]; // every element in a[j+2..n-1] is no less then y
        loop invariant same_elements_list (list_of_array{Pre} (a, n), update (list_of_array (a, n), j+1, y));
        loop invariant -1 <= j <= i-1;
        loop assigns a[0..n-1], j;
	loop variant j;
    */
    while (j >= 0 && a[j] > y) {
        //@ ghost LC4:
        a[j+1] = a[j];
        //@ assert swap_list (update (list_of_array{LC4} (a, n), j+1, y), update (list_of_array (a, n), j, y), j, j+1);
        j = j - 1;
    }
    //@ ghost L4:
    a[j+1] = y;
    //@ assert \length (list_of_array(a, n)) >= 0 ==> update (list_of_array{L4} (a, n), j+1, y) == list_of_array (a, n);
  }
  //@ assert same_elements_list (list_of_array{Pre} (a, n), list_of_array (a, n));
}

