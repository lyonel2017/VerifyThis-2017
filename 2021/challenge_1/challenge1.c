/*@ predicate swap{L1, L2}(int *a, int *b, integer debut, integer i, integer j, integer fin) =
      debut <= i < fin && debut <= j < fin &&
      \at(a[i], L1) == \at(b[j], L2) &&
      \at(a[j], L1) == \at(b[i], L2) &&
      \forall integer k; debut <= k < fin && k != i && k != j ==> \at(a[k], L1) == \at(b[k], L2);
*/

/*@ predicate same_array{L1,L2}(int *a, int *b, integer debut, integer fin) =
      \forall integer k; debut <= k < fin ==> \at(a[k],L1) == \at(b[k],L2);
*/

/*@ inductive permutation{L1, L2}(int *a, int *b, integer debut, integer fin) {
      case refl{L1, L2}:
        \forall int *a, int *b, integer debut, fin;
        same_array{L1,L2}(a, b, debut, fin) ==>
        permutation{L1, L2}(a, b, debut, fin);
      case swap{L1, L2}: \forall int *a, int *b, integer debut, i, j, fin;
        swap{L1, L2}(a, b, debut, i, j, fin) ==>
        permutation{L1, L2}(a, b, debut, fin);
      case trans{L1, L2, L3}: \forall int* a, int *b, int *c, integer debut, fin;
        permutation{L1, L2}(a, b, debut, fin) ==>
        permutation{L2, L3}(b, c, debut, fin) ==>
        permutation{L1, L3}(a, c, debut, fin);
}*/

/*@ predicate sorted_le(int* tab, integer idx, integer n) = \forall integer x,y; idx <= x < y < n ==> tab[x] <= tab[y];
    predicate sorted_ge(int* tab, integer idx, integer n) = \forall integer x,y; idx <= x < y < n ==> tab[x] >= tab[y];
*/

/*@ predicate lt_lex_aux {L1,L2}(int* a, int* b, integer i, integer m, integer j) =
      i <= m < j && \at(a[m],L1) < \at(b[m],L2) && same_array{L1,L2}(a, b, i, m);

    predicate lt_lex {L1,L2}(int* a, int* b, integer i, integer j) =
      \exists integer m; lt_lex_aux {L1,L2}(a, b, i, m, j);

    lemma lt_lex_irrefl {L1,L2} : \forall int* a, integer i, j; same_array{L1,L2}(a, a, i, j) ==> !lt_lex {L1,L2}(a, a, i, j);
    lemma lt_lex_trans {L1,L2,L3}: \forall int* a, int* b, int* c, integer i, j;
      lt_lex {L1,L2}(a, b, i, j) ==> lt_lex {L2,L3}(b, c, i, j) ==> lt_lex {L1,L3}(a, c, i, j);

    predicate is_larger {L1, L2}(int* a, int* b, integer i, integer j) =
      permutation{L1,L2}(a,b,i,j) && lt_lex{L1,L2}(a, b, i, j);

    predicate is_next {L1,L2}(int* a, int* b, integer i, integer j) =
      is_larger{L1,L2} (a,b,i,j) &&
      \forall int* c; is_larger{L1,L1} (a,c,i,j) ==> !is_larger{L1,L2}(c,b,i,j);

    predicate min_lex{L} (int* a, integer i, integer j) =
      \forall int* c; !is_larger{L,L} (c,a,i,j);
    predicate max_lex{L} (int* a, integer i, integer j) =
      \forall int* c; !is_larger{L,L} (a,c,i,j);

    lemma sorted_le_lex : \forall int* a, integer i, j;
      sorted_le (a, i, j) ==> min_lex (a, i, j);

    lemma sorted_ge_lex : \forall int* a, integer i, j;
      sorted_ge (a, i, j) ==> max_lex (a, i, j);

    lemma is_next_concat {L1,L2} : \forall int* a, int* b, integer i, j, k;
      same_array{L1,L2}(a,b,i,j) ==> is_next{L1,L2}(a,b,j,k) ==> is_next{L1,L2}(a,b,i,k);

    lemma is_next_sorted_ge {L1, L2, L3} : \forall int* a, integer i, j, n;
      sorted_ge{L1} (a, i, n) ==> \at(a[i-1], L1) > \at(a[i], L1) ==>
      \forall int* b, int* c;
      swap{L1,L2}(a,b,i-1,i-1,j,n) ==> permutation{L2,L3}(b,c,i,n) ==> sorted_le{L3}(c,i,n) ==>
      is_next{L1,L3}(a,c,i,n);

*/

/*@ requires \valid(x) && \valid(y);
  @ requires \separated(x,y);
  @ ensures *x == \old(*y) && *y == \old(*x);
  @ assigns *x,*y;*/
void swap(int *x, int *y){
  int t = *x;
  * x = *y;
  *y = t;
}


/*@ requires \valid(A+(0..n-1));
  @ requires n >= 0;
  @ ensures permutation{Pre,Post}(A,A,0,n);
  @ ensures \result == 0 ==> same_array{Pre,Post}(A, A, 0, n) && max_lex (A, 0, n);
  @ ensures \result == 1 ==> lt_lex {Pre,Post}(A,A,0,n);
//  @ ensures \result == 1 ==> is_next_lex {Pre,Post}(A, A, 0, n);
  @ assigns A[0..n-1];
*/
int next (int* A, int n){
  int i = n - 1;

  /*@ loop invariant -1 <= i < n;
    @ loop invariant sorted_ge(A,i,n);
    @ loop assigns i;
    @ loop variant i;
    @*/
  while(i > 0 && A[i] <= A[i-1]){
    i--;
  }
  if (i <= 0){return 0;}

  int j = n - 1;

  /*@ loop invariant i <= j < n;
    @ loop invariant \forall integer k; j < k < n ==> A[k] <= A[i-1];
    @ loop assigns j;
    @ loop variant j;
    @*/
  while(A[j] <= A[i-1]){
    j--;
  }

 L1:swap(A+(i-1),A+j);
  /*@ assert swap{L1,Here}(A,A,0,i-1,j,n);*/
  /*@ assert permutation{L1,Here}(A,A,0,n);*/
  /*@ assert lt_lex_aux {L1,Here}(A, A,0,i-1,n);*/
  /*@ assert sorted_ge (A, i, n); */

  j = n - 1;

  /* assert sorted1(A,i,j+1);*/

  /*@ loop invariant \at(i,LoopEntry) <= i <= n;
    @ loop invariant 0 <= j < n;
    @ loop invariant i <= j+1;
    @ loop invariant permutation{LoopEntry,Here}(A,A,0,n);
    @ loop invariant same_array{LoopEntry,Here}(A, A, 0, \at(i,LoopEntry));
    @ loop invariant lt_lex_aux {L1,Here}(A, A,0,\at(i-1,LoopEntry),n);
    @ loop invariant sorted_ge(A,i,j+1);
    @ loop invariant \forall integer x; \at(i,LoopEntry) <= x < i ==> A[x] <= A[j];
    @ loop invariant \forall integer x; j < x < n ==> A[i] <= A[x];
    @ loop invariant \forall integer x,y; \at(i,LoopEntry) <= x < i && j < y < n ==> A[x] <= A[y];
    @ loop invariant sorted_le(A,j,n);
    @ loop invariant sorted_le(A,\at(i,LoopEntry),i);
    @ loop assigns i,j,A[0..n-1];
    @ loop variant j-i;
    @*/
  while(i < j){
  L2:swap(A+i,A+j);
    /*@ assert swap{L2,Here}(A,A,0,i,j,n);*/
    /*@ assert permutation{L2,Here}(A,A,0,n);*/
    i++;
    j--;
  }
  /*@ assert sorted_le(A,\at(i,L1),n);*/

  return 1;
}

/*@ requires \valid(A+(0..n-1));
    ensures sorted_le(A, 0, n);
    ensures permutation{Pre,Post} (A,A,0,n);
    assigns A[0..n-1];
*/
void sort (int* A, int n);

/*@ requires A == \null || \valid(A+(0..n-1)) && 0 <= n;
    assigns A[0..n-1];
*/
int permut (int* A, int n) {
  int result = 0;
  if (!A)
    return result;
  sort (A, n);
  //@ assert min_lex (A, 0, n);
  /*@ loop assigns A[0..n-1], result;
      // loop variant A for is_larger; // not yet supported by Wp
    @*/
  do {
    result++;
  } while (next (A, n));

  return result;
}
