/*@ predicate swap{L1, L2}(int *a, int *b, integer debut, integer i, integer j, integer fin) =
      debut <= i < fin && debut <= j < fin &&
      \at(a[i], L1) == \at(b[j], L2) &&
      \at(a[j], L1) == \at(b[i], L2) &&
      \forall integer k; debut <= k < fin && k != i && k != j ==> \at(a[k], L1) == \at(b[k], L2);
*/

/*@ predicate same_array{L1,L2}(int *a, int *b, integer debut, integer fin) =
      \forall integer k; debut <= k < fin ==> \at(a[k],L1) == \at(b[k],L2);
*/

/*@ inductive same_elements{L1, L2}(int *a, int *b, integer debut, integer fin) {
      case refl{L1, L2}:
        \forall int *a, int *b, integer debut, fin;
        same_array{L1,L2}(a, b, debut, fin) ==>
        same_elements{L1, L2}(a, b, debut, fin);
      case swap{L1, L2}: \forall int *a, int *b, integer debut, i, j, fin;
        swap{L1, L2}(a, b, debut, i, j, fin) ==>
        same_elements{L1, L2}(a, b, debut, fin);
      case trans{L1, L2, L3}: \forall int* a, int *b, int *c, integer debut, fin;
        same_elements{L1, L2}(a, b, debut, fin) ==>
        same_elements{L2, L3}(b, c, debut, fin) ==>
        same_elements{L1, L3}(a, c, debut, fin);
}*/

/*
  inductive lt_lex2 (int* a, int* b, integer m, integer n) {
     case lt_lex2_1 :
        \forall int* a, int* b, integer m, n;
           a[m] < b[m] ==> lt_lex2 (a, b, m, n);
     case lt_lex2_2 :
        \forall int* a, int* b, integer m, n;
           a[m] == b[m] ==> lt_lex2 (a, b, m+1, n) ==> lt_lex2 (a, b, m, n);
  }
*/


/*@ predicate lt_lex_aux {L1,L2}(int* a, int* b, integer n, integer m) =
     0 <= m < n && \at(a[m],L1) < \at(b[m],L2) && same_array{L1,L2}(a, b, 0, m);

    predicate lt_lex {L1,L2}(int* a, int* b, integer n) =
     \exists integer m; lt_lex_aux {L1,L2}(a, b, n, m);


  lemma lt_lex_irrefl {L1,L2} : \forall int* a, integer n; same_array{L1,L2}(a, a, 0, n) ==> !lt_lex {L1,L2}(a, a, n);
  lemma lt_lex_trans {L1,L2,L3}: \forall int* a, int* b, int* c, integer n;
         lt_lex {L1,L2}(a, b, n) ==> lt_lex {L2,L3}(b, c, n) ==> lt_lex {L1,L3}(a, c, n);

  predicate is_next_lex {L1,L2}(int* a, int* b, integer n) =
         lt_lex{L1,L2} (a, b, n) && \forall int* c; lt_lex {L1,L2}(a, c, n) ==> !lt_lex{L1,L2}(c, b, n);
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

/*@ predicate sorted(int* tab, integer idx, integer n) = \forall integer x,y; idx <= x < y < n ==> tab[x] >= tab[y];*/


/*@ requires \valid(A+(0..n-1));
  @ requires n >= 0;
  @ ensures same_elements{Pre,Post}(A,A,0,n);
  @ ensures \result == 0 ==> (sorted(A,0,n) && same_array{Pre,Post}(A, A, 0, n));
  @ ensures \result == 1 ==> is_next_lex {Pre,Post}(A, A, n);
  @ assigns A[0..n-1];
*/
int next (int* A, int n){
  int i = n - 1;

  /*@ loop invariant -1 <= i < n;
    @ loop invariant \forall integer k; i < k < n ==> A[k] <= A[k-1];
    @ loop invariant sorted(A,i,n);
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
  /*@ assert same_elements{L1,Here}(A,A,0,n);*/
  /*@ assert lt_lex_aux {L1,Here}(A, A,n,i-1);*/

  j = n - 1;
  /*@ loop invariant \at(i,LoopEntry) <= i <= n;
    @ loop invariant 0 <= j < n;
    @ loop invariant i <= j+1;
    @ loop invariant same_elements{LoopEntry,Here}(A,A,0,n);
    @ loop invariant same_array{LoopEntry,Here}(A, A, 0, \at(i,LoopEntry));
    @ loop invariant lt_lex_aux {L1,Here}(A, A,n,\at(i-1,LoopEntry));
    @ loop assigns i,j,A[0..n-1];
    @ loop variant j-i;
    @*/
  while(i < j){
  L2:swap(A+i,A+j);
    /*@ assert swap{L2,Here}(A,A,0,i,j,n);*/
    /*@ assert same_elements{L2,Here}(A,A,0,n);*/
    i++;
    j--;
  }

  return 1;
}

/*@ requires \valid(A+(0..n-1));
    ensures sorted(A, 0, n);
    ensures same_elements{Pre,Post} (A,A,0,n);
*/
void sort (int* A, int n);

/*@ requires A == \null || \valid(A+(0..n-1)) && 0 <= n;
*/
int permut (int* A, int n) {
  int result = 0;
  if (!A)
    return result;
  sort (A, n);
  do {
    result++;
  } while (next (A, n));

  return result;
}
