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

/*@ requires \valid(x) && \valid(y);
  @ requires \separated(x,y);
  @ ensures *x == \old(*y) && *y == \old(*x);
  @ assigns *x,*y;*/
void swap(int *x, int *y){
  int t = *x;
  * x = *y;
  *y = t;
}

/*@ predicate sorted(int* tab, integer idx, integer n) = \forall integer x,y; idx <= x < y <= n ==> tab[x] >= tab[y];*/


/*@ requires \valid(A+(0..n));
  @ requires n >= 0;
  @ ensures same_elements{Pre,Post}(A,A,0,n+1);
  @ ensures \result == 0 ==> (sorted(A,0,n) && same_array{Pre,Post}(A, A, 0, n+1));
*/
int next (int* A, int n){
  int i = n;

  /*@ loop invariant 0 <= i <= n;
    @ loop invariant \forall integer k; i < k <= n ==> A[k] <= A[k-1];
    @ loop invariant sorted(A,i,n);
    //@ loop invariant \forall integer x,y; i <= x < y <= n ==> A[x] >= A[y];
    @ loop assigns i;
    @ loop variant i;
    @*/
  while(i > 0 && A[i] <= A[i-1]){
    i--;
  }
  if (i <= 0){return 0;}

  int j = n;

  /*@ loop invariant i <= j <= n;
    @ loop invariant \forall integer k; j < k <= n ==> A[k] <= A[i-1];
    @ loop assigns j;
    @ loop variant j;
    @*/
  while(A[j] <= A[i-1]){
    j--;
  }

 L1:swap(A+(i-1),A+i);
  /*@ assert swap{L1,Here}(A,A,0,i-1,i,n+1);*/
  /*@ assert same_elements{L1,Here}(A,A,0,n+1);*/

  j = n;
  /*@ loop invariant \at(i,LoopEntry) <= i <= n;
    @ loop invariant 0 <= j <= n;
    @ loop invariant i <= j+1;
    @ loop invariant same_elements{LoopEntry,Here}(A,A,0,n+1);
    @ loop assigns i,j,A[0..n];
    @ loop variant j-i;
    @*/
  while(i < j){
  L2:swap(A+i,A+j);
    /*@ assert swap{L2,Here}(A,A,0,i,j,n+1);*/
    /*@ assert same_elements{L2,Here}(A,A,0,n+1);*/
    i++;
    j--;
  }

  return 1;
}
