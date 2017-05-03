/*@ predicate swap{L1, L2}(int *a, int *b, integer begin, integer i, integer j, integer end) =
      begin <= i < j < end &&
      \at(a[i], L1) == \at(b[j], L2) &&
      \at(a[i], L2) == \at(b[j], L1) &&
      \forall integer k; begin <= k < end && k != i && k != j ==>
        \at(a[k], L1) == \at(b[k], L2);
*/

/*@ predicate same_array{L1,L2}(int *a, int *b, integer begin, integer end) =
      \forall integer k; begin <= k < end ==> \at(a[k],L1) == \at(b[k],L2);
*/

/*@ inductive same_elements{L1, L2}(int *a, int *b, integer begin, integer end) {
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
    lemma split_same_elements{L1,L2} :
      \forall int *a, *b, integer begin, i, end; begin <= i <= end ==>
      same_elements{L1,L2}(a,b,begin,i) ==>
      same_elements{L1,L2}(a,b,i,end) ==>
      same_elements{L1,L2}(a,b,begin,end);
*/

/* lemma same_elements_extensional{L1,L2} :
      \forall int *a, integer length;
      (\forall integer k; 0 <= k < length ==> \at(a[k], L1) == \at(a[k], L2)) ==>
      same_elements{L1,L2}(a, length);
*/

/*@ lemma disjoint_cases : \forall integer i, j; i < j || i == j || i > j;
*/

/*@ requires 0 <= i;
    requires 0 <= j;
    requires \valid(list+(0..\max(i, j)));
    //ensures \forall integer n; n > \max(i,j) ==> same_elements{Pre, Here}(list, list, 0, n);
    ensures same_elements{Pre, Here}(list, list, 0, \max(i, j)+1);
    ensures i != j ==> swap{Pre, Here}(list, list, 0, \min(i,j), \max(i, j), \max(i,j)+1);
    ensures i == j ==> same_array{Pre,Here}(list, list, 0, \max(i,j)+1);
    //ensures \forall integer k; k != i && k != j ==> list[k] == \old(list[k]);
    //ensures list[j]==\old(list[i]);
    //ensures list[i]==\old(list[j]);
    assigns list[0..\max(i,j)];
*/
void swap (int list[], int i, int j) {
  int temp = list[i];
  list[i] = list[j];
  list[j] = temp;
  //@ assert i<j==>swap{Pre, Here}(list,list,0,i,j,\max(i,j)+1);
  //@ assert i>j==>swap{Pre, Here}(list,list,0,j,i,\max(i,j)+1);
}

/*@ lemma odd_even : \forall integer k; k >= 0 ==> k % 2 == 0 || k % 2 == 1;
*/

/*@ requires n >= 0;
    requires \valid(list+(0..n-1));
    assigns list[0..n-1];
    ensures sorted: \forall integer i, j; 0 <= i <= j < n ==> list[i] <= list[j]; // the final array is sorted (proved!)
    ensures same_elements: same_elements{Pre, Here}(list, list, 0, n); // the array contains the same elements at the end as in the beginning
*/
void oddEvenSort (int list[], int n) {
  int sorted = 0;
  /*@ loop invariant 0 <= sorted <= 1;
    @ loop invariant same_elements{Pre, Here}(list, list, 0, n);
    @ loop assigns sorted,list[0..n-1];
  */
  while(!sorted) {
    sorted=1;
    /*@ loop invariant 0 <= sorted <= 1;
      @ loop invariant 1 <= i <= n+1;
      @ loop invariant same_elements{Pre, Here}(list, list, 0, n);
      @ loop invariant \forall integer k; 0 <= k < i ==> k%2==1 ==> list[k] <= list[k+1];
      @ loop assigns i, list[0..n-1], sorted;
      @ loop variant n - i;
    */
    for(int i = 1; i < n-1; i+=2) {
      if (list[i] > list[i+1]) {
        //@ ghost L1:
        swap(list, i, i+1);
        //@ assert swap{L1, Here}(list,list,0,i,i+1,i+2);
        //@ assert same_elements{L1, Here}(list,list,i+2,n);
        sorted = 0;
      }
    }
    /*@ loop invariant 0 <= sorted <= 1;
      @ loop invariant 0 <= i <= n;
      @ loop invariant same_elements{Pre, Here}(list, list, 0, n);
      @ loop invariant sorted == 1 ==> \forall integer k; 0 <= k < n ==> list[k] == \at(list[k], LoopEntry);
      @ loop invariant \forall integer k; 0 <= k < i ==> k%2==0 ==> list[i] <= list[i+1];
      @ loop assigns i, list[0..n-1], sorted;
      @ loop variant n - i;
    */
    for(int i = 0; i < n-1; i+=2) {
      if (list[i] > list[i+1]) {
        //@ ghost L2:
        swap(list, i, i+1);
        //@ assert swap{L2, Here}(list,list,0,i,i+1,i+2);
        //@ assert same_elements{L2, Here}(list,list,i+2,n);
        sorted = 0;
      }
    }
    //@ assert sorted == 1 ==> \forall integer k; 0 <= k < n-1 ==> list[k] <= list[k+1];
  }
}
