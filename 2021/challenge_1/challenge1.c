/*@ predicate sorted(int* tab, integer idx) = \forall integer x,y; 0 <= x < y < idx ==> tab[x] <= tab[y]; */


/*@ predicate swap{L1, L2}(int *a, int *b, integer begin, integer i, integer j, integer end) =
      begin <= i < end && begin <= j < end &&
      \at(a[i], L1) == \at(b[j], L2) &&
      \at(a[j], L1) == \at(b[i], L2) &&
      \forall integer k; begin <= k < end && k != i && k != j ==> \at(a[k], L1) == \at(b[k], L2);
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
      case trans{L1, L2, L3}: \forall int* a, int *b, int *c, integer begin, end;
        same_elements{L1, L2}(a, b, begin, end) ==>
        same_elements{L2, L3}(b, c, begin, end) ==>
        same_elements{L1, L3}(a, c, begin, end);
}*/

/* lemma case split {L1, L2}: \forall int *a, int *b, integer begin, i, end;
        begin <= i < end ==>
        same_elements{L1,L2}(a, b, begin, i) ==>
        same_elements{L1,L2}(a, b, i, end) ==>
        same_elements{L1,L2}(a, b, begin, end);
*/

/* lemma partition {L1, L2}: \forall int *a, int *b, integer begin, i, j, end;
        begin <= i <= j < end ==>
        same_array{L1,L2}(a, b, begin, i) ==>
        same_elements{L1,L2}(a, b, i, j) ==>
        same_array{L1,L2}(a, b, j, end) ==>
        same_elements{L1, L2}(a, b, begin, end);
*/

/*@ requires \valid(x) && \valid(y);
   requires \separated(x,y);
   ensures *x == \old(*y) && *y == \old(*x);
   assigns *x,*y;*/
void swap(int *x, int *y){
  int t = *x;
  * x = *y;
  *y = t;
}

int next (int* A, int n){
  int i = n-1;

  while(i > 0 && A[i] <= A[i-1]){
    i--;
  }
  if (i <= 0){return 0;}

  int j = n-1;
  while(j > 0 && A[j] <= A[j-1]){
    j--;
  }

  swap(A+(i-1),A+i);

  while(i < j){
    swap(A+i,A+j);
    i++;
    i--;
  }

  return 1;
}
