/*@ axiomatic sum_axiomatic {
  @   logic integer sum (int* a, int* b, integer n, integer i, integer j, integer k, integer l)
  @     reads a[0..n*n-1], b[0..n*n-1];
  @
  @   axiom sum_nil : \forall int *a, *b, integer n, i, j, k; sum (a, b, n, i, j, k, k) == 0;
  @   axiom sum_next : \forall int *a, *b, integer n, i, j, k, l;
  @     sum (a, b, n, i, j, k, l + 1) == sum (a, b, n, i, j, k, l) + a[i*n+l]*b[l*n+j];
  @ }
*/

/*@ predicate matrix_eq{L1,L2} (int* a, int* b, integer n) = // reads a[0..n*n-1], b[0..n*n-1] =
      \forall integer k; 0 <= k < n*n ==> \at(a[k],L1) == \at(b[k],L2);
 */

/*@ lemma sum_only_read{L1,L2} :
      \forall int *a, *b, integer n, i, j, k, l;
        0 <= n && 0 <= i < n && 0 <= j < n && 0 <= k <= l <= n ==>
        matrix_eq{L1,L2}(a, a, n) && matrix_eq{L1,L2}(b, b, n) ==>
        sum{L1} (a, b, n, i, j, k, l) == sum{L2} (a, b, i, j, n, k, l);
 */

/*@ lemma split_sum : \forall int *a, *b, integer n, i, j, k, m, l;
  @   0 <= n && 0 <= i < n && 0 <= j < n && 0 <= k <= m <= l <= n ==>
  @   sum(a, b, n, i, j, k, l) == sum(a, b, n, i, j, k, m) + sum(a, b, n, i, j, m, l);
*/

/*@ lemma sum_assoc : \forall int *a, *b, *c, *tmp1, *tmp2, integer n;
  @   (\forall integer i, j; 0 <= i < n && 0 <= j < n ==> tmp1[i*n+j] == sum(b, c, n, i, j, 0, n)) &&
  @   (\forall integer i, j; 0 <= i < n && 0 <= j < n ==> tmp2[i*n+j] == sum(a, b, n, i, j, 0, n)) ==>
  @   \forall integer i, j; 0 <= i < n && 0 <= j < n ==> sum(a, tmp1, n, i, j, 0, n) == sum(tmp2, c, n, i, j, 0, n);
*/

/*@ requires \separated(a+(0..n*n-1),c+(0..n*n-1));
  @ requires \separated(b+(0..n*n-1),c+(0..n*n-1));
  @ requires \valid_read(a+(0..n*n-1));
  @ requires \valid_read(b+(0..n*n-1));
  @ requires \valid(c+(0..n*n-1));
  @ requires n >= 0;
  @ assigns c[0..n*n-1] \from a[0..n*n-1],b[0..n*n-1];
  //@ relational \forall int *a1, *a2, *b1, *b2, *c1,*c2, int n; \callset(\call(matrix_mult,a1, b1, c1, n,id1),\call(matrix_mult,a2,b2,c2,n,id2)) ==> \at(c1[0],Post_id1) < \at(c2[0],Post_id2);
  @ ensures \forall integer i, j; 0 <= i < n && 0 <= j < n ==> c[i*n+j] == sum(a, b, n, i, j, 0, n);
 */
void matrix_mult(int a[], int b[], int c[], int n) {
  /*@ loop assigns c[0..n*n-1], i;
    @ loop invariant 0 <= i <= n;
    @ loop invariant \forall integer k, j; 0 <= k < i && 0 <= j < n ==> c[k*n+j] == sum(a, b, n, k, j, 0, n);
    @ loop variant n - i;
  */
  for(int i = 0; i < n; i++) {
    /*@ loop assigns c[i*n..i*n+n-1], j;
      @ loop invariant 0 <= j <= n;
      @ loop invariant \forall integer k; 0 <= k < j ==> c[i*n+k] == sum(a, b, n, i, k, 0, n);
      @ loop variant n - j;
    */
    for(int j = 0; j < n; j++) {
      c[i*n+j] = 0;
      /*@ loop assigns c[i*n+j], k;
        @ loop invariant 0 <= k <= n;
        @ loop invariant c[i*n+j] == sum(a, b, n, i, j, 0, k);
        @ loop variant n - k;
      */
      for(int k = 0; k < n; k++) {
        c[i*n+j] += a[i*n+k] * b[k*n+j];
      }
    }
  }
}
