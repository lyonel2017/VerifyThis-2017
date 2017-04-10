/*@ axiomatic sum_axiomatic {
  @   logic integer sum (int* a, int* b, integer i, integer j, integer n, integer k);
  @
  @   axiom sum_nil : \forall int *a, *b, integer i, j, n; sum (a, b, i, j, n, 0) == 0;
  @   axiom sum_next : \forall int *a, *b, integer i, j, n, k;
  @     sum (a, b, i, j, n, k + 1) == sum (a, b, i, j, n, k) + a[i*n+k]*b[k*n+j];
  @ }
*/

/*@ requires \separated(a+(0..n*n-1),c+(0..n*n-1));
  @ requires \separated(b+(0..n*n-1),c+(0..n*n-1));
  @ requires \valid_read(a+(0..n*n-1));
  @ requires \valid_read(b+(0..n*n-1));
  @ requires \valid(c+(0..n*n-1));
  @ requires n >= 0;
  @ assigns c[0..n*n-1];
  @ ensures \forall integer i, j; 0 <= i < n && 0 <= j < n ==> c[i*n+j] == sum(a, b, i, j, n, n);
 */
void matrix_mult(int a[], int b[], int c[], int n) {
  /*@ loop assigns c[0..n*n-1], i;
    @ loop invariant 0 <= i <= n;
    @ loop invariant \forall integer k, j; 0 <= k < i && 0 <= j < n ==> c[k*n+j] == sum(a, b, k, j, n, n);
    @ loop variant n - i;
  */
  for(int i = 0; i < n; i++) {
    /*@ loop assigns c[i*n..i*n+n-1], j;
      @ loop invariant 0 <= j <= n;
      @ loop invariant \forall integer k; 0 <= k < j ==> c[i*n+k] == sum(a, b, i, k, n, n);
      @ loop variant n - j;
    */
    for(int j = 0; j < n; j++) {
      c[i*n+j] = 0;
      /*@ loop assigns c[i*n+j], k;
        @ loop invariant 0 <= k <= n;
        @ loop invariant c[i*n+j] == sum(a, b, i, j, n, k);
        @ loop variant n - k;
      */
      for(int k = 0; k < n; k++) {
        c[i*n+j] += a[i*n+k] * b[k*n+j];
      }
    }
  }
}
