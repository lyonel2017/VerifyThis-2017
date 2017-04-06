/*@ requires \separated(a+(0..n*n-1),c+(0..n*n-1));
  @ requires \separated(b+(0..n*n-1),c+(0..n*n-1));
  @ requires \valid_read(a+(0..n*n-1));
  @ requires \valid_read(b+(0..n*n-1));
  @ requires \valid(c+(0..n*n-1));
  @ requires n >= 0;
  @ assigns c[0..n*n-1];
 */
void matrix_mult(int a[], int b[], int c[], int n) {
  /*@ loop assigns c[0..n*n-1], i;
    @ loop invariant 0 <= i <= n;
    @ loop variant n - i;
  */
  for(int i = 0; i < n; i++) {
    /*@ loop assigns c[i*n..i*n+n-1], j;
      @ loop invariant 0 <= j <= n;
      @ loop variant n - j;
    */
    for(int j = 0; j < n; j++) {
      c[i*n+j] = 0;
      /*@ loop assigns c[i*n+j], k;
        @ loop invariant 0 <= k <= n;
        @ loop variant n - k;
      */
      for(int k = 0; k < n; k++) {
        c[i*n+j] += a[i*n+k] * b[k*n+j];
      }
    }
  }
}
