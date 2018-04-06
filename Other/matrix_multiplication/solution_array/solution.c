/*@ axiomatic sum_axiomatic {
  @   logic integer sum{L} (int* a, int* b, integer n, integer i, integer j, integer k)
  @     reads a[0..n*n-1], b[0..n*n-1];
  @
  @   axiom sum_nil : \forall int *a, *b, integer n, i, j, k; sum (a, b, n, i, j, 0) == 0;
  @   axiom sum_next : \forall int *a, *b, integer n, i, j, k;
  @     sum (a, b, n, i, j, k + 1) == sum (a, b, n, i, j, k) + a[i*n+k]*b[k*n+j];
  @ }
*/

/* logic integer coef (int *a, int *b, integer n, integer i, integer j, integer k) = a[i*n+k]*b[k*n+j];
    logic integer sum (int *a, int *b, integer n, integer i, integer j, integer k) = \sum (0, k, coef(a, b, n, i, j));
 */

/*@ predicate matrix_eq{L1,L2} (int* a, int* b, integer n) = // reads a[0..n*n-1], b[0..n*n-1] =
      \forall integer k; 0 <= k < n*n ==> \at(a[k],L1) == \at(b[k],L2);

    lemma matrix_eq_trans{L1,L2,L3} : \forall int *a, *b, *c, integer n;
      matrix_eq{L1,L2}(a,b,n) ==> matrix_eq{L2,L3}(b,c,n) ==> matrix_eq{L1,L3}(a,c,n);

    lemma matrix_eq_comm{L1,L2} : \forall int *a, *b, integer n;
      matrix_eq{L1,L2}(a,b,n) ==> matrix_eq{L2,L1}(b,a,n);
 */

/*@ lemma sum_only_read{L1,L2} :
      \forall int *a, *b, integer n, i, j, k;
        0 <= n && 0 <= i < n && 0 <= j < n && 0 <= k <= n ==>
        matrix_eq{L1,L2}(a, a, n) && matrix_eq{L1,L2}(b, b, n) ==>
        sum{L1} (a, b, n, i, j, k) == sum{L2} (a, b, n, i, j, k);
 */

/*@ lemma sum_assoc : \forall int *a, *b, *c, *tmp1, *tmp2, integer n;
  @   (\forall integer i, j; 0 <= i < n && 0 <= j < n ==> tmp1[i*n+j] == sum(b, c, n, i, j, n)) &&
  @   (\forall integer i, j; 0 <= i < n && 0 <= j < n ==> tmp2[i*n+j] == sum(a, b, n, i, j, n)) ==>
  @   \forall integer i, j; 0 <= i < n && 0 <= j < n ==> sum(a, tmp1, n, i, j, n) == sum(tmp2, c, n, i, j, n);
*/

/*@ requires \separated(a+(0..n*n-1),c+(0..n*n-1));
  @ requires \separated(b+(0..n*n-1),c+(0..n*n-1));
  @ requires \valid_read(a+(0..n*n-1));
  @ requires \valid_read(b+(0..n*n-1));
  @ requires \valid(c+(0..n*n-1));
  @ requires n >= 0;
  @ assigns c[0..n*n-1] \from a[0..n*n-1],b[0..n*n-1];
  //@ relational \forall int *a1, *a2, *b1, *b2, *c1,*c2, int n; \callset(\call(matrix_mult,a1, b1, c1, n,id1),\call(matrix_mult,a2,b2,c2,n,id2)) ==> \at(c1[0],Post_id1) < \at(c2[0],Post_id2);
  @ ensures \forall integer i, j; 0 <= i < n && 0 <= j < n ==> c[i*n+j] == sum(a, b, n, i, j, n);
 */
void matrix_mult(int a[], int b[], int c[], int n) {
  /*@ loop assigns c[0..n*n-1], i;
    @ loop invariant 0 <= i <= n;
    @ loop invariant \forall integer k, j; 0 <= k < i && 0 <= j < n ==> c[k*n+j] == sum(a, b, n, k, j, n);
    @ loop variant n - i;
  */
  for(int i = 0; i < n; i++) {
    /*@ loop assigns c[i*n..i*n+n-1], j;
      @ loop invariant 0 <= j <= n;
      @ loop invariant \forall integer k; 0 <= k < j ==> c[i*n+k] == sum(a, b, n, i, k, n);
      @ loop variant n - j;
    */
    for(int j = 0; j < n; j++) {
      c[i*n+j] = 0;
      /*@ loop assigns c[i*n+j], k;
        @ loop invariant 0 <= k <= n;
        @ loop invariant c[i*n+j] == sum(a, b, n, i, j, k);
        @ loop variant n - k;
      */
      for(int k = 0; k < n; k++) {
        c[i*n+j] += a[i*n+k] * b[k*n+j];
      }
    }
  }
}

/*@ requires \separated (ab+(0..n*n-1), a+(0..n*n-1));
  @ requires \separated (ab+(0..n*n-1), b+(0..n*n-1));
  @ requires \separated (ab+(0..n*n-1), c+(0..n*n-1));
  @ requires \separated (ab+(0..n*n-1), bc+(0..n*n-1));
  @ requires \separated (ab+(0..n*n-1), ab_c+(0..n*n-1));
  @ requires \separated (ab+(0..n*n-1), a_bc+(0..n*n-1));
  @ requires \separated (bc+(0..n*n-1), a+(0..n*n-1));
  @ requires \separated (bc+(0..n*n-1), b+(0..n*n-1));
  @ requires \separated (bc+(0..n*n-1), c+(0..n*n-1));
  @ requires \separated (bc+(0..n*n-1), ab_c+(0..n*n-1));
  @ requires \separated (bc+(0..n*n-1), a_bc+(0..n*n-1));
  @ requires \separated (ab_c+(0..n*n-1), a+(0..n*n-1));
  @ requires \separated (ab_c+(0..n*n-1), b+(0..n*n-1));
  @ requires \separated (ab_c+(0..n*n-1), c+(0..n*n-1));
  @ requires \separated (ab_c+(0..n*n-1), a_bc+(0..n*n-1));
  @ requires \separated (a_bc+(0..n*n-1), a+(0..n*n-1));
  @ requires \separated (a_bc+(0..n*n-1), b+(0..n*n-1));
  @ requires \separated (a_bc+(0..n*n-1), c+(0..n*n-1));
  @ requires n >= 0;
  @ requires \valid_read(a+(0..n*n-1));
  @ requires \valid_read(b+(0..n*n-1));
  @ requires \valid_read(c+(0..n*n-1));
  @ requires \valid(ab+(0..n*n-1));
  @ requires \valid(bc+(0..n*n-1));
  @ requires \valid(a_bc+(0..n*n-1));
  @ requires \valid(ab_c+(0..n*n-1));
  @ assigns ab[0..n*n-1], bc[0..n*n-1], a_bc[0..n*n-1], ab_c[0..n*n-1];
  @ ensures matrix_eq{Post,Post} (a_bc,ab_c,n);
*/
void matrix_mult_assoc(int a[], int b[], int c[], int ab[], int bc[], int ab_c[], int a_bc[], int n) {
  L1:
  matrix_mult (a, b, ab, n);
  //@ assert matrix_eq{L1,Here} (a, a, n);
  //@ assert matrix_eq{L1,Here} (b, b, n);
  //@ assert matrix_eq{L1,Here} (c, c, n);
  //@ assert \forall integer i, j; 0 <= i < n && 0 <= j < n ==> ab[i*n+j] == sum(a, b, n, i, j, n);
  L2:
  matrix_mult (ab, c, ab_c, n);
  //@ assert matrix_eq{L1,Here} (a, a, n);
  //@ assert matrix_eq{L1,Here} (b, b, n);
  //@ assert matrix_eq{L1,Here} (c, c, n);
  //@ assert matrix_eq{L2,Here} (ab, ab, n);
  //@ assert \forall integer i, j; 0 <= i < n && 0 <= j < n ==> ab[i*n+j] == sum(a, b, n, i, j, n);
  //@ assert \forall integer i, j; 0 <= i < n && 0 <= j < n ==> ab_c[i*n+j] == sum(ab, c, n, i, j, n);
  L3:
  matrix_mult (b, c, bc, n);
  //@ assert matrix_eq{L1,Here} (a, a, n);
  //@ assert matrix_eq{L1,Here} (b, b, n);
  //@ assert matrix_eq{L1,Here} (c, c, n);
  //@ assert matrix_eq{L2,Here} (ab, ab, n);
  //@ assert matrix_eq{L3,Here} (ab_c, ab_c, n);
  //@ assert \forall integer i, j; 0 <= i < n && 0 <= j < n ==> ab[i*n+j] == sum(a, b, n, i, j, n);
  //@ assert \forall integer i, j; 0 <= i < n && 0 <= j < n ==> ab_c[i*n+j] == sum(ab, c, n, i, j, n);
  //@ assert \forall integer i, j; 0 <= i < n && 0 <= j < n ==> bc[i*n+j] == sum(b, c, n, i, j, n);
  L4:
  matrix_mult (a, bc, a_bc, n);
  //@ assert matrix_eq{L1,Here} (a, a, n);
  //@ assert matrix_eq{L1,Here} (b, b, n);
  //@ assert matrix_eq{L1,Here} (c, c, n);
  //@ assert matrix_eq{L2,Here} (ab, ab, n);
  //@ assert matrix_eq{L3,Here} (ab_c, ab_c, n);
  //@ assert matrix_eq{L4,Here} (bc, bc, n);
  //@ assert \forall integer i, j; 0 <= i < n && 0 <= j < n ==> ab[i*n+j] == sum(a, b, n, i, j, n);
  //@ assert \forall integer i, j; 0 <= i < n && 0 <= j < n ==> a_bc[i*n+j] == sum(a, bc, n, i, j, n);
  //@ assert \forall integer i, j; 0 <= i < n && 0 <= j < n ==> bc[i*n+j] == sum(b, c, n, i, j, n);
  //@ assert \forall integer i, j; 0 <= i < n && 0 <= j < n ==> ab_c[i*n+j] == sum(ab, c, n, i, j, n);
  /*@ assert matrix_eq{Here,Here} (a_bc, ab_c, n);
  */
}
