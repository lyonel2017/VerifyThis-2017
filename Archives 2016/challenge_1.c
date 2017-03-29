/*@ axiomatic Sum {
  @   // sum(t,i,j) denotes t[i]+...+t[j-1]
  @   logic integer sum{L}(int *t, integer i, integer j)
  @        reads i,j,t, t[..] ;
  @   axiom sum1{L} :
  @     \forall int *t, integer i, j; i >= j ==> sum(t,i,j) == 0;
  @   axiom sum2{L} :
  @     \forall int *t, integer i, j; i <= j ==>
  @       sum(t,i,j+1) == sum(t,i,j) + t[j];
  @ }
  @*/

/*@ lemma sum3{L} :
  @     \forall int *t, integer i, j, k;
  @       i <= j <= k ==>
  @         sum(t,i,k) == sum(t,i,j) + sum(t,j,k);
  @*/

/*@ lemma sum_footprint{L} :
  @     \forall int *t1,*t2, integer i, j;
  @       (\forall integer k; i<=k<j ==> t1[k] == t2[k]) ==>
  @       sum(t1,i,j) == sum(t2,i,j);
  @*/

/* predicate matrix_mult();*/


/*@ requires \valid(a+(0..n*n);
    requires \valid(b+(0..n*n);
    requires \valid(c+(0..n*n);
    assigns c[0..n*n];
*/
int[] matrixMultiply(int[] a, int[] b, int[] c,int n) {

    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
           for (int k = 0; k < n; k++) {
	     /*@ loop invariant  */
                       c[i*n+j] += a[i*n+k] * b[k*n+j];
                   }
           }
    }
    return c;
 }
