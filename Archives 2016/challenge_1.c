/*@ axiomatic Sum_matrix {
  @   logic integer sum_matrix{L}(int **a, int **b, integer i, integer j, integer d, integer f)
  @        reads a[i][d..f],b[d..f][j];
  @   axiom sum_matrix_1{L} :
  @     \forall int **a, int **b, integer i, j, d,f; f <= d ==> sum_matrix(a,b,i,j,d,f) == 0;
  @   axiom sum_matrix_2{L} :
  @     \forall int **a, int **b, integer i, j, d,f; d <= f ==> sum_matrix(a,b,i,j,d,f+1) == sum_matrix(a,b,i,j,d,f) + a[i][f] * b[f][j];
  @ }
  @*/

/*@ predicate matrix_prod(int **a, int **b, int **c, integer n) =
   \forall integer i,j; 0 <= i < n && 0 <= j < n ==> c[i][j] == sum_matrix(a,b,i,j,0,n);*/

/*@ requires n >= 0;
  @ requires \valid(a+(0..n-1));
  @ requires \valid(b+(0..n-1));
  @ requires \valid(c+(0..n-1));
  @ requires \forall integer k; 0 <= k < n ==> \valid(a[k]+(0..n-1));
  @ requires \forall integer k; 0 <= k < n ==> \valid(b[k]+(0..n-1));
  @ requires \forall integer k; 0 <= k < n ==> \valid(c[k]+(0..n-1));
  @ requires \forall integer x,y,z; 0 <= x < n && 0 <= y < n && 0 <= z < n ==> \separated(a[x]+(0..n-1),b[y]+(0..n-1),c[z]+(0..n-1),a+(0..n-1),b+(0..n-1),c+(0..n-1));
  @ requires \forall int i,j; 0 <= i < n && 0 <= j < n ==> c[i][j] == 0;
  @ assigns c[0..n-1][0..n-1];
  @ ensures matrix_prod(a,b,c,n);
*/
void matrixMultiply(int **a, int **b, int **c,int n) {

  /*@ loop invariant 0 <= i <= n;
    @ loop invariant \forall integer p,t; 0 <= p < n && 0 <= t < i ==> c[t][p] == sum_matrix(a,b,t,p,0,n);
    @ loop invariant \forall integer p,t; 0 <= p < n && i <= t < n ==> c[t][p] == 0;
    @ loop assigns i,c[0..n-1][0..n-1];*/
    for (int i = 0; i < n; i++) {
      /*@ghost M:*/
      /*@ loop invariant 0 <= i < n;
	@ loop invariant 0 <= j <= n;
	@ loop invariant \forall integer p,t; 0 <= p < j && 0 <= t < i ==> c[t][p] == sum_matrix(a,b,t,p,0,n);
	@ loop invariant \forall integer p,t; 0 <= p < n && 0 <= t < n && p != j ==> c[t][p] == \at(c[t][p],M);
	@ loop assigns i,j,c[0..n-1][0..n-1];*/
      for (int j = 0; j < n; j++) {
	/*@ghost I:*/
	/*@ loop invariant 0 <= i < n;
	  @ loop invariant 0 <= j < n;
	  @ loop invariant 0 <= k <= n;
	 /@ loop invariant c[i][j] == sum_matrix(a,b,i,j,0,k);
	  @ loop invariant \forall integer p,t; 0 <= p < n && 0 < t < n && p != j && t != i ==> c[t][p] == \at(c[t][p],I);
	  @ loop assigns i,j,k,c[i][j];*/
           for (int k = 0; k < n; k++) {
                 c[i][j] += a[i][k] * b[k][j];
	   }
      }
    }
    /* assert \false;*/
    return;
 }
