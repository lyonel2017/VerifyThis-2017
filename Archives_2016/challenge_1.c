/*@ axiomatic Sum_matrix {
  @   logic integer sum_matrix{L}(int **a, int **b, integer i, integer j, integer f, integer n)
  @        reads a[i][0..f],b[0..f][j];
  @   axiom sum_matrix_1{L} :
  @     \forall int **a, int **b, integer i, j, f,n; f <= 0 && 0 <= i < n && 0 <= j < n ==> sum_matrix(a,b,i,j,f,n) == 0;
  @   axiom sum_matrix_2{L} :
  @     \forall int **a, int **b, integer i, j, f,n; 0 < f+1 <= n && 0 <= i < n && 0 <= j < n ==> sum_matrix(a,b,i,j,f+1,n) == sum_matrix(a,b,i,j,f,n) + a[i][f] * b[f][j];
  @}
  @*/

/*@ predicate matrix_prod(int **a, int **b, int **c, integer n) =
   \forall integer i,j; 0 <= i < n && 0 <= j < n ==> c[i][j] == sum_matrix(a,b,i,j,n,n);*/

/*@ requires n >= 0;
  @ requires \valid(a+(0..n-1));
  @ requires \valid(b+(0..n-1));
  @ requires \valid(c+(0..n-1));
  @ requires \forall integer y1,y2; 0 <= y1 < n && 0 <= y2 < n ==> \separated(a+y1,c+y2);
  @ requires \forall integer y1,y2; 0 <= y1 < n && 0 <= y2 < n ==> \separated(b+y1,c+y2);
  @ requires \forall integer y1,y2; 0 <= y1 < n && 0 <= y2 < n && y1 != y2 ==> \separated(c+y1,c+y2);
  @ requires \forall integer k; 0 <= k < n ==> \valid(a[k]+(0..n-1));
  @ requires \forall integer k; 0 <= k < n ==> \valid(b[k]+(0..n-1));
  @ requires \forall integer k; 0 <= k < n ==> \valid(c[k]+(0..n-1));
  @ requires \forall integer x1,x2,y1,y2; 0 <= x1 < n && 0 <= x2 < n && 0 <= y1 < n && 0 <= y2 < n && x1 != x2 ==> \separated(c[x1]+y1,c[x2]+y2);
  @ requires \forall integer x1,x2,y1,y2; 0 <= x1 < n && 0 <= y1 < n && 0 <= y2 < n && y1 != y2 && x1 == x2 ==> \separated(c[x1]+y1,c[x2]+y2);
  @ requires \forall integer x1,x2,y1,y2; 0 <= x1 < n && 0 <= x2 < n && 0 <= y1 < n && 0 <= y2 < n ==> \separated(c[x1]+y1,a[x2]+y2);
  @ requires \forall integer x1,x2,y1,y2; 0 <= x1 < n && 0 <= x2 < n && 0 <= y1 < n && 0 <= y2 < n ==> \separated(c[x1]+y1,b[x2]+y2);
  @ requires \forall integer x1,y1,y2; 0 <= x1 < n && 0 <= y1 < n && 0 <= y2 < n ==> \separated(c[x1]+y1,c+y2);
  @ requires \forall integer x1,y1,y2; 0 <= x1 < n && 0 <= y1 < n && 0 <= y2 < n ==> \separated(a[x1]+y1,c+y2);
  @ requires \forall integer x1,y1,y2; 0 <= x1 < n && 0 <= y1 < n && 0 <= y2 < n ==> \separated(b[x1]+y1,c+y2);
  @ requires \forall integer x1,y1,y2; 0 <= x1 < n && 0 <= y1 < n && 0 <= y2 < n ==> \separated(c[x1]+y1,a+y2);
  @ requires \forall integer x1,y1,y2; 0 <= x1 < n && 0 <= y1 < n && 0 <= y2 < n ==> \separated(c[x1]+y1,b+y2);
  @ requires \forall int i,j; 0 <= i < n && 0 <= j < n ==> c[i][j] == 0;
  @ assigns c[0..n-1][0..n-1];
  @ ensures matrix_prod(a,b,c,n);
*/
void matrixMultiply(int **a, int **b, int **c,int n) {
  /*@ loop invariant 0 <= i <= n;
    @ loop invariant \forall integer p,t; 0 <= p < n && i <= t < n ==> c[t][p] == 0;
    @ loop invariant \forall integer p,t; 0 <= p < n && 0 <= t < i ==> c[t][p] == sum_matrix(a,b,t,p,n,n);
    @ loop invariant \forall integer i,j; 0 <= i < n && 0 <= j < n ==> a[i][j] == \at(a,Pre)[i][j];
    @ loop invariant \forall integer i,j; 0 <= i < n && 0 <= j < n ==> b[i][j] == \at(b,Pre)[i][j];
    @ loop assigns i,c[0..n-1][0..n-1];*/
    for (int i = 0; i < n; i++) {
      /*@ ghost K:;*/
      /*@ loop invariant 0 <= i < n;
	@ loop invariant 0 <= k <= n;
	@ loop invariant i == \at(i,K);
	@ loop invariant \forall integer p,t; 0 <= p < n && i < t < n ==> c[t][p] == 0;
	@ loop invariant \forall integer p,t; 0 <= p < n && 0 <= t < i ==> c[t][p] == sum_matrix(a,b,t,p,n,n);
	@ loop invariant \forall integer p,t; 0 <= p < n && 0 <= t < i ==> c[t][p] == \at(c,K)[t][p];
	@ loop invariant \forall integer p; 0 <= p < n ==> c[i][p] == sum_matrix(a,b,i,p,k,n);
	@ loop invariant \forall integer i,j; 0 <= i < n && 0 <= j < n ==> a[i][j] == \at(a,Pre)[i][j];
	@ loop invariant \forall integer i,j; 0 <= i < n && 0 <= j < n ==> b[i][j] == \at(b,Pre)[i][j];
	@ loop assigns i,k,c[i][0..n-1];*/
      for (int k = 0; k < n; k++) {
	/*@ ghost I:;*/
	/*@ loop invariant 0 <= i < n;
	  @ loop invariant 0 <= j <= n;
	  @ loop invariant 0 <= k < n;
	  @ loop invariant i == \at(i,K);	
	  @ loop invariant i == \at(i,I);
	  @ loop invariant k == \at(k,I);
	  @ loop invariant \forall integer p,t; 0 <= p < n && i < t < n ==> c[t][p] == 0;
	  @ loop invariant \forall integer p,t; 0 <= p < n && 0 <= t < i ==> c[t][p] == \at(c,I)[t][p];
	  @ loop invariant \forall integer p,t; 0 <= p < n && 0 <= t < i ==> c[t][p] == \at(c,K)[t][p];
	  @ loop invariant \forall integer p,t; 0 <= p < n && 0 <= t < i ==> c[t][p] == sum_matrix(a,b,t,p,n,n);
	  @ loop invariant \forall integer p; j <= p < n ==> c[i][p] == \at(c,K)[i][p];
	  @ loop invariant \forall integer p; j <= p < n ==> c[i][p] == \at(c,I)[i][p];
	  @ loop invariant \forall integer p; j <= p < n ==> c[i][p] == sum_matrix(a,b,i,p,k,n);
	  @ loop invariant \forall integer p; 0 <= p < j ==> c[i][p] == sum_matrix(a,b,i,p,k+1,n);
	  @ loop invariant \forall integer i,j; 0 <= i < n && 0 <= j < n ==> a[i][j] == \at(a,Pre)[i][j];
	  @ loop invariant \forall integer i,j; 0 <= i < n && 0 <= j < n ==> b[i][j] == \at(b,Pre)[i][j];
	  @ loop assigns i,j,k,c[i][0..n-1];*/
           for (int j = 0; j < n; j++) {
                 c[i][j] = c[i][j] + a[i][k] * b[k][j];
	   }
      }
    }
    return;
 }
