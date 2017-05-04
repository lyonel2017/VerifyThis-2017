/*@ axiomatic Sum {
  @   logic integer sum{L}(int *t, integer i, integer j)
  @        reads t[..] ;
  @   axiom sum1{L} :
  @     \forall int *t, integer i, j; i >= j ==> sum(t,i,j) == 0;
  @   axiom sum2{L} :
  @     \forall int *t, integer i, j; i <= j ==>
  @       sum(t,i,j+1) == sum(t,i,j) + t[j];
  @   lemma sum3{L} :
  @     \forall int *t, integer i, j, k;
  @       0 <= i <= j <= k ==>
  @         sum(t,i,k) == sum(t,i,j) + sum(t,j,k);
  @   lemma sum_4{L1,L2} :
  @     \forall int *t, integer i, j; 
  @       (\forall integer k; i <= k < j ==> \at(t[k],L1) == \at(t[k],L2)) ==>
  @       \at(sum(t,i,j),L1) == \at(sum(t,i,j),L2);
  @   lemma sum5{L} :
  @     \forall int *t, integer i, j;
  @       0 <= i <= j && t[j] < 0 ==>
  @         sum(t,i,j) > sum(t,i,j+1);
  @ }
  @*/

/*@ axiomatic sum_max {
     logic integer sum_max(int* a, integer i, integerj);
     logic integer sum_suf_max(int* a, integer i, integerj);

     axomatic sum_max1{L}: 
         \forall int *a,integer i,j; 
	     \exists integer m,n; 0 <= i <= m <= n <= j && sum_max(a,i,j) == sum(a,m,n) && sum_max(a,i,j) >= sum(a,i,); ;

     axomatic sum_max2{L}: 
         \forall int *a,integer i,j,n,m;
	     0 <= i <= m <= n <= j ==> sum_max(a,i,j) >= sum(a,m,n);

     axomatic sum_max3{L}: 
         \forall int *a,integer i,j; 
	     \exists integer n; 0 <= i <= n <= j && sum_suf_max(a,i,j) == sum(a,n,j);

     axomatic sum_max4{L}: 
         \forall int *a,integer i,j,m;
	     0 <= i <= m <= j ==> sum_suf_max(a,i,j) >= sum(a,m,j);

     lemma sum_max5{L]:
        \forall int *a,integer n;
            sum_max(a,0,n+1) == \max(sum_max(a,0,n),sum_suf_max(a,0,n) + a[n+1])
}
*/

/*@ requires size >= 0;
  @ requires \valid(a+(0..size));
  @ assigns \nothing;
  @ ensures \result >= 0;
  @ ensures \forall integer m,n; 0 <= m <= n <= size ==> \result >= sum(a,m,n);
  @ ensures \exists integer m,n; 0 <= m <= n <= size && \result == sum(a,m,n);
*/
int maxSubArraySum(int a[], int size)
{
    int max_so_far = 0, max_ending_here = 0;
    /*@ ghost int x = 0;*/
    /*@ ghost int y = 0;*/
    /*@ loop assigns i, max_so_far, max_ending_here,x,y;
      @ loop invariant 0 <= i <= size;
      @ loop invariant 0 <= x <= size;
      @ loop invariant x <= i;
      @ loop invariant 0 <= y <= size;
      @ loop invariant y <= i;
      @ loop invariant max_ending_here == sum(a,x,i);
      @ loop invariant max_so_far >= max_ending_here >= 0;
      @ loop invariant \exists integer m,n; 0 <= m <= n <= i && max_so_far == sum(a,m,n);
      @ loop invariant \forall integer m,n; 0 <= m <= n <= y ==> max_so_far >= sum(a,m,n);
      @ loop variant size - i;
     */
    for (int i = 0; i < size; i++){
      /*@ ghost L:;*/  
      max_ending_here = max_ending_here + a[i];
      if (max_ending_here < 0){ 
	max_ending_here = 0;
	/*@ assert max_ending_here > max_ending_here + a[i];*/
	/*@ ghost x = i+1;*/
	/*@ assert a[i] < 0;*/
      }
      else{ 
	if (max_so_far < max_ending_here){ 
	  max_so_far = max_ending_here;
	  /*@ assert a[i] >= 0;*/
	  /*@ assert max_so_far == sum(a,x,i+1);*/
	  /*@ ghost y = i+1;*/
	}
      }
      /*@ assert max_ending_here == 0 || max_ending_here == sum(a,x,i+1);*/
      /*@ assert max_so_far == \at(max_so_far, L) || max_so_far == max_ending_here;*/
      /*@ assert max_so_far >= \at(max_so_far,L);*/
    }
    return max_so_far;
}
