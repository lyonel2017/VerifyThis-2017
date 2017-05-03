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


  @   lemma sum_5{l} :
  @     \forall int *t, integer i, j, k;
  @       0 <= i <= j <= k && sum(t,i,j) >= 0 && sum(t,j,k) >= 0 ==>
  @         sum(t,i,k) >= sum(t,i,j) + sum(t,j,k);    
  @   lemma sum_6{l} :
  @     \forall int *t, integer i, j, k;
  @       0 <= i <= j <= k && sum(t,i,j) >= 0 && sum(t,j,k) >= 0 && sum(t,i,k) >= sum(t,i,j) + sum(t,j,k)==>
  @         sum(t,i,k) >= sum(t,i,j) &&  sum(t,i,k) >= sum(t,j,k); 
  @   lemma sum_7{l} :
  @     \forall int *t, integer i, j, k;
  @       0 <= i <= j <= k && sum(t,i,k) < sum(t,i,j) + sum(t,j,k) ==>
  @         (sum(t,i,k) < sum(t,i,j) || sum(t,i,k) < sum(t,j,k));   
  @ }
  @*/

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
    /*@ loop assigns i, max_so_far, max_ending_here,x;
      @ loop invariant 0 <= i <= size;
      @ loop invariant 0 <= x <= size;
      @ loop invariant x <= i;
      @ loop invariant max_ending_here == sum(a,x,i);
      @ loop invariant \forall integer m,n; x <= m <= n <= i ==> max_ending_here >= sum(a,m,n);
      @ loop invariant max_so_far >= max_ending_here >= 0;
      @ loop invariant \exists integer m,n; 0 <= m <= n <= i && max_so_far == sum(a,m,n);
      @ loop invariant \forall integer m,n; 0 <= m <= n <= i ==> max_so_far >= sum(a,m,n);
      @ loop variant size - i;
     */
    for (int i = 0; i < size; i++){
      /*@ ghost L:;*/  
      max_ending_here = max_ending_here + a[i];
      if (max_ending_here < 0){ 
	max_ending_here = 0;
	/*@ ghost x = i+1;*/
      }
      else{ 
	if (max_so_far < max_ending_here){ 
	  max_so_far = max_ending_here;
	}
      }
      /*@ assert max_so_far == \at(max_so_far, L) || max_so_far == max_ending_here;*/
      /*@ assert max_ending_here == 0 || max_ending_here == sum(a,x,i+1);*/
      /*@ assert max_so_far >= \at(max_so_far,L);*/
    }
    return max_so_far;
}
