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
  @ }
  @*/

/*@ axiomatic count {
    logic integer CARD (set<\list<boolean> > s);
    logic set<\list<boolean> > FILTER (integer i);  //{ x | x in U and p x}
} */

/*@ ensures main_post : \result== CARD(FILTER (50));
    assigns \nothing;
 */
int counting ()
{
  int count[51];
  count[0] = 1;
  count[1] = 1;
  count[2] = 1;
  count[3] = 2;
  /*@ loop invariant 4 <= n <= 51;
      loop invariant main_outer : \forall integer i; 0 <= i < n ==> count[i] == CARD(FILTER(i));
      loop assigns n, count[0..50];
      loop variant 50-n;
  */
  for(int n = 4; n <= 50; n++) {
    count[n] = count[n-1];
    /*@ loop invariant bounds : 3 <= k <= n;
        loop invariant main_inner : count[n] == \at(count[n], LoopEntry) + sum{LoopEntry}(count+0, n-k, n-3);
        loop assigns k, count[n];
        loop variant n-k;
    */
    for (int k = 3; k <= n - 1; k++) {
      count[n] = count[n] + count[n-k-1];
    }
    count[n] = count[n]+1;
  }
  return count[50];
}
