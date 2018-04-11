/*@ axiomatic Num{
     logic integer num{L}(int *t, integer i, integer j, integer n)
          reads t[..] ;
     axiom num1{L} :
       \forall int *t, integer i, j, n; !(0 <= i <= i+j < n && t[i] == t[i+j]) ==> num(t,i,j,n) == 0;
     axiom num2{L} :
       \forall int *t, integer i, j, n; 0 <= i <= i+j < n && t[i] == t[i+j] ==> num(t,i,j,n) == num(t,i+1,j,n) + 1;
     lemma num3{L} :
       \forall int *t, integer i,j,n,l,p;
       0 <= i <= i+j <= p < n ==> num(t,i,j,n) == num(t,i,j,p) + num(t,p-j,j,n);
     lemma num4{L} :
       \forall int *t, integer i,j,n,p,k,l;
       0 <= i <= k < i+j <= l < n < p && t[k] != t[l] ==> num(t,i,j,n) == num(t,i,j,p);

}*/

/*@ requires 0 <= x <= y < n;
  @ requires \valid(t+(0..n));
  @ ensures \result == num(t,x,x-y,n);
  //@ ensures \forall int p; 0 <= p < \result ==> t[x+p] == t[y+p];
*/
int lcp(int t[], int x, int y, int n) {
  int l = 0;
  /*@ loop assigns l;
    @ loop invariant 0 <= y+l <= n;
    @ loop invariant y-x >= 0;
    //@ loop invariant \forall int p; 0 <= p < l ==> t[x+p] == t[y+p];
    @ loop invariant l == num(t,x,y-x,y+l);
    @ loop variant n - l;
  */
  while (x+l<n && y+l<n && t[x+l]==t[y+l]) {
    l++;
  }
  return l;
}
