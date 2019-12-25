/*@ ghost int test = 0;*/

/*@ predicate best(int *pat,int n, int *a) = \forall int k; 0 <= k < n ==> pat[k] == a[k];*/
/*@ predicate less(int *pat,int n, int *a) = \exists int p; 0 <= p <= n && best(pat,p,a) && pat[p] != a[p] && (\forall int k; p < k < n ==> pat[k] == a[k-1]);*/
/*@ predicate bad(int *pat,int n, int *a) = \exists int p,q; 0 <= p < q <= n && best(pat,p,a) && pat[p] != a[p] && (\forall int k; p < k < q ==> pat[k] == a[k-1]) && pat[q] != a[q-1];*/

/*@ requires n >= 0;
  @ ensures \result == 1 && test == 0 ==> best(pat,n,a);
  @ ensures \result == 1 && test == 1 ==> less(pat,n,a);
  @ ensures \result == 0 && test == 0 ==> \false;
  @ ensures \result == 0 && test == 1 ==> !best(pat,n,a);
  @ ensures \result == 0 && test == 1 ==> bad(pat,n,a);
  @ assigns test;
*/
int isRelaxedPrefix(int pat[], int n, int a[]){
  int shift = 0;
  int i = 0;
  /*@ ghost int p = 0;*/
  /*@ ghost test = 0;*/

  /*@ loop assigns i,shift,p,test;
    @ loop invariant 0 <= i <= n;
    @ loop invariant 0 <= p <= i;
    @ loop invariant 0 <= shift <= 1;
    @ loop invariant shift == 0 ==> i == p;
    @ loop invariant shift == 1 ==> i > p;
    @ loop invariant shift == test;
    @ loop invariant \forall int k; 0 <= k < p ==> pat[k] == a[k];
    @ loop invariant shift == 1 ==> pat[p] != a[p];
    @ loop invariant \forall int k; p < k < i ==> pat[k] == a[k-1];
    @ loop variant n - i;
 */
  for(i=0; i < n; i++){
    if(pat[i]!=a[i-shift])
      if(shift==0)
	shift=1;
      else
	return  0;
    /*@ ghost if(shift == 0) p = p+1;*/
    /*@ ghost test = shift;*/
  }
  return 1;
}
