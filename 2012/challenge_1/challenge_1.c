#include <stdio.h>
#include <stdlib.h>

/*@ axiomatic lcp{
  @ predicate cp(int* t, int x, int y, int n, integer l) = 0 <= l <= n - \max(x,y) && (\forall integer i; 0 <= i < l ==> t[x+i] == t[y+i]);
  @ predicate lcp(int* t, int x, int y, int n, integer l) = cp(t, x, y, n, l) && (\forall integer k; cp(t, x, y, n, k) ==> 0 <= k <= l);
}*/

/*@ requires 0 <= x < n;
  @ requires 0 <= y < n;
  @ requires \valid(t+(0..n));
  @ ensures lcp(t, x, y, n, \result);
  @ assigns \nothing;
*/
int lcp(int t[], int x, int y, int n) {
  int l = 0;
  /*@ loop assigns l;
    @ loop invariant 0 <= y+l <= n;
    @ loop invariant 0 <= x+l <= n;
    @ loop invariant cp(t, x, y, n, l);
    @ loop variant n - l;
  */
  while (x+l<n && y+l<n && t[x+l]==t[y+l]) {
    l++;
  }
  return l;
}

//use behavior and proof complete and disjoint
// define a corresponding lexicographical oder predicate/logical function

/*@ requires 0 <= x < n;
  @ requires 0 <= y < n;
  @ requires \valid(t+(0..n));
  @ ensures x == y ==> \result == 0;
  @ ensures x != y ==> lcp(t, x, y, n, n-x) ==> \result == -1;
  @ ensures x != y ==> lcp(t, x, y, n, n-y) ==> \result == 1;
  @ ensures x != y ==> \forall integer l; lcp(t, x, y, n, l) ==> l < n - \max(x,y) ==> t[x+l] < t[y+l] ==> \result == -1;
  @ ensures x != y ==> \forall integer l; lcp(t, x, y, n, l) ==> l < n - \max(x,y) ==> t[x+l] > t[y+l] ==> \result == 1;
*/
int compare(int* t, int x, int y, int n) {
  if (x == y) return 0;

  int l = lcp (t, x, y, n);

  if (l == n-x ) return -1;
  if (l == n-y) return 1;
  if (t[x+l] < t[y+l]) return -1;
  if (t[x+l] > t[y+l]) return 1;

  exit(0);
}

/*@ requires \valid(x) && \valid(y);
  @ requires \separated(x,y);
  @ ensures *x == \old(*y) && *y == \old(*x);
  @ assigns *x,*y;*/
void swap(int *x, int *y){
  int t = *x;
  * x = *y;
  *y = t;
}

// proof that the array is sort correspond to the lexicographical oder and no element are lost
void sort(int* t, int* suffixes, int n) {
  for(int i = 0; i < n; i++) {
    int j = i;
    while(j > 0 && compare(t, suffixes[j - 1], suffixes[j], n) > 0) {
      swap(suffixes+j,suffixes+(j-1));
      j--;
    }
  }
}

void suffixArray(int* t, int* suffixes, int n) {
  for (int i = 0; i < n; i++) suffixes[i] = i;
  sort(t,suffixes,n);
}

void doLRS(int* t, int* suffixes, int n, int* solStart, int* solLength) {
  suffixArray(t, suffixes, n);
  *solStart = 0;
  *solLength = 0;

  for (int i=1; i < n; i++) {
    int length = lcp(t,suffixes[i], suffixes[i-1],n);
    if (length > *solLength) {
      *solStart = suffixes[i];
      *solLength = length;
    }
  }
}

int main (){
  int t[4] = {8,8,8,8};
  int suffixes [4];
  int solStart;
  int solLength;

  doLRS(t,suffixes,4,&solStart,&solLength);
  printf("Start %d, Length %d\n",solStart,solLength);

  return 1;
}
