#define MAX 1000

char a[MAX];
int l, r, n;
int const K;
// global invariant K_is_positive: K > 0 ;

/*@ axiomatic nth {
  logic int nth(integer i) = i < l ? a[i] : a[i+r-l];
}
*/

/*@ requires 0 <= l <= r < n;
    ensures \forall integer i; 0 <= i < n - (r - l) ==> nth(i) == \at(nth(i), Pre);
    assigns l, r, a[r-1];
*/
void left()
{
  if (l != 0) {
    l = l - 1;
    r = r - 1;
    a[r] = a[l];
  }
}

/*@ requires 0 <= l <= r < n;
    ensures \forall integer i; 0 <= i < n - (r - l) ==> nth(i) == \at(nth(i), Pre);
    assigns l, r, a[l];
*/
void right()
{
  if (l < r) {
    a[l] = a[r];
    l = l + 1;
    r = r + 1;
  }
}

/*@ requires 0 <= l < r + K < n <= 800;
    requires K > 0;
    requires l == r;
    ensures \forall integer i; 0 <= i < n - (r - l) ==> nth(i) == \at(nth(i), Pre);
    ensures l < r;
    assigns r, n, a[(r+K)..(n+K-1)];
*/
void grow()
{
  n = n + K;

  /*@ loop invariant r + K - 1 <= i <= n - 1;
      loop invariant \forall integer j; 0 <= j <= i ==> a[j] == \at(a[j], LoopEntry);
      loop invariant \forall integer j; i < j < n ==> a[j] == \at(a[j-K], LoopEntry);
      loop assigns i, a[r+K..n+K-1];
  */
  for (int i = n-1; i >= r+K; i--) {
    a[i] = a[i - K];
  }
  r = r + K;
}

/*@ requires 0 <= l <= r < n;
    requires r + K < n;
    requires K > 0;
    ensures \forall integer i; 0 <= i < \old(l) ==> nth(i) == \old(nth(i));
    ensures nth(\old(l)) == c;
    ensures \forall integer i; \old(l)+1 <= i < n - (r-l) ==> nth(i) == \old(nth(i-1));
    behavior insert:
      assumes l == r;
      assigns l, r, n, a[l], a[r+K..n+K-1];
    behavior other:
      assumes l < r;
      assigns l, a[l];
    complete behaviors;
    disjoint behaviors;
*/
void insert (char c)
{
   if (l == r) {
     grow ();
   }
   a[l] = c;
   l = l + 1;
}

/*@ requires 0 <= l <= r < n;
    behavior change:
      assumes l != 0;
      ensures \forall integer i; 0 <= i < \old(l) - 1 ==> nth(i) == \old(nth(i));
      ensures \forall integer i; \old(l) <= i < n - (r-l) ==> nth(i) == \old(nth(i+1));
      assigns l;
    behavior nothing:
      assumes l == 0;
      ensures \forall integer i; 0 <= i < n-(r-l) ==> nth(i) == \old(nth(i));
      assigns \nothing;
    complete behaviors;
    disjoint behaviors;
*/
void delete () {
  if (l != 0) {
    l = l - 1;
  }
}
