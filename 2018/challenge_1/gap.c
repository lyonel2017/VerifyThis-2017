#define MAX 1000

char a[MAX];
int l, r, n;

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

/*@ requires 0 <= l < r < n;
    ensures \forall integer i; 0 <= i < \old(l) ==> nth(i) == \old(nth(i));
    ensures nth(\old(l)) == c;
    ensures \forall integer i; \old(l)+1 <= i < n - (r-l) ==> nth(i) == \old(nth(i-1));
    assigns l, a[l];
*/
void insert (char c)
{
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
*/
void delete () {
  if (l != 0) {
    l = l - 1;
  }
}
