#define MAX 1000

char a[MAX];
int l, r, n;

/*@ axiomatic nth {
  logic int nth(integer i) = i < l ? a[i] : a[i+r-l];
}
*/

/*@ ensures \forall integer i; 0 <= i < n - (r - l) ==> nth(i) == \at(nth(i), Pre);
 */
void left()
{
  if (l != 0) {
    l = l - 1;
    r = r - 1;
    a[r] = a[l];
  }
}

//@ requires l < r;
void insert (char c)
{
   a[l] = c;
   l = l + 1;
}

void delete () {
  if (l != 0) {
    l = l - 1;
  }
}
