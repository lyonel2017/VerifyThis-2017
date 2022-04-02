#include <stdlib.h>

#define N 1000

#define empty_array {{0}, 0}

typedef struct array {
  int a[N];
  unsigned int index;
} array;

/*@ logic integer length (array a) = a.index;
    logic int get (array a, unsigned int i) = a.a[i];
    predicate wf (array a) = a.index <= N;
*/

typedef struct sr {
  array runs;
  array data;
} sr;

/*@ predicate wf_sr(sr r) = wf(r.runs) && wf(r.data);
*/

/*@ requires wf(a);
    requires i < a.index;
    terminates \true;
    assigns \nothing;
    ensures \result == a.a[i];
*/
int get (array a, unsigned int i) {
  return a.a[i];
}

/*@ requires wf(a);
    terminates \true;
    assigns \nothing;
    ensures \result == a.index;
*/
unsigned int length (array a) {
  return a.index;
}

/*@ requires wf(a);
    terminates \true;
    assigns \nothing;
    ensures wf(\result);
    ensures \result.index == a.index + 1;
    ensures \result.a[a.index] == x;
    ensures \forall integer i; 0 <= i < a.index ==> \result.a[i] == a.a[i];
*/
array push_back (array a, int x) {
  if (a.index < N) {
    a.a[a.index++] = x;
  } else { exit(1); };
  return a;
}

/*@ requires wf_sr(r1);
    requires wf_sr(r2);
    terminates \true;
    assigns \nothing;
*/
sr merge (sr r1, sr r2) {
  sr res = {empty_array, empty_array};
  unsigned int di1 = 0;
  unsigned int di2 = 0;
  unsigned int ri1 = 0;
  unsigned int ri2 = 0;

  /*@ loop invariant 0 <= ri1 <= length(r1.runs);
      loop invariant 0 <= ri2 <= length(r2.runs);
      loop invariant wf(res.data);
      loop assigns res.data, ri1, ri2;
      loop variant length (r1.runs) + length (r2.runs) - ri1 - ri2;
  */
  while (ri1 < length (r1.runs) || ri2 < length(r2.runs)) {
    int t1 = ri1 < length(r1.runs) && (ri2 == length(r2.runs) || get(r1.data,di1) <= get(r2.data,di2));
    int t2 = ri2 < length(r2.runs) && (ri1 == length(r1.runs) || get(r2.data,di2) <= get(r1.data,di1));

    if (t1) {
      /*@ loop invariant wf(res.data);
	@ loop invariant 0 <= di1 <= get(r1.runs,ri1); 
          loop assigns res, di1;
          loop variant get(r1.runs,ri1) - di1;
      */
      for (; di1 < get(r1.runs,ri1); ++di1) {
        res.data = push_back(res.data, get(r1.data,di1));
      }
      ++ri1;
    }

    if (t2) {
      /*@ loop invariant wf(res.data);
	@ loop invariant 0 <= di1 <= get(r1.runs,ri1);
          loop assigns res, di2;
          loop variant get(r2.runs,ri2) - di2;
      */
      for (; di2 < get(r2.runs,ri2); ++di2) {
        res.data = push_back(res.data, get(r2.data,di2));
      }
      ++ri2;
    }

    res.runs = push_back(res.runs, length(res.data));
  }

  return res;
}

/*@ requires l <= h;
    terminates \true;
*/
sr msort (array a, int l, int h) {
  sr res = {empty_array,empty_array};
  if (l == h) return res;
  if (h - l == 1) {
    res.data = push_back(res.data, get(a,l));
    res.runs = push_back(res.runs, length(res.data));
    return res;
  }

  int m = l + (h-l)/2;

  sr res1 = msort(a,l,m);
  sr res2 = msort(a,m,h);
  return merge(res1, res2);
}

