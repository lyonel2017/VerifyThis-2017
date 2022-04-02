#define N 1000

#define empty_array {{0}, 0}

typedef struct array {
  int a[N];
  int index;
} array;

typedef struct sr {
  array runs;
  array data;
} sr;

int get (array a, int i) {
  return a.a[i];
}

int length (array a) {
  return a.index;
}

array push_back (array a, int x) {
  if (a.index < N) {
    a.a[a.index++] = x;
  };
  return a;
}

sr merge (sr r1, sr r2) {
  sr res = {empty_array, empty_array};
  int di1 = 0;
  int di2 = 0;
  int ri1 = 0;
  int ri2 = 0;

  while (ri1 < length (r1.runs) || ri1 < length(r2.runs)) {
    int t1 = ri1 < length(r1.runs) && (ri2 == length(r2.runs) || get(r1.data,di1) <= get(r2.data,di2));
    int t2 = ri2 < length(r2.runs) && (ri1 == length(r1.runs) || get(r2.data,di2) <= get(r1.data,di1));

    if (t1) {
      for (; di1 < get(r1.runs,ri1); ++di1) {
        res.data = push_back(res.data, get(r1.data,di1));
      }
      ++ri1;
    }

    if (t2) {
      for (; di2 < get(r2.runs,ri2); ++di2) {
        res.data = push_back(res.data, get(r2.data,di2));
      }
      ++ri2;
    }

    res.data = push_back(res.data, length(res.data));
  }

  return res;
}

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

