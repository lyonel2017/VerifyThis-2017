void pair_sort(int a[], int n) {
  int i = 0; // i is running index (inc by 2 every iteration)

  while (i < n-1) {
    int x = a[i];	// let x and y hold the next to elements in A
    int y = a[i+1];

    if (x < y) {	// ensure that x is not smaller than y
        int tmp = x;
        x = y;
        y = tmp;
    }

    int j = i - 1;	// j is the index used to find the insertion point
    while (j >= 0 && a[j] > x)	{// find the insertion point for x
       a[j+2] = a[j];	// shift existing content by 2
       j = j - 1;
    }

    a[j+2] = x;	// store x at its insertion place
	// A[j+1] is an available space now

    while (j >= 0 && a[j] > y) {	// find the insertion point for y
        a[j+1] = a[j];	// shift existing content by 1
        j = j - 1;
    }
    a[j+1] = y;	// store y at its insertion place

    i = i+2;
  }

  if (i == n-1) {	// if length(A) is odd, an extra
    int y = a[i];	// single insertion is needed for 
    int j = i - 1;	// the last element
    while (j >= 0 && a[j] > y) {
        a[j+1] = a[j];
        j = j - 1;
    }
    a[j+1] = y;
  }
}

