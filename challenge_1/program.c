/*@ requires n >= 0;
    requires \valid(a+(0..n-1));
    assigns a[0..n-1];
    ensures \forall integer i, j; 0 <= i <= j < n ==> a[i] <= a[j];
*/
void pair_sort(int a[], int n) {
  int i = 0; // i is running index (inc by 2 every iteration)

  /*@ loop invariant \forall integer k, j; 0 <= k <= j < i ==> a[k] <= a[j];
      loop assigns i, a[0..n-1];
      loop variant n - 1 - i;
  */
  while (i < n-1) {
    int x = a[i];	// let x and y hold the next to elements in A
    int y = a[i+1];

    if (x < y) {	// ensure that x is not smaller than y
        int tmp = x;
        x = y;
        y = tmp;
    }

    int j = i - 1;	// j is the index used to find the insertion point
    /*@ loop invariant \forall integer k; j+2 <= k < i+1 ==> x < a[k];
        loop assigns a[0..n-1], j;
    */
    while (j >= 0 && a[j] > x)	{// find the insertion point for x
       a[j+2] = a[j];	// shift existing content by 2
       j = j - 1;
    }

    //@ assert \forall integer k, l; j+3 <= k <= l < i+1 ==> a[k] <= a[l];
    a[j+2] = x;	// store x at its insertion place
	// A[j+1] is an available space now
    //@ assert \forall integer k, l; j+2 <= k <= l < i+1 ==> a[k] <= a[l];

    /*@ loop invariant \forall integer k; j+1 <= k < i+1 ==> y < a[k];
        loop assigns a[0..n-1], j;
    */
    while (j >= 0 && a[j] > y) {	// find the insertion point for y
        a[j+1] = a[j];	// shift existing content by 1
        j = j - 1;
    }
    a[j+1] = y;	// store y at its insertion place

    //@ assert \forall integer k, l; 0 <= k <= l < i+1 ==> a[k] <= a[l];

    i = i+2;
  }

  //@ assert \forall integer i, j; 0 <= i <= j < n - 1 ==> a[i] <= a[j];
  if (i == n-1) {	// if length(A) is odd, an extra
    int y = a[i];	// single insertion is needed for 
    int j = i - 1;	// the last element
    /*@ loop invariant \forall integer k, l; j < k < n ==> y < a[j];
        loop assigns j, a[0..n-1];
    */
    while (j >= 0 && a[j] > y) {
        a[j+1] = a[j];
        j = j - 1;
    }
    a[j+1] = y;
  }
}

