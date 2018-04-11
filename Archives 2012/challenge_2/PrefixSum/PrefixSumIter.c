/* axiomatic Sum {
     logic integer sum{L}(int *t, integer i, integer j)
          reads t[..] ;
     axiom sum1{L} :
       \forall int *t, integer i, j; i >= j ==> sum(t,i,j) == 0;
     axiom sum2{L} :
       \forall int *t, integer i, j; i <= j ==>
         sum(t,i,j+1) == sum(t,i,j) + t[j];
     lemma sum3{L} :
       \forall int *t, integer i, j, k;
         0 <= i <= j <= k ==>
           sum(t,i,k) == sum(t,i,j) + sum(t,j,k);
     lemma sum_4{L1,L2} :
       \forall int *t, integer i, j;
         (\forall integer k; i <= k < j ==> \at(t[k],L1) == \at(t[k],L2)) ==>
         \at(sum(t,i,j),L1) == \at(sum(t,i,j),L2);
}*/

/*@ axiomatic power{
  logic integer POWER(integer x, integer a);
}*/

/*@ requires length >= 2 && \exists int k; POWER(2,k) == length;*/
int upsweep(int a[], int length) {
  int space = 1;
  /*@ ghost int x = 0;*/
  /*@ loop invariant 1 <= space <= length;
    @ loop invariant POWER(2,x) == space;
    @ loop assigns space,a[0..length],x;*/
  for (; space < length; space=space*2) {
    int left = space - 1;
    /*@ loop invariant space == \at(space,LoopEntry);
      @ loop invariant space - 1 <= left <= length;
      @ loop invariant x == \at(x,LoopEntry);
      @ loop assigns left,a[0..length];*/
    while (left < length) {
      int right = left + space;
      a[right] = a[left] + a[right];
      left = left + space*2;
    }
    /*@ ghost x++;*/
  }
  return space;
}


/* void downsweep(int space, int a[], int length) { */
/*   a[a.length - 1] = 0; */
/*   space = space/2; */
/*   for (; space > 0; space=space/2) { */
/*     int right = space*2 - 1; */
/*     while (right < a.length) { */
/*       int left = right - space; */
/*       int temp = a[right]; */
/*       a[right] = a[left] + a[right]; */
/*       a[left] = temp; */
/*       right = right + space*2; */
/*     } */
/*   } */
/* } */


/* void main (String [] args) { */
/*   int [] a = {3,1,7,0,4,1,6,3}; */
/*   PrefixSumIter p = new PrefixSumIter(a); */
/*   System.out.println(Arrays.toString(a)); */
/*   int space = p.upsweep(); */
/*   System.out.println(space); */
/*   System.out.println(Arrays.toString(a)); */
/*   p.downsweep(space); */
/*   System.out.println(Arrays.toString(a)); */
/* } */


/*
  [3, 1, 7, 0, 4, 1, 6, 3]
  [3, 4, 7, 11, 4, 5, 6, 25]
  [0, 3, 4, 11, 11, 15, 16, 22]



*/
