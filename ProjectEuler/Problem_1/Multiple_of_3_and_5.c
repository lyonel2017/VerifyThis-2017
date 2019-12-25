/*
 ============================================================================
 Name        : Multiple.c
 Version     : 0.0.1
 Description : Find the sum of all multiples of 3 and 5 below 1000
 ============================================================================
 */

#include <stdio.h>
#include <stdlib.h>

/*@ axiomatic Sum {
     logic integer sum(integer i, integer j);

     axiom sum1:
       \forall integer i, j; i >= j ==> sum(i,j) == 0;
     axiom sum2:
       \forall integer i, j; i <= j ==>
         sum(i,j+1) == sum(i,j) + j;
     lemma sum3:
       \forall integer i, j, k;
         0 <= i <= j <= k ==>
           sum(i,k) == sum(i,j) + sum(j,k);
}*/

/*@ requires n >= 1;
  @ assigns \nothing;
  @ ensures sum(0,n) == ((n-1)*(n))/2;
*/
void sum_lemma(int n) {
  int i,s = 0;
  /*@ loop invariant 0 <= i <= n;
    @ loop invariant s == sum(0,i);
    @ loop invariant s == ((i-1)*(i))/2;
    @ loop assigns s,i;
    @ loop variant n-i;
  */
  for(i=0; i < n; i++){
    s = s + i;
  }
  return;
}

/*@ axiomatic Sum_Mult {
  logic integer sum_mult(integer i, integer j,integer x);
     axiom sum_mult1:
       \forall integer i, j,x; i >= j ==> sum_mult(i,j,x) == 0;
     axiom sum_mult2:
       \forall integer i, j,x; i <= j ==> j%x == 0 ==>
         sum_mult(i,j+1,x) == sum_mult(i,j,x) + j;
     axiom sum_mult3:
       \forall integer i, j,x; i <= j ==> j%x != 0 ==>
         sum_mult(i,j+1,x) == sum_mult(i,j,x);
}*/

/*@ requires n >= 1;
  @ assigns \nothing;
*/
void sum_mumt_lemma(int n, int x) {
  int i,s = 0;
  /*@ loop invariant 0 <= i <= n;
    @ loop invariant s == sum_mult(0,i,x);
    @ loop invariant s == x * sum(0,i/x);
    @ loop assigns s,i;
    @ loop variant n-i;
  */
  for(i=0; i < n; i++){
    if(i%x){}
    else {
      s = s + i;
    }
  }
  return;
}


/*@ requires x >= 1;
  @ assigns \nothing;
  @ ensures sum(0,x+1) == \result;*/
int sum(int x){
  return (x*(x+1))/2;
}

/*@ requires lim >= 1;
  @ assigns \nothing;*/
int f(int lim){
  return 3*sum(lim/3)+5*sum(lim/5)-15*sum(lim/15);
}

int main(void) {
  int x = 0;
  int lim = 1000 - 1;
  puts("Find the sum of all multiples of 3 and 5 below 1000:");
  x = f(lim);
  printf("%d \n",x);
  return EXIT_SUCCESS;
}



/* axiomatic Sum_Mult_3_5 {
  logic integer sum_mult_3_5(integer n);

  axiom Sumzero:
  sum_mult_3_5(0) == 0;

  axiom SumMultLe: \forall integer n;
  (n%3 == 0 || n%5 == 0) ==>
  sum_mult_3_5(n) == sum_mult_3_5(n-1) + n;

  axiom SumMultGt: \forall integer n;
  (n%3 != 0 && n%5 != 0) ==>
  sum_mult_3_5(n) == sum_mult_3_5(n-1);
}*/
