/*
 ============================================================================
 Name        : Even.c
 Version     : 0.0.1
 Description : By considering the terms in the Fibonacci sequence less then four million, find the sum of the even-valued term
 ============================================================================
 */

#include <stdio.h>
#include <stdlib.h>

/*@ axiomatic fib{
  logic integer fib(integer x);

  axiom fib0: fib(0) == 0;
  axiom fib1: fib(1) == 1;
  axiom fibn: \forall integer n; n >= 2 ==> fib(n) == fib (n-1) + fib (n-2);
}*/

/*@ axiomatic Sum_Event_fib {
  logic integer sum_even_fib(integer m,integer n);

  axiom Sumzero:
  \forall integer m; sum_even_fib(m,0) == 0;

  axiom SumEvenLe: \forall integer m,n;
  n >= 0 ==> fib(n) < m ==> fib(n)%2 == 0 ==>
  sum_even_fib(m,n) == sum_even_fib(m,n-1) + fib(n);

  axiom SumEvenGt: \forall integer n,m;
  n >= 0 ==> fib(n) >= m ==> fib(n)%2 == 0 ==>
  sum_even_fib(m,n) == sum_even_fib(m,n-1);

  axiom SumOdd: \forall integer n,m;
  n >= 0 ==> fib(n)%2 != 0 ==>
  sum_even_fib(m,n) == sum_even_fib(m,n-1);
}*/


/*@ requires n >= 0;
  @ assigns \nothing;
  @ ensures \exists integer k; \result == sum_even_fib(n,k) && fib(k+1) >= n;*/
int f(int n){
  int sum = 0;
  int b = 0;
  int c = 1;
  int a = c + b;
  /*@ ghost int p = 2;*/

  /*@ loop invariant fib(p-2) == b;
    @ loop invariant fib(p-1) == c;
    @ loop invariant fib(p) == a;
    @ loop invariant 2 <= p;
    @ loop invariant sum == sum_even_fib(n,p-1);
    @ loop assigns a,b,c,sum,p;
  */
  while(a < n){
    if ((a % 2) == 0) {sum = sum + a;}
    b = c;
    c = a;
    a = c + b;
    /*@ ghost p = p + 1;*/
  }
  return sum;
}

int main(void) {
	int x = 0;
	puts("Result:");
	x = f(4000000);
	printf("%d \n",x);
	return EXIT_SUCCESS;
}
