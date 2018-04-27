/*
 ============================================================================
 Name        : Even.c
 Author      : Lionel Blatter
 Version     : 0.0.1
 Description : By considering the terms in the Fibonacci sequence less then four million, find the sum of the even-valued term
 ============================================================================
 */

#include <stdio.h>
#include <stdlib.h>

int f(int n){
	int a = 0;
	int b = 1;
	int c = 2;
	int sum = 2;

	while(a < n){
		if ((a % 2) == 0) {sum = sum + a;}
		a = b + c;
		b = c;
		c = a;
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
