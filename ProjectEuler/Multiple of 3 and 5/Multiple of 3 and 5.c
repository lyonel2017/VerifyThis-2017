/*
 ============================================================================
 Name        : Multiple.c
 Author      : Lionel Blatter
 Version     : 0.0.1
 Description : Find the sum of all multiples of 3 and 5 below 1000
 ============================================================================
 */

#include <stdio.h>
#include <stdlib.h>

int sum(int x){
	return (x*(x+1))/2;
}

int main(void) {
	int x = 0;
	int lim = 1000 - 1;
	puts("Find the sum of all multiples of 3 and 5 below 1000:");
	x = 3*sum(lim/3)+5*sum(lim/5)-15*sum(lim/15);
	printf("%d \n",x);
	return EXIT_SUCCESS;
}
