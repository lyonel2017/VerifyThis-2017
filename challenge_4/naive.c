/* This is an implementation of the naive version in C with ACSL annotations. */

#include <stdlib.h>

struct buff {
  int h;
  int n;
  int tab [1000];
};
/* type invariant valid_buffer(struct buff b) =
    b.h > 0 && 0 <= b.n < 1000;  
*/

/*@ predicate valid_empty_buff(integer h, struct buff b) =
  @     b.h == h && b.n == 0 && (\forall integer k; 0 <= k < 1000 ==> b.tab[k] == 0);
*/

/*@ requires 0 <= h < 1000;
  @ assigns \nothing;
  @ ensures valid_empty_buff(h,\result);*/
struct buff empty (int h){
    struct buff temp;
    temp.h = h;
    temp.n = 0;
    /*@ loop assigns i, temp.tab[0..1000];
      @ loop invariant 0 <= i <= 1000;
      @ loop invariant \forall integer k; 0 <= k < i ==> temp.tab[k] == 0;
     */
    for(int i = 0; i < 1000; i++){
      temp.tab[i] = 0;
    }
    return temp;
}


/*@ requires 0 <= b.n < 1000 && 0 <= b.h < 1000;
  @ behavior full_buffer:
     assumes b.n + 1 >= 1000;
     assigns \nothing;
  @ behavior good:
     assumes b.n < 1000;
     assigns \result \from b,a;
     ensures \forall integer k; 0 <= k <= \at(b.n,Pre) ==> \result.tab[k] == \at(b.tab[k],Pre);
     ensures \result.tab[\at(b.n,Pre) + 1] == a;
 */
struct buff add (struct buff b, int a){
  if ( b.n + 1 < 1000){
    b.n = b.n + 1;
    b.tab[b.n] = a;
  }
  else {
    exit(1);
  }
  return b;
}

/*@ requires \valid(t+(0..b.h));
  @ requires b.h > 0;
  @ requires b.n > 0;
  @ requires b.n < 1000 && b.h < 1000;
  @ assigns t[0..b.h];
  @ ensures \forall integer k; b.n <= b.h ==> 0 <= k <= b.n ==> t[k] == \at(b.tab[b.n - k],Pre);
  @ ensures \forall integer k; b.h <= b.n ==> 0 <= k <= b.h ==> t[k] == \at(b.tab[b.n - k],Pre);
*/
void get (int t[], struct buff b){
  int j = 0;
  /*@ loop assigns t[0..b.h],j;
    @ loop invariant \forall integer k; 0 <= k < j ==> t[k] == \at(b.tab[b.n - k],Pre);
    @ loop invariant 0 <= j;
    @ loop invariant j <= b.n + 1 && j <= b.h + 1;
    @ loop variant b.n-j;
   */
  while(b.n-j >= 0 && b.h-j >= 0){
    t[j] = b.tab[b.n - j];
    j ++;
  }
 }

struct caterpillar {
  int h;
  int xs_n;
  int xs [1000];
  int ys_n;
  int ys [1000];
};

/*@ predicate valid_empty_caterpillar(integer h, struct caterpillar b) =
  @     b.h == h && b.xs_n == 0 && b.ys_n == 0
  @     && (\forall integer k; 0 <= k < 1000 ==> b.xs[k] == 0) 
  @     && (\forall integer k; 0 <= k < 1000 ==> b.ys[k] == 0);
*/

/*@ requires 0 <= h < 1000;
  @ assigns \nothing; 
  @ ensures valid_empty_caterpillar(h,\result);*/
struct caterpillar empty_caterpillar (int h){
    struct caterpillar temp;
    temp.h = h;
    temp.xs_n = 0;
    temp.ys_n = 0;
    /*@ loop assigns i, temp.xs[0..1000];
      @ loop invariant 0 <= i <= 1000;
      @ loop invariant \forall integer k; 0 <= k < i ==> temp.xs[k] == 0;
     */
    for(int i = 0; i < 1000; i++){
      temp.xs[i] = 0;
    }
    /*@ loop assigns i, temp.ys[0..1000];
      @ loop invariant 0 <= i <= 1000;
      @ loop invariant \forall integer k; 0 <= k < i ==> temp.ys[k] == 0;
     */
    for(int i = 0; i < 1000; i++){
      temp.ys[i] = 0;
    }
    return temp;
}

/*@ requires 0 <= b.xs_n < 1000 && 0 <= b.ys_n < 1000 && 0 <= b.h < 1000;
  @ behavior full_buffer:
     assumes b.xs_n >= b.h - 1;
     assigns \result \from b,a;
     ensures \forall integer k; 0 <= k <= \at(b.h,Pre) ==> \result.ys[k] == \at(b.xs[k],Pre);
     ensures \forall integer k; 0 <= k <= \at(b.h,Pre) ==> \result.xs[k] == 0;
  @ behavior good:
     assumes b.xs_n < b.h - 1;
     assigns \result \from b,a;
     ensures \forall integer k; 0 <= k <= \at(b.ys_n,Pre) ==> \result.ys[k] == \at(b.ys[k],Pre);
     ensures \forall integer k; 0 <= k <= \at(b.xs_n,Pre) ==> \result.xs[k] == \at(b.xs[k],Pre);
     ensures \result.xs[\at(b.xs_n,Pre) + 1] == a; 
 */
struct caterpillar add_caterpillar (struct caterpillar b, int a){
  if(b.xs_n >= b.h - 1){
    /*@ loop assigns i, b.ys[0..b.h];
      @ loop invariant 0 <= i <= b.h + 1;
      @ loop invariant \forall integer k; 0 <= k < i ==> b.ys[k] == b.xs[k];
     */
    for(int i = 0; i <= b.h; i++){
      b.ys[i] = b.xs[i];
    }
    /*@ loop assigns i, b.xs[0..b.h];
      @ loop invariant 0 <= i <= b.h + 1;
      @ loop invariant \forall integer k; 0 <= k < i ==> b.ys[k] == \at(b.ys[k],LoopEntry);
      @ loop invariant \forall integer k; 0 <= k < i ==> b.xs[k] == 0;
     */
    for(int i = 0; i <= b.h; i++){
      b.xs[i] = 0;
    }
    b.ys_n = b.xs_n;
    b.xs_n = 0;
  }
  else {
    b.xs_n = b.xs_n + 1;
    b.xs[b.xs_n] = a;
  }
  return b;
}

/*@ requires \valid(t+(0..b.h));
  @ requires b.h > 0;
  @ requires b.xs_n > 0;
  @ requires b.ys_n > 0;
  @ requires b.xs_n < 1000 && b.ys_n && b.h < 1000;
  @ assigns t[0..b.h];
  //@ ensures \forall integer k; 0 <= k <= b.xs_n ==> t[k] == \at(b.xs[b.xs_n - k],Pre);
  //@ ensures \forall integer k; ys <= b.h ==> 0 <= k <= b.xs_n ==> t[k] == \at(b.xs[b.xs_n - k],Pre);
*/
void get_caterpillar (int t[], struct caterpillar b){
  int j = 0;
  /*@ loop assigns t[0..b.h],j;
    @ loop invariant \forall integer k; 0 <= k < j ==> t[k] == \at(b.xs[b.xs_n - k],Pre);
    @ loop invariant 0 <= j;
    @ loop invariant j <= b.xs_n + 1 && j <= b.h + 1;
    @ loop variant b.xs_n-j;
   */
  while(b.xs_n-j >= 0 && b.h-j >= 0){
    t[j] = b.xs[b.xs_n - j];
    j ++;
  }

  int i = 0;
  /*@ loop assigns t[0..b.h],i;
    @ loop invariant \forall integer k; 0 <= k < i ==> t[j+k] == \at(b.ys[b.ys_n - k],Pre);
    @ loop invariant 0 <= i;
    @ loop invariant j == \at(j,LoopEntry);
    @ loop invariant i <= b.ys_n+1 && i <= b.h + 1 - j;
    @ loop variant b.ys_n-i;
   */
  while(b.ys_n-i >= 0 && b.h-j-i >= 0){
    t[j+i] = b.ys[b.ys_n - i];
    i ++;
  }
 }
