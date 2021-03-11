/*@ axiomatic gcd_axio{
  logic int GCD (int x, int y);
}*/

/*@ requires x > 0 && y > 0;
  @ ensures \result > 0;
  @ ensures \result == GCD(x,y);*/
int gcd(int x, int y){
  int a = x;
  int b = y;
  /*@ loop assigns a,b;
    @ loop invariant a > 0;
    @ loop invariant b > 0;
    @ loop invariant GCD(a,b) == GCD(x,y);
    @ loop variant a*b;
*/
  while(a != b){
    if(a > b){
      a = a - b;
    }
    else{
      b = b - a;
    }
  }
  return a;
}
