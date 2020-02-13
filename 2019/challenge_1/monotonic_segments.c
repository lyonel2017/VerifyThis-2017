#include <stdio.h>

#define size 100

struct sequence {
  unsigned int n;
  unsigned int t [size];
};

typedef struct sequence seq;

/*@ requires s.n < size;
  @ ensures \result.n == s.n + 1;
  @ ensures \forall integer i; 0 <= i < s.n ==>  \result.t[i] == s.t[i];
  @ ensures \result.t[s.n] == x;
  @ assigns \nothing;
*/
seq add (seq s, unsigned int x){
  seq s_tmp = s;
  s_tmp.t[s_tmp.n] = x;
  s_tmp.n++;
  return s_tmp;
}

/*@ predicate non_empty(seq s) = s.n > 0;*/
/*@ predicate begin_to_end(seq s, integer n) = s.t[0] == 0 && s.t[s.n-1] == n;*/
/*@ predicate within_bounds(seq s, integer n) = \forall integer k; 0 <= k < s.n ==> 0 <= s.t[k] <= n;*/

/*@ predicate monotic_sub_l(seq s, integer k1, integer k2) = \forall integer i,j; k1 <= i < j < k2 ==> s.t[i] < s.t[j];*/
/*@ predicate monotic_sub_r(seq s, integer k1, integer k2) = \forall integer i,j; k1 <= i < j < k2 ==> s.t[i] >= s.t[j];*/
/*@ predicate monotonic(seq s_c, seq s) = \forall integer k; 0 <= k < s_c.n-1 ==> (monotic_sub_l(s, s_c.t[k], s_c.t[k+1]) || monotic_sub_r(s, s_c.t[k], s_c.t[k+1]));*/

/*@ requires s.n < size;
  @ ensures non_empty(\result);
  @ ensures begin_to_end(\result,s.n);
  @ ensures within_bounds(\result, s.n);
  @ ensures monotonic(\result, s);
*/
seq monotonic_sequence (seq s){
  seq s_tmp;
  s_tmp.n = 0;
  s_tmp = add (s_tmp,0);
  unsigned int x = 0;
  unsigned int y = 1;
  unsigned int i = 0;
  /*@ loop invariant 1 <= y <= s.n+1;
      loop invariant x == y-1;
      loop invariant non_empty(s_tmp);
      loop invariant begin_to_end(s_tmp, x);
      loop invariant within_bounds(s_tmp, s.n);
      loop invariant monotonic(s_tmp, s);
      loop assigns y,x,s_tmp,i;
      loop variant s.n -y;*/
  while(y < s.n){
  l1:i = s.t[x] < s.t[y];
    /*@ loop invariant 1 <= y <= s.n;
        loop invariant y > x;
        loop invariant monotic_sub_l(s, x, y) || monotic_sub_r(s, x, y);
        loop assigns y;
        loop variant s.n -y;*/
    while (y < s.n && ((s.t[y-1] < s.t[y]) == i)){
      y++;
    }
    s_tmp = add(s_tmp,y);
    x = y;
    y = x + 1;
  }
  if(x < s.n) s_tmp = add(s_tmp,s.n);
  return s_tmp;
}

/*--------------------------------------------------------------------------*/

void add_q (seq* s, unsigned int x){
  s->t[s->n] = x;
  s->n++;
  return;
}

void swap(int *x, int *y){
  int t = *x;
  *x=*y;
  *y=t;
}

void revert (seq* s, unsigned int x, unsigned int y){
  unsigned int i = 0;
  for(i = 0; i <= (y-x/2) ; i--) swap(s->t+(x+i),s->t+(y-i-1));
}

void revert_decr(seq* s, seq seg){
  unsigned int i = 0;
  for(i = 0; i < seg.n-1; i++){
    if(s->t[seg.t[i]] >= s->t[seg.t[i]+1]) revert(s,seg.t[i],seg.t[i+1]);
  }
  return;
}

void print_seq(seq s){
  int i = 0;
  for(i = 0; i < s.n; i++){
    printf("%d ", (int) s.t[i]);
  }
  printf("\n");
}

seq merge(seq s, seq seg){
  seq s_tmp_1;
  s_tmp_1.n = 0;

  seq s_tmp_2;
  s_tmp_2.n = 0;

  unsigned int i = 0;
  unsigned int x = 0;
  unsigned int y = 0;
  unsigned int temp = 0;

  for(i = 0; i < seg.n-1; i++){
    while(x < s_tmp_1.n && y < seg.t[i+1] - seg.t[i] + temp){
      if (s_tmp_1.t[x] < s.t[y]){
        add_q(&s_tmp_2,s_tmp_1.t[x]);
        x = x + 1;
      }
      else{
        add_q(&s_tmp_2,s.t[y]);
        y = y + 1;
      }
    }
    while(x < s_tmp_1.n){
      add_q(&s_tmp_2,s_tmp_1.t[x]);
      x = x + 1;
    }
    while(y < seg.t[i+1] - seg.t[i] + temp){
      add_q(&s_tmp_2,s.t[y]);
      y = y + 1;
    }
    print_seq(s_tmp_2);
    s_tmp_1 = s_tmp_2;
    s_tmp_2.n=0;
    x = 0;
    temp = y;
  }
  return s_tmp_1;
}


int main (){
  seq s = {.n =7,.t={6,3,4,2,5,3,7}};
  print_seq(s);
  seq s_tmp = monotonic_sequence(s);
  revert_decr(&s,s_tmp);
  print_seq(merge(s, s_tmp));
  return 0;
}
