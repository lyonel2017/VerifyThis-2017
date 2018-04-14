#include <stdio.h>
#include <stdbool.h>

bool pass[2];
int next = 0;

int data = 0;

/*@ ensures \forall int x; 1 <= x < 2 ==> pass[x] == \false;
  @ ensures pass[0] == \true;
  @ assigns pass[0..2] next;*/
void abql_int(){
  /*@ loop invariant \forall int x; 0 <= x < i ==> pass[x] == \false;
    @ loop invariant n - i;*/
  for(int i = 1; i < n; i++){
    pass[i] = false
  }
  pass[0] = true;
  next = 0;
  return;
}

/*@ ensures \result == \old(next);
  @ ensures next = \old(next) + 1;
  @ assigns next;*/
int fetch_and_add(){
  int tmp = next;
  next = next + 1;
  return tmp;
}

/*@ relational \callset(\call{l1,l2}(abql_int),\call{l3,l4}(abql_acquire),\call{l5,l6}(abql_acquire)) ==>
    (forall int i;  0 <= i < 2 ==> \at(pass[i],l2) == \at(pass[i],l3) && \at(pass[i],l4) == \at(pass[i],l5) ==>
    (exists int x; \callresult(l6) == x) ==> \false;
  @ relational \callset(\call{l1,l2}(abql_int),\call{l3,l4}(abql_acquire),\call{l5,l6}(abql_release,\callresult(l4)),\call{l7,l8}(abql_acquire)) ==>
    (forall int i;  0 <= i < 2 ==> \at(pass[i],l2) == \at(pass[i],l3) && \at(pass[i],l4) == \at(pass[i],l5) ==>
    \callresult(l4) == \callresult(l8) + 1;*/
int abql_acquire(){
  int ticket = fetch_and_add() % N;
  /*@ loop !(pass[ticket]);*/
  while (!(pass[ticket]));
  return ticket;
}

void abql_release(int ticket){
  pass[ticket] = false;
  pass[(my_ticket +1) % N] = true;
  return;
}

void thread(){
  int lock = abql_acquire();
  data = data + 1;
  abql_release(lock);
}
