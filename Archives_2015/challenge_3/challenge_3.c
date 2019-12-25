#include <stdio.h>


struct node{
  int d;
  struct node *p;
  struct node *s;
};

struct node data[10];
struct node** pred[10];
struct node** succ[10];

void init_data (struct node data[],int n){
  int i = 0;
  struct node* pre = NULL;
  struct node* succ = data+(i+1);

  while (i < n-1){
    data[i].d = i;
    data[i].p = pre;
    data[i].s = succ;
    i ++;
    pre = data+(i-1);
    succ = data+(i+1);
  }
    data[i].d = i;
    data[i].p = data+(i-1);
    data[i].s = NULL;
    return;
}

void init_pred (struct node data[], struct node* pre[],int n){
  int i = 0;

  while (i < n){
    pres[i] = &(data[i].p);
    i ++;
  }
  return;
}

void init_succ (struct node data[], struct node** succ[],int n){
  int i = 0;

  while (i < n){
    succ[i] = &(data[i].s);
    i ++;
  }
  return;
}

struct node * remove(struct node** pre[], struct node** succ[], int x){
  *(succ[x])->p = pre[x]
  *(pred[x])->s = succ[x];
  return;
}

void add(struct node** pre[], struct node** succ[], struct node** data[], int x){
  *(succ[x])-> p = data[x];
  *(pred[x]) -> s = data[x];
  return;
}

int main(){

  return 0;
}
