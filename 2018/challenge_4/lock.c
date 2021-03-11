// Inspired from https://frama-c.com/download/frama-c-mthread-examples.tgz

// frama-c -mthread -cpp-extra-args="-I$(frama-c -print-share-path)/mt/" -slevel 15 $(frama-c -print-share-path)/mt/mthread_pthread.c $(frama-c -print-share-path)/mt/mthread_queue.c -value-verbose 0 -mt-verbose 3 -mt-shared-values 2 -mt-share $(frama-c -print-share-path)/mt -mt-shared-accesses-synchronization lock.c -mt-write-races

#include "mthread_pthread.h"
#define NULL ((void*)0)
#define N 5

pthread_mutex_t lock;
pthread_t jobs[N];

int pass[N];
int next;

int fetch_and_add(int next, int n)
{
    pthread_mutex_lock(&lock);
    int tmp = next++;
    pthread_mutex_unlock(&lock);
    return tmp;
}

void ablq_init()
{
    for(int i = 1; i < N; i++) {
        pass[i] = 0;
    }
    pass[0] = 1;
    next = 0;
}

int ablq_acquire ()
{
    int my_ticket = fetch_and_add(next, 1) % N;
    while (! pass[my_ticket]);
    return my_ticket;
}

void abql_release(int my_ticket)
{
    pass[my_ticket] = 0;
    pass[(my_ticket + 1) % N] = 1;
}

void * job (void * k)
{
    while(1) {
        int n = ablq_acquire();
        abql_release(n);
    }
}


int main() {
  pthread_mutex_init(&lock, NULL);

  //@ loop pragma UNROLL N;
  for(int i=0;i<N;i++)
    pthread_create( &jobs[i], NULL, &job, NULL );

  return 0;
}
