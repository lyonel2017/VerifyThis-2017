#include <stddef.h>
#include <limits.h>

typedef struct list* ref;

struct list {
  int data;
  ref prev;
  ref next;
};

/*@ inductive reachable_prev{L}(ref root, ref to) {
      case prev_empty{L}: \forall ref root; reachable_prev (root, root);
      case prev_non_empty{L}: \forall ref l1, l2;
        \valid(l1) && reachable_prev(l1->prev,l2) ==> reachable_prev (l1, l2);
    }

    inductive reachable_next{L}(ref root, ref to) {
      case next_empty{L}: \forall ref root; reachable_next (root, root);
      case next_non_empty{l}: \forall ref l1, l2;
        \valid(l1) && reachable_next(l1->next,l2) ==> reachable_next (l1, l2);
    }

    predicate reachable{L} (ref root, ref to) =
      reachable_prev (root, to) || reachable_next (root, to);

    predicate linked_list{L} (ref root) =
      reachable_prev (root, NULL) && reachable_next (root, NULL) &&
      (\forall ref l; reachable (root, l) && \valid(l) && \valid(l->next) ==> l->next->prev == l) &&
      (\forall ref l; reachable (root, l) && \valid(l) && \valid(l->prev) ==> l->prev->next == l);

    logic integer lsize{L} (ref head) =
      (head == NULL) ? 0 : 1 + lsize (head->next);

    lemma lsize_pos : \forall ref root; reachable_next(root, NULL) ==> 0 <= lsize (root);
*/

/*@ requires linked_list (head);
    requires lsize(head) <= INT_MAX;
    terminates \true;
    assigns \nothing;
*/
int size (ref head) {
  int count;

  count=0;
  /*@ loop invariant linked_list(head);
      loop invariant count + lsize(head) == \at(lsize(head), LoopEntry);
      loop assigns count, head;
      loop variant lsize(head);
  */
  while (head != NULL) {
    count++;
    head = head->next;
  }

  return count;
}

/*@ requires \valid(head);
*/
void dll_to_bst_rec (ref head, int n, ref* root, ref* right) {
  if (n > 0) {
    ref* left;
    dll_to_bst_rec (head, n/2, left, root);
    (*root)->prev = *left;
    // unlike the question, we reuse [left] instead of introducing [temp]
    dll_to_bst_rec ((*root)->next, n-n/2-1, left, right);
    (*root)->next = *left;
  } else {
    *root = NULL;
    *right = head;
  }
}

ref dll_to_bst (ref head) {
  int n;
  ref root, right;
  n = size (head);
  dll_to_bst_rec (head, n, &root, &right);

  return root;
}
