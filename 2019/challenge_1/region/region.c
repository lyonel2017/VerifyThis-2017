//@ ghost int ALLOC = 3 ;
/*@ axiomatic test{

  // Necessary pre-condition for any allocating function.
  predicate Allocating{L} = 3 <= \at( ALLOC , L ) ;

  logic integer WPREGION(int *addr) reads addr ;
  logic int* WPALLOC(integer k) reads k;

  // The k-th allocated address since FROM.
  logic int *Alloc{FROM}(integer k) = WPALLOC(\at(ALLOC+k,FROM));

  // Designate the k-th allocated address since FROM.
  predicate Allocated{FROM}(int *addr,integer k) =  (WPREGION(addr) == \at(ALLOC+k,FROM)) && (addr == WPALLOC(\at(ALLOC+k,FROM))) ;

  // Number of allocated pointers between PRE and POST.
  predicate Allocates{PRE,POST}(integer n) = \at( ALLOC , POST ) ==  \at( ALLOC , PRE ) + n ;

  }*/

/*@ requires 0 < len;
    requires Allocating ;
    ensures \valid(\result+(0 .. len-1));
    ensures \forall integer j; (0 <= j < len ==> \result[j] == 0);
    ensures Allocates{Pre,Post}(1);
    ensures Allocated{Pre}(\result,1);
    assigns ALLOC ;
 */
int* arr_init(int len); //{ return (int*)calloc(len, sizeof(int)); }


/*@ requires Allocating ;
    requires 0 < len;
    requires \valid(in_arr+(0 .. len-1));
    ensures \valid(\result+(0 .. len-1));
    ensures \forall integer j;  (0 <= j < len ==> \result[j] == in_arr[j]);
    ensures Allocates{Pre,Post}(1);
    ensures Allocated{Pre}(\result,1);
    assigns Alloc{Pre}(1)[0..len-1];
    assigns ALLOC ;
 */
int* arr_copy1(int len, int* in_arr){
  int i = 0;
  int * out_arr = arr_init(len);
  //@ assert \separated(in_arr+(0 .. len-1), out_arr+(0 .. len-1));

  /*@ loop invariant 0 <= i <= len;
      loop invariant \forall integer j; ((0 <= j < i) ==> out_arr[j] == in_arr[j]);
      loop assigns out_arr[0 .. len-1], i;
      loop variant (len-i);
  */
  while(i < len){
    out_arr[i] = in_arr[i];
    i = i + 1;
  }
  return out_arr;
}
