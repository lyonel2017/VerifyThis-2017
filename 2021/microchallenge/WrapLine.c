/*@  requires 0 <= from <= to;
  @  requires \valid(s+(0..to-1));
  @  ensures -1 == \result || from <= \result < to;
  @  ensures \result == -1 ==>
  @     (\forall int i; from <= i < to ==> s[i] != c);
  @  ensures from <= \result < to ==>
  @     s[\result] == c &&
  @     (\forall int i; from <= i < \result ==> s[i] != c);
  @  assigns \nothing;
  @*/
static int indexOf(char* s, char c, int from, int to) {
  /*@ loop invariant from <= k <= to;
    @ loop invariant \forall int i; from <= i < k ==> s[i] != c;
    @ loop assigns k;
    @ loop variant to - k;
    @*/
  for(int k = from; k < to; k++) {
    if(s[k] == c) {
      return k;
    }
  }
  return -1;
}

/*@ predicate replace_space_by_new_line{L1,L2}(char* s, int n) =
  @   \forall int i; 0 <= i < n && \at(s[i], L1) != \at(s[i],L2) ==>
  @   \at(s[i], L1) == ' ' && \at(s[i],L2) == '\n';
*/

/*@ predicate at_least_lineLength(char* s, int lineLength, int n) =
  @   \forall int i,j; 0 <= i < j < n && s[i] == '\n' && s[j] == '\n' ==> j-i >= lineLength;
*/

/*@  requires lineLength > 0;
  @  requires 0 < n;
  @  requires \valid(s+(0..n-1));
  @  requires \forall int i; 0 <= i < n ==> s[i] != '\n';
  @  ensures replace_space_by_new_line{Pre,Post}(s,n);
  @  ensures at_least_lineLength(s,lineLength,n);
  @  assigns s[0 .. n -1];
  @*/
void wrapLines_simpl(char* s, int lineLength, int n) {

  int lastBreak = -1;
  int lastSpace = indexOf(s, ' ', 0, n);

  /*@ loop invariant -1 <= lastSpace < n;
    @ loop invariant -1 <= lastBreak < n;
    @ loop invariant lastSpace == -1 || (lastBreak < lastSpace < n && s[lastSpace] == ' ');
    @ loop invariant \forall int i; lastBreak < i < n ==> \at(s[i], LoopEntry) == s[i];
    @ loop invariant replace_space_by_new_line{LoopEntry,Here}(s,n);
    @ loop invariant at_least_lineLength(s,lineLength,n);
    @ loop assigns s[0..n-1],lastBreak,lastSpace;
    @ loop variant lastSpace == -1 ? 0 : n + 1 - lastSpace;
    @*/
  while(lastSpace != -1) {
    if(lastSpace - lastBreak > lineLength) {
      s[lastSpace] = '\n';
      lastBreak = lastSpace;
    }
    lastSpace = indexOf(s, ' ', lastSpace+1, n);
  }
  return;
}

/*@ predicate impossible_to_break(char* s, int length, int n) =
  @   \forall int i; 0 <= i < n - length ==>
  @   (\forall int j; i <= j <= i + length ==> s[j] != '\n') ==>
  @   (\forall int j; i <= j <= i + length ==> s[j] != ' ');
*/

/*@ predicate break_largest{L1,L2}(char* s, int length, int n) =
  @   \forall int a, b, c; 0 <= a < b < c < n &&
  @   (a == -1 || \at(s[a],L2) == '\n') &&
  @   \at(s[b],L2) == '\n' && \at(s[b],L1) == ' ' &&
  @   (\at(s[c],L2) == ' ' || \at(s[c],L2) == '\n') ==>
  @   c - a > length;
*/

/*@  requires 0 < length;
  @  requires 0 < n < 2147483646; // the length of array is limited to MAX_INT -1 because of an overflow
  @  requires \valid(s+(0..n-1));
  @  ensures replace_space_by_new_line{Pre,Post}(s,n);
  @  ensures impossible_to_break(s,length,n);
  @  ensures break_largest{Pre,Post}(s, length, n);
  @  assigns s[0 .. n-1];
  @*/
void wrapLines(char* s, int length, int n) {

  int lastChange = -1;
  int lastSpace = -1;

  /*@ loop invariant -1 <= lastSpace < n;
    @ loop invariant -1 <= lastChange <= lastSpace;
    @ loop invariant lastSpace <= lastChange + length + 1;
    @ loop invariant lastChange == -1 || s[lastChange] == '\n';
    @ loop invariant 0 <= lastSpace  ==> \at(s[\at(lastSpace,Here)],LoopEntry) == ' ' || \at(s[\at(lastSpace,Here)],LoopEntry) == '\n';
    @ loop invariant \forall int x; lastChange < x < n ==> s[x] == \at(s[x],LoopEntry);
    @ loop invariant \forall int x; lastChange < x <= lastSpace ==> s[x] != '\n';
    @ loop invariant replace_space_by_new_line{LoopEntry,Here}(s,n);
    @ loop invariant impossible_to_break(s, length, lastSpace);
    @ loop invariant \forall int a, b, c; 0 <= a < b < c < n &&
        b <= lastChange && (a == -1 || s[a] == '\n') &&
        s[b] == '\n' && \at(s[b],LoopEntry) == ' ' &&
        (s[c] == ' ' || s[c] == '\n') ==> c - a > length;
    @ loop assigns s[0 .. n-1],lastChange, lastSpace;
    @ loop variant 2*n - lastSpace - lastChange;
    @*/
  while(1) {
    int nextSpace = indexOf(s, ' ', lastSpace + 1,n);
    int nextNewLine = indexOf(s, '\n', lastSpace + 1,n);
    if(nextSpace == -1) {
      /*n - lastChange can overflow if the array contain no space and is of size MAX_INT*/
      if(n - lastChange > length &&
	 (nextNewLine - lastChange > length || nextNewLine == -1) &&
	 lastSpace >= 0) {
	s[lastSpace] = '\n';
      }
      return;
    }

    if(0 <= nextNewLine && nextNewLine < nextSpace) {
      if(nextNewLine - lastChange > length && lastSpace >= 0) {
	s[lastSpace] = '\n';
      }
      lastChange = lastSpace = nextNewLine;
    } else {
      if(nextSpace - lastChange > length) {
	if(lastChange == lastSpace) {
	  s[nextSpace] = '\n';
	  lastChange = lastSpace = nextSpace;
	} else {
	  s[lastSpace] = '\n';
	  lastChange = lastSpace;
	}
      } else {
	lastSpace = nextSpace;
      }
    }
  }
  return;
}
