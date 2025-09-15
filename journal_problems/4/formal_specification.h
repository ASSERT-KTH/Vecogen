/*@
predicate is_digit(char c) = ('0' <= c <= '9');
*/

/*@
requires \valid(x0 + (0 .. strlen(x0)));
  requires strlen(x0) > 0;
  assigns \nothing;
  ensures is_digit(x0[0]) ==> \result == (x0[0] - '0');
  ensures !is_digit(x0[0]) ==> \result == -1;
*/

