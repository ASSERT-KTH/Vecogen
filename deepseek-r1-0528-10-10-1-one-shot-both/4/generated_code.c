#include <string.h>

/*This function named `p` takes a string as input. It specifically deals with the first character of the string and checks whether this character is a digit or not. If it is a digit, the function will convert that digit from a character type to an integer type and return the integer value. If the first character of the string is not a digit, the function will return -1.

  Input
  The input to the function `p` is a string, denoted as `x0`. 

  Output
  The output of the function `p` is an integer. If the first character of the input string `x0` is a digit, the function will convert that digit from a character type to an integer type and return the integer value. If the first character of the string is not a digit, the function will return -1.
*/

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

int p(char *x0) {
    if (x0[0] >= '0' && x0[0] <= '9')
        return x0[0] - '0';
    else
        return -1;
}
