#include <limits.h>

#include <string.h>

/*The context of this problem is string processing in the C programming language. The focus is on a specific string analysis function named submatcher_0. This function takes a single string as input and checks if every character in the string is 'a'. It does this by recursively checking each character of the string, starting from the first character and moving forward until it encounters a null character.

  The goal of the function submatcher_0 is to determine whether or not the input string consists entirely of 'a' characters. It returns a boolean value, with 1 (true) indicating that the string does consist entirely of 'a' characters and 0 (false) indicating otherwise. 

  Input
  The input to the function is a character string, denoted as x22 in the code. 

  Output
  The output of the function is an integer, which is either 1 (true) if every character in the string is an 'a', or 0 (false) otherwise.
*/

/*@
predicate submatcher_0(char *x) = x[0] == '\0' || (x[0] == 'a' && submatcher_0(x + 1));
*/

/*@
requires ((strlen(x22)>=0) && \valid_read(x22+(0..strlen(x22))));
  decreases strlen(x22);
  assigns \nothing;
  ensures \result <==> submatcher_0(x22);
*/

int submatcher_0(char *x22) {
    if (*x22 == '\0') {
        return 1;
    }
    if (*x22 == 'a') {
        return submatcher_0(x22 + 1);
    }
    return 0;
}
