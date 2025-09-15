#include <stdlib.h>

#include <stddef.h>

/*In a context where character manipulation is necessary, the goal is to transform 
  a given character by shifting its ASCII value. The task involves taking a character 
  input and adjusting its value in a specific manner.

  Input
  A single character variable 'c' which is expected to be in the range of 
  0 to 127, representing valid ASCII values.

  Output
  The output is a character value that remains within the ASCII range of 
  0 to 127. It should be the result of subtracting 32 from the input character's 
  ASCII value.
*/

/*@
requires 0 <= c <= 127;
  assigns \nothing;
  ensures 0 <= \result <= 127;
  ensures \result == (((c + 32) + 128) % 128);
*/

char shift_plus32(char c) {
    return (char)(((c + 32) % 128 + 128) % 128);
}
