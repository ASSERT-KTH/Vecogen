#include <stdlib.h>

#include <stddef.h>

/*In a computing context, there is a need to transform character values while ensuring they remain within a specific range. The goal is to create a function that shifts a given character value down by 32, while also ensuring that the result is wrapped around to stay within the limits of acceptable character values.

  Input
  The input is a single character value represented as a signed 8-bit integer, referred to as 'c'. 
  The valid range for 'c' is from 0 to 127, inclusive.

  Output
  The output is a character value, also represented as a signed 8-bit integer. 
  The output will always lie within the range of 0 to 127, inclusive, and will be the result of
  the transformation applied to the input character.
*/

/*@
requires 0 <= c <= 127;
  assigns \nothing;
  ensures 0 <= \result <= 127;
  ensures \result == (((c - 32) + 128) % 128);
*/

char shift_minus32(char c) {
    return (char)((c - 32 + 128) % 128);
}
