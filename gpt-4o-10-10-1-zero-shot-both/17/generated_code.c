#include <limits.h>

/*The goal is to perform multiplication of two integers while ensuring that the result remains within the valid range of integer values.

  Input:
      - Two integers, a and b.
      - Each integer can take any value within the range of a standard 32-bit signed integer

  Output:
      - The product of the two integers, which is also an integer.
      - The output will be valid as long as the product does not exceed the limits of a 32-bit signed integer.
*/

/*@
requires (long long)a * (long long)b >= INT_MIN && (long long)a * (long long)b <= INT_MAX;
  assigns \nothing;
  ensures \result == a * b;
@
*/

int Multiply(int a, int b) {
    // Since the requires clause in the ACSL specification guarantees that the
    // product of a and b will not overflow or underflow, we can safely perform
    // the multiplication directly.
    return a * b;
}
