#include <limits.h>

/*In a mathematical context, the task is to compute a specific value known as the N-th hexagonal number.
  This number is derived from a formula that involves the position of the number in the sequence (n).
  The goal is to calculate this value efficiently while ensuring that the computation remains within the bounds of standard integer values.

  Input:
      An integer n representing the position in the hexagonal number sequence, where n is a non-negative integer.

  Output:
      The N-th hexagonal number.
*/

/*@
requires n >= 0;
  // Ensure that the computation does not overflow the int range.
  // (2LL * n - 1LL) is computed in long long arithmetic.
  requires (long long)n * (2LL * n - 1LL) <= INT_MAX;
  
  assigns \nothing;
  
  ensures \result == n * (2 * n - 1);
*/

int NthHexagonalNumber(int n) {
    return n * (2 * n - 1);
}
