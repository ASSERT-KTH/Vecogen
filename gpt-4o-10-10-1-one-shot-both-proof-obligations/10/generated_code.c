#include <limits.h>

#include <stdint.h>

/*Octagonal numbers are a specific sequence of numbers that can be represented geometrically as octagons. The goal is to determine the nth octagonal number based on a given integer input. 

  Input
  The input consists of a single integer variable, n, which represents the position in the sequence of octagonal numbers. It is constrained such that n is between 0 and 10,000, inclusive.

  Output
  The output is a single integer value, which is the nth octagonal number calculated.
*/

/*@
requires 0 <= n <= 10000;
  // This function computes the nth octagonal number: n*(3*n -2)
  assigns \nothing;
  ensures \result == n * (3 * n - 2);
*/

int NthOctagonalNumber(int n) {
    return n * (3 * n - 2);
}
