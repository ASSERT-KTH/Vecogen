

/*	
  In a mathematical context, the task is to compute a specific sequence of numbers known as nonagonal numbers. 
  These numbers are generated based on a formula that involves the input value, which represents the position in the sequence. The goal is to find the value at the given position without performing any modification to the input.

  Input:
  The input is a single integer, n, which represents the index of the nonagonal number to be calculated. 
  The value of n must be within the range of 0 to 783, inclusive.

  Output
  The output is a single integer that represents the n-th nonagonal number calculated according to the specified formula. This output is derived from the input index and follows the mathematical relationship defined for nonagonal numbers.
*/


#include <limits.h>

/*@
  requires n >= 0 && n <= 783;
  assigns \nothing;
  ensures \result == n * (7 * n - 5) / 2;
*/
int NthNonagonalNumber(int n) {
    long long temp = n;
    long long factor = 7LL * temp - 5LL;
    long long product = temp * factor;
    long long result_ll = product / 2LL;
    return (int) result_ll;
}