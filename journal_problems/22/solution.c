/*
  In a scenario where you have a collection of boolean values, the goal is to determine how many of these values are true. 

  Input
  The input consists of a pointer to an array of boolean values and an integer representing the number of elements in the array. The integer must be non-negative, and the array must have at least as many elements as specified by this integer.

  Output
  The output is an integer that indicates the total count of true values in the provided array. This count will range from 0 to the total number of elements specified in the input.
*/

#include <stddef.h>
#include <stdbool.h>

/*@
  logic integer SumTrue(bool *a, int n) =
    (n == 0 ? 0
             : SumTrue(a, (int)(n - 1)) + (a[n - 1] ? 1 : 0));
*/

/*@
  requires \valid(a + (0 .. n-1));
  requires 0 <= n;
  decreases n;
  assigns \nothing;
  ensures \result == SumTrue(a, n);
  ensures n == 0 ==> \result == 0;
  ensures n > 0 ==> \result == SumTrue(a, (int)(n - 1)) + (a[n - 1] ? 1 : 0);
  ensures \result  <= n;
*/
int countTo(bool *a, int n) {
  if (n == 0) {
    return 0;
  } else {
    int tmp = countTo(a, n - 1);
    if (a[n - 1]) {
      tmp = tmp + 1;
    }
    return tmp;
  }
}