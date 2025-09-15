#include <stddef.h>

#include <limits.h>

/*This problem involves calculating the sum of a sequence of integers stored in an array. The goal is to find the total sum of the elements from the beginning of the array up to a specified number of elements.

  Input
  The input consists of two components: a pointer to an array of integers and an integer representing the number of elements to be summed. The integer can be any non-negative value, and the array is guaranteed to contain at least as many elements as the specified integer.

  Output
  The output is the total sum of the specified number of elements in the array. The sum is calculated in such a way that it does not exceed a certain maximum value defined by the data type limits.
*/

/*@
logic integer SumTo{L}(int *a, integer n) = 
    (n <= 0) ? 0 : SumTo{L}(a, n - 1) + a[n - 1];
*/

/*@
requires a != \null;
  requires n >= 0;
  requires \valid_read(a + (0 .. n-1));
  requires \forall integer i; 0 <= i < n ==> 0 <= a[i] <= INT_MAX;
  requires SumTo(a, n) <= LLONG_MAX;
  decreases n;
  assigns \nothing;
  ensures \result == SumTo(a, n);
*/

long long sumTo(int *a, int n) {
    if (n == 0)
        return 0;
    return sumTo(a, n - 1) + a[n - 1];
}
