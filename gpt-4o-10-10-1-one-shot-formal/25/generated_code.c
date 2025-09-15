#include <stddef.h>

#include <limits.h>

/*In a given context where a collection of integers is provided, the goal is to identify the smallest integer from that collection.The task requires examining a sequence of integers to determine which one has the lowest value.

  Input
  The input consists of an array of integers, denoted as a, and a size n which represents the number of integers in the array.  The size n must be a positive integer, and the array should be valid and accessible for the specified range.

  Output
  The output is a single integer that represents the minimum value found within the provided array of integers. 
  This value will be one of the integers contained in the input array.
*/

/*@
requires n > 0;
  requires \valid(a + (0 .. n-1));
  decreases n;
  assigns \nothing;
  ensures \forall size_t k; 0 <= k < n ==> \result <= a[k];
  ensures \exists size_t k; 0 <= k < n && a[k] == \result;
*/

int Min(const int *a, size_t n) {
    /* Base case */
    if (n == 1) {
        return a[0];
    }
    /* Recursively find the minimum of the rest of the array */
    int min_rest = Min(a, n-1);
    /* Compare current element with the minimum of the rest */
    return (a[n-1] < min_rest) ? a[n-1] : min_rest;
}
