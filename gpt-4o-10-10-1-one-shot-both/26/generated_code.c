#include <stddef.h>

#include <limits.h>

/*In a scenario where a series of integers is provided, the goal is to identify the largest integer within that series. The task is to process an array of integers and determine the maximum value it contains.

  Input
  The input consists of an array of integers, denoted as a, along with a size indicator n. The size n must be a positive integer, ensuring that there is at least one element in the array. The elements of the array can be any integer values.

  Output
  The output is a single integer representing the maximum value found within the provided array of integers. This value is guaranteed to be one of the elements in the array.
*/

/*@
requires n > 0;
  requires \valid(a + (0 .. n-1));
  decreases n;
  assigns \nothing;
  ensures \forall size_t k; 0 <= k < n ==> \result >= a[k];
  ensures \exists size_t k; 0 <= k < n && a[k] == \result;
*/

int Max(const int *a, size_t n) {
    /* Base case */
    if (n == 1) {
        return a[0];
    }
    
    /* Recursive call */
    int max_of_rest = Max(a, n - 1);
    
    /* Return the maximum between the last element and the max of the rest */
    return (a[n - 1] > max_of_rest) ? a[n - 1] : max_of_rest;
}
