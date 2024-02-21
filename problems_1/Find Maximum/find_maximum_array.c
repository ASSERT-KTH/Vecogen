#include <stddef.h>

typedef unsigned int uint;

/*@
  // is the element a[m] the maximum among indices 0 to e?
  predicate is_max(int *a, integer e, integer m) =
    \forall integer i; 0 <= i <= e ==> a[i] <= a[m];
 */

/*@
  requires n > 0;
  requires \valid_read(a + (0..n-1));
  assigns \nothing;
  ensures is_max(a, n-1, \result);
 */
uint findmax(int a[], uint n)
{
    uint max_index = 0;

    /*@
      loop invariant 0 <= max_index < n;
      loop invariant 1 <= i <= n;
      loop invariant is_max(a, i-1, max_index);
      loop assigns i, max_index;
      loop variant n - i;
     */
    for (uint i = 1; i < n; i++)
    {
        if (a[i] > a[max_index])
        {
            max_index = i;
        }
    }

    return max_index;
}
