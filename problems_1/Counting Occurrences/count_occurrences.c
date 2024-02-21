#include "count_occurrences.h"

/*@
  assigns \nothing;
  ensures \result == count(a, n, x);
 */
uint occurs(int *a, uint n, int x) {
    uint count = 0;
    /*@ 
      loop invariant 0 <= i <= n;
      loop invariant count == count(a, (uint)i, x);
      loop assigns i, count;
      loop variant n - i;
     */
    for (uint i = 0; i < n; ++i) {
        if (a[i] == x) {
            ++count;
        }
    }
    return count;
}
