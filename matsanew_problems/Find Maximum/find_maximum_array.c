#include "find_maximum.h"

uint findmax(int a[], uint n) {
    //@ assert n > 0;
    //@ assert \valid_read(a + (0..n-1));

    // Initialize max_index to the first element
    uint max_index = 0;

    // Assert that the initial max_index is valid
    //@ assert 0 <= max_index < n;

    /*@
      loop invariant 1 <= i <= n;
      loop invariant max_index < i;
      loop invariant \forall integer j; 0 <= j < i ==> a[j] <= a[max_index];
      loop assigns i, max_index;
      loop variant n - i;
     */
    for (uint i = 1; i < n; i++) {
        if (a[i] > a[max_index]) {
            max_index = i;
        }
    }

    // Assert that the final max_index is valid
    //@ assert 0 <= max_index < n;

    // Assert the post-condition
    //@ assert is_max(a, n - 1, max_index);

    return max_index;
}
