/* Method findmax() returns the index of the maximum element in array a[] of
   n elements */

typedef unsigned int uint;

/*@
  // is the element a[m] the maximum among indices
    0 to e?
  predicate is_max(int *a, integer e, integer m) =
    \forall integer i; 0 <= i <= e ==> a[i] <= a[m];
 */

/*@
  requires n > 0;
  requires \valid_read(a + (0..n-1));
  assigns \nothing;
  ensures is_max(a, n-1, \result);
 */
uint findmax(int a[], uint n);