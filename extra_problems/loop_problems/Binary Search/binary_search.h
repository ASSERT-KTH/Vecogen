
/* Method binary_search() performs a binary-search for element x in array a[]
   of n elements. If a match is found, the corresponding index is returned;
   otherwise -1 is returned. */

/*@
  // Does array a[] contain x between its indices s and e?
  predicate contains(int *a, integer s, integer e, int x) =
    \exists integer i; s <= i <= e && a[i] == x;
 */

/*@
  requires \valid_read(a + (0..n-1));
  requires n > 0;

  // To specify the sorted order, if we instead use the predicate
  // (\forall int i; 0 <= i <= n-2 ==> a[i] <= a[i+1]), the provers
  // like cvc4 and alt-ergo are not able to prove this method.
  requires \forall int i, j; 0 <= i < j <= n-1 ==> a[i] <= a[j];

  ensures contains(a, 0, n-1, x) ==> a[\result] == x;
  ensures !contains(a, 0, n-1, x) ==> \result == -1;
 */
int binary_search(int a[], int n, int x);