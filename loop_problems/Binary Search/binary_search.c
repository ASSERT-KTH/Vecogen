#include <stddef.h>

/*@
  // Does array a[] contain x between its indices s and e?
  predicate contains(int *a, integer s, integer e, int x) =
    \exists integer i; s <= i <= e && a[i] == x;
*/

/*@
  requires \valid_read(a + (0..n-1));
  requires n > 0;
  requires \forall int i, j; 0 <= i < j <= n-1 ==> a[i] <= a[j];
  ensures contains(a, 0, n-1, x) ==> a[\result] == x;
  ensures !contains(a, 0, n-1, x) ==> \result == -1;
*/
int binary_search(int a[], int n, int x)
{
  int low = 0;
  int high = n - 1;

  /*@
    loop invariant 0 <= low <= high + 1;
    loop invariant high <= n - 1;
    loop invariant \forall integer k; 0 <= k < low ==> a[k] < x;
    loop invariant \forall integer k; high < k <= n - 1 ==> a[k] > x;
    loop assigns low, high;
    loop variant high - low;
  */
  while (low <= high)
  {
    int mid = low + (high - low) / 2;

    if (a[mid] == x)
    {
      return mid;
    }
    else if (a[mid] < x)
    {
      low = mid + 1;
    }
    else
    {
      high = mid - 1;
    }
  }

  return -1;
}
