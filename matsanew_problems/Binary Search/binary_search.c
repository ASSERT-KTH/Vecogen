#include <stddef.h>

/*@ predicate contains(int *a, integer s, integer e, int x) =
  \exists integer i; s <= i <= e && a[i] == x;
 */

/*@ requires \valid_read(a + (0..n-1));
  requires n > 0;
  requires \forall int i, j; 0 <= i < j <= n-1 ==> a[i] <= a[j];
  ensures contains(a, 0, n-1, x) ==> a[\result] == x;
  ensures !contains(a, 0, n-1, x) ==> \result == -1;
 */
int binary_search(int a[], int n, int x) {
    int s = 0;
    int e = n - 1;

    /*@ loop assigns s, e;
      loop invariant (s == e+1) || (s <= e && 0 <= s <= n-1 && 0 <= e <= n-1);
      loop invariant !contains(a, 0, s-1, x) && !contains(a, e+1, n-1, x);
      loop invariant contains(a, 0, n-1, x) ==> contains(a, s, e, x);
      loop variant e-s+1;
     */
    while (s <= e) {
        int m = s + (e - s) / 2;
        int val = a[m];

        if (val == x)
            return m;
        else if (val < x) {
            s = m + 1;
            //@assert !contains(a, s, m, x);
        } else {
            e = m - 1;
            //@assert !contains(a, m, e, x);
        }
    }

    return -1;
}
