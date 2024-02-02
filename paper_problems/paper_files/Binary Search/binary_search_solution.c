/* Method binary_search() looks for an integer x in a sorted array arr[] of size n.
    If x is found, the method returns the index of x in arr[];
    otherwise, it returns -1. */

/*@
  // Predicate that checks if array arr[] contain x (between indices l and r)
  predicate contains(int *arr, integer l, integer r, int x) =
    \exists integer i; l <= i <= r && arr[i] == x;
 */

/*@
  requires \valid_read(arr + (0..n-1));
  requires n > 0;

  // Predicate that has corted order
  requires \forall int i, j; 0 <= i < j <= n-1 ==> arr[i] <= arr[j];

  ensures contains(arr, 0, n-1, x) ==> arr[\result] == x;
  ensures !contains(arr, 0, n-1, x) ==> \result == -1;
 */
int binary_search(int a[], int n, int x)
{
    int s, e;
    /* e can become -1, so using signed int */

    s = 0;
    e = n - 1;

    /*@
      loop assigns s, e;
      loop invariant (s == e+1) || (s <= e && 0 <= s <= n-1 && 0 <= e <= n-1);
      loop invariant !contains(a, 0, s-1, x) && !contains(a, e+1, n-1, x);
      loop invariant contains(a, 0, n-1, x) ==> contains(a, s, e, x);
      loop variant e-s+1;
     */
    while (s <= e)
    {
        int m = s + (e - s) / 2;

        if (a[m] == x)
            return m;

        if (a[m] < x)
        {
            //@assert !contains(a, s, m, x);
            s = m + 1;
        }
        else
        {
            //@assert !contains(a, m, e, x);
            e = m - 1;
        }
    }

    return -1;
}