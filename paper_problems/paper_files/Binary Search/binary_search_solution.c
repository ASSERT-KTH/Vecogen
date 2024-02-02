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
  assigns \nothing;
 */
int binary_search(int arr[], int n, int x)
{
    int l, r;
    /* r can become -1, so using signed int */

    l = 0;
    r = n - 1;

    /*@
      loop assigns l, r;
      loop invariant (l == r+1) || (l <= r && 0 <= l <= n-1 && 0 <= r <= n-1);
      loop invariant !contains(arr, 0, l-1, x) && !contains(arr, r+1, n-1, x);
      loop invariant contains(arr, 0, n-1, x) ==> contains(arr, l, r, x);
      loop variant r-l+1;
     */
    while (l <= r)
    {
        int m = l + (r - l) / 2;

        if (arr[m] == x)
            return m;

        if (arr[m] < x)
        {
            //@assert !contains(arr, l, m, x);
            l = m + 1;
        }
        else
        {
            //@assert !contains(arr, m, r, x);
            r = m - 1;
        }
    }

    return -1;
}