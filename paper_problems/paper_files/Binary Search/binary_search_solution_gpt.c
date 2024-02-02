#include <limits.h>

/*@
  // Loop invariant for binary search
  requires \forall int k; 0 <= k < i ==> arr[k] <= x;
  requires \forall int k; i <= k <= n-1 ==> arr[k] > x;
  assigns i, l, r;
  ensures i == \result ==> contains(arr, 0, n-1, x) && arr[i] == x;
  ensures \result == -1 ==> !contains(arr, 0, n-1, x);
 */
int binary_search(int arr[], int n, int x)
{
    int l = 0;
    int r = n - 1;
    int i = -1; // Initialize i to -1 indicating not found

    /*@
      loop invariant 0 <= l <= r <= n-1;
      loop invariant \forall int k; 0 <= k < l ==> arr[k] <= x;
      loop invariant \forall int k; r < k <= n-1 ==> arr[k] > x;
      loop assigns i, l, r;
      loop variant r - l + 1;
     */
    while (l <= r)
    {
        int mid = l + (r - l) / 2;

        if (arr[mid] == x)
        {
            // x found, update i and break
            i = mid;
            break;
        }
        else if (arr[mid] < x)
        {
            // Discard left half
            l = mid + 1;
        }
        else
        {
            // Discard right half
            r = mid - 1;
        }
    }

    return i;
}
