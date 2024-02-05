#include <limits.h>

/*@
  // Predicate that checks if the subarray arr[l..r] is sorted in ascending order
  predicate is_sorted(int *arr, integer l, integer r) =
    \forall integer i, j; l <= i < j <= r ==> arr[i] <= arr[j];
*/

/*@
  // Lemma stating that if a subarray is sorted and contains an element,
  // then it indeed contains that element
  lemma sorted_contains_implies_contains:
    \forall int *arr, integer l, r, x;
    is_sorted(arr, l, r) && contains(arr, l, r, x) ==> \exists integer i; l <= i <= r && arr[i] == x;
*/

/*@
  // Lemma stating that if a subarray is sorted and does not contain an element,
  // then it indeed does not contain that element
  lemma sorted_not_contains_implies_not_contains:
    \forall int *arr, integer l, r, x;
    is_sorted(arr, l, r) && !contains(arr, l, r, x) ==> \forall integer i; l <= i <= r ==> arr[i] != x;
*/

int binary_search(int arr[], int n, int x)
{
    /*@
      loop invariant 0 <= low <= high <= n - 1;
      loop invariant is_sorted(arr, 0, low - 1);
      loop invariant is_sorted(arr, high + 1, n - 1);
      loop invariant \forall integer k; 0 <= k < low ==> arr[k] < x;
      loop invariant \forall integer k; high < k <= n - 1 ==> arr[k] > x;
      loop assigns low, high;
      loop variant high - low;
     */
    int low = 0;
    int high = n - 1;

    while (low <= high)
    {
        int mid = low + (high - low) / 2;

        if (arr[mid] == x)
        {
            //@ assert contains(arr, 0, n-1, x);
            return mid;
        }
        else if (arr[mid] < x)
        {
            low = mid + 1;
        }
        else
        {
            high = mid - 1;
        }
    }

    //@ assert !contains(arr, 0, n-1, x);
    return -1;
}
