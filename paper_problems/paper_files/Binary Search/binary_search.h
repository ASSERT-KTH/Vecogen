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
int binary_search(int arr[], int n, int x);