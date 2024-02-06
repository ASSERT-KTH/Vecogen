#include "selection_sort.h"

/*@
  requires \valid(a+i) && \valid(a+j);
  assigns a[i], a[j];
  ensures swap_at_indices{Pre, Post}(a, i, j);
 */
static void swap(int a[], int i, int j)
{
    int temp = a[i];
    a[i] = a[j];
    a[j] = temp;
}

/*@
  requires n >= 1;
  requires \valid(a + (0..n-1));
  assigns a[0..n-1];
  ensures sorted(a, n);
  ensures permutation{Pre, Post}(a, n);
 */
void selection_sort(int a[], int n)
{
    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer k, l; 0 <= k < i <= l < n ==> a[k] <= a[l];
      loop assigns i, a[0..n-1];
      loop variant n - i;
    */
    for (int i = 0; i < n - 1; ++i) {
        int min_index = i;
        /*@
          loop invariant i <= j < n;
          loop invariant min_index == i || (\forall integer k; i <= k < j ==> a[k] >= a[min_index]);
          loop assigns j, min_index;
          loop variant n - j;
        */
        for (int j = i + 1; j < n; ++j) {
            //@ assert i < j <= n; // Assertion to ensure the index relationship is correct
            //@ assert min_index == i || a[min_index] <= a[j]; // Assertion to ensure the minimum index is correct
            if (a[j] < a[min_index]) {
                min_index = j;
            }
        }
        swap(a, i, min_index);
        //@ assert sorted(a, i + 1); // Assertion to ensure partial array is sorted after each iteration
    }
    //@ assert sorted(a, n); // Assertion to ensure the entire array is sorted at the end
}
