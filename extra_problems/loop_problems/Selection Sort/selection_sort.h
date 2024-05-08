/* Method selection_sort() sorts the array a[] of n elements using
   Selection Sort algorithm. */

/*@
  predicate sorted(int *a, integer n) =
    \forall integer i; 0 <= i <= n-2 ==> a[i] <= a[i+1];

  predicate swap_at_indices{L1, L2}(int *a, integer i, integer j) =
    \at(a[i], L1) == \at(a[j], L2) && \at(a[i], L2) == \at(a[j], L1);

  // array a[] (of n elements) at labels L1 and L2 differs only by a swap at indices
  // i and j
  predicate swap_in_array{L1, L2}(int *a, integer n, integer i, integer j) =
    swap_at_indices{L1, L2}(a, i, j) &&
    \forall integer k; (0 <= k <= n-1 && k!=i && k!=j) ==>
    \at(a[k], L1) == \at(a[k], L2);

  // define how array a[] (of n elements) at label L1 is a permutation of it at
  // label L2
  inductive permutation{L1, L2}(int *a, integer n)
  {
    case reflexive{L1}:
      \forall int *a, integer n; permutation{L1, L1}(a, n);

    case swap{L1, L2}:
      \forall int *a, integer n, i, j; 0 <= i < j <= n-1 &&
      swap_in_array{L1, L2}(a, n, i, j) ==> permutation{L1, L2}(a, n);

    case transitive{L1, L2, L3}:
      \forall int *a, integer n; permutation{L1, L2}(a, n) &&
      permutation{L2, L3}(a, n) ==> permutation{L1, L3}(a, n);
  }
 */

/*@
  requires \valid(a+i) && \valid(a+j);
  assigns a[i], a[j];
  ensures swap_at_indices{Pre, Post}(a, i, j);
 */
static void swap(int a[], int i, int j);

/*@
  requires n >= 1;
  requires \valid(a + (0..n-1));
  assigns a[0..n-1];
  ensures sorted(a, n);
  ensures permutation{Pre, Post}(a, n);
 */
void selection_sort(int a[], int n);