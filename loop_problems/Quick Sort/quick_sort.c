#include <limits.h>

/* Method quick_sort() sorts the subarray (from indices s to e) of array a[]
   using Quick Sort algorithm. */

/*@
  predicate lesser(int *a, integer s, integer e, int p) =
    \forall int i; s <= i <= e ==> a[i] <= p;

  predicate greater(int *a, integer s, integer e, int p) =
    \forall int i; s <= i <= e ==> a[i] > p;

  predicate sorted(int *a, integer s, integer e) =
    \forall integer i; s <= i <= e-1 ==> a[i] <= a[i+1];

  predicate swap_at_indices{L1, L2}(int *a, integer i, integer j) =
    \at(a[i], L1) == \at(a[j], L2) && \at(a[i], L2) == \at(a[j], L1);

  // the array a[] at labels L1 and L2 differs only by a swap at indices i and j
  predicate swap_in_array{L1, L2}(int *a, integer s, integer e, integer i,
                                  integer j) =
    swap_at_indices{L1, L2}(a, i, j) &&
    \forall integer k; (s <= k <= e && k!=i && k!=j) ==>
    \at(a[k], L1) == \at(a[k], L2);

  predicate unchanged{L1, L2}(int *a, integer s, integer e) =
      \forall integer i; s <= i <= e ==> \at(a[i], L1)==\at(a[i], L2);

  // define how a subarray (indices s to e) of array a[] at label L1 is a permutation
  // of it at label L2
  inductive permutation{L1, L2}(int *a, integer s, integer e)
  {
    case reflexive{L1}:
      \forall int *a, integer s, e; permutation{L1, L1}(a, s, e);

    case swap{L1, L2}:
      \forall int *a, integer s, e, i, j; s <= i < j <= e &&
      swap_in_array{L1, L2}(a, s, e, i, j) ==> permutation{L1, L2}(a, s, e);

    case unchanged{L1, L2}:
      \forall int *a, integer s, e; unchanged{L1, L2}(a, s, e) ==>
      permutation{L1, L2}(a, s, e);

    case transitive{L1, L2, L3}:
      \forall int *a, integer s, e; permutation{L1, L2}(a, s, e) &&
      permutation{L2, L3}(a, s, e) ==> permutation{L1, L3}(a, s, e);

    case split{L1, L2}:
      \forall int *a, integer s, e, i; s <= i <= e && permutation{L1, L2}(a, s, i) &&
      permutation{L1, L2}(a, i+1, e) ==> permutation{L1, L2}(a, s, e);
  }

  // axioms added to assist the prover
  axiomatic axm
  {
    axiom perm_lesser{L1, L2}:
      \forall int *a, p, integer s, e; permutation{L1, L2}(a, s, e) &&
      lesser{L1}(a, s, e, p) ==> lesser{L2}(a, s, e, p);

    axiom perm_greater{L1, L2}:
      \forall int *a, p, integer s, e; permutation{L1, L2}(a, s, e) &&
      greater{L1}(a, s, e, p) ==> greater{L2}(a, s, e, p);
  }
 */

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
  requires 0 <= s <= e < INT_MAX;
  requires \valid(a+(s..e));
  assigns a[s..e];
  ensures s-1 <= \result <= e;
  ensures lesser(a, s, \result, p) && greater(a, \result+1, e, p);
  ensures permutation{Pre, Post}(a, s, e);
 */
static int partition(int a[], int s, int e, int p)
{
    int left = s;
    int right = e;

    /*@
      loop invariant s <= left && left <= e+1;
      loop invariant s <= right+1 && right <= e;
      loop invariant \forall integer k; s <= k && k < left ==> a[k] <= p;
      loop invariant \forall integer k; right < k && k <= e ==> a[k] > p;
      loop assigns left, right, a[s..e];
      loop variant right - left;
    */
    while (left <= right)
    {
        while (left <= e && a[left] <= p)
        {
            left++;
        }

        while (right >= s && a[right] > p)
        {
            right--;
        }

        if (left < right)
        {
            swap(a, left, right);
            left++;
            right--;
        }
    }
    return right; // The pivot index
}

/*@
  requires 0 <= s <= e < INT_MAX;
  requires \valid(a+(s..e));
  assigns a[s..e];
  ensures sorted(a, s, e);
  ensures permutation{Pre, Post}(a, s, e);
 */
void quick_sort(int a[], int s, int e)
{
    if (s < e)
    {
        int p = a[e]; // Adjusting pivot selection for simplicity
        int pivot = partition(a, s, e, p);

        quick_sort(a, s, pivot);
        quick_sort(a, pivot + 1, e);
    }
}