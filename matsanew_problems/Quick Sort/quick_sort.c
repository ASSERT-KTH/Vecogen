#include <limits.h>

/*@ 
  // Predicates and axioms from the header file...
 */

static void swap(int a[], int i, int j) {
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
static int partition(int a[], int s, int e, int p) {
    //@ assert \valid(a+(s..e));
    int pivot = a[e];
    int i = s - 1;
    /*@
      loop invariant s <= j <= e+1;
      loop invariant s <= i < j <= e;
      loop invariant lesser(a, s, i, pivot);
      loop invariant greater(a, j, e, pivot);
      loop assigns i, j, a[s..e];
      loop variant j;
    */
    for (int j = s; j <= e; j++) {
        if (a[j] <= pivot) {
            i++;
            swap(a, i, j);
        }
    }
    swap(a, i + 1, e);
    //@ assert lesser(a, s, i, pivot);
    //@ assert greater(a, i + 1, e, pivot);
    return i + 1;
}

/*@ 
  requires 0 <= s <= e < INT_MAX;
  requires \valid(a+(s..e));
  assigns a[s..e];
  ensures sorted(a, s, e);
  ensures permutation{Pre, Post}(a, s, e);
 */
void quick_sort(int a[], int s, int e) {
    if (s < e) {
        int pivot_index = partition(a, s, e, a[e]);
        //@ assert s <= pivot_index <= e;
        //@ assert permutation{Pre, Here}(a, s, e);
        quick_sort(a, s, pivot_index - 1);
        //@ assert sorted(a, s, pivot_index - 1);
        quick_sort(a, pivot_index + 1, e);
        //@ assert sorted(a, pivot_index + 1, e);
    }
}
