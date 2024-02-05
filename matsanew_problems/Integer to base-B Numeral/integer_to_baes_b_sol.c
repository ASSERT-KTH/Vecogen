#include <limits.h>

/* Given any non-negative integer n, we can represent it as a sequence of
   digits in base b using Positional Numeral System (e.g. the routinely used
   decimal and binary numeral systems).

   Method int_to_seq() finds such sequence of digits for the specified n and b
   and populates them in array a[] starting at the returned index.
   Method seq_to_int() returns integer n for the specified b and sequences of digits
   in array a[] (indices 0 to size-1).

   The order of digits in the array is most-significant (at lower index) to
   least-significant (at higher index).

   We need to specify -machdep option to allow RTE to use 64 bits long type
   (used in method seq_to_int()).
 */

/*@
  logic integer power(integer x, integer y) =
    y >= 1 ? power(x, y-1)*x : 1;

  // Integer value of a sequences of digits (array a from indices s to e) in base b.
  // Definition used by int_to_seq().
  logic integer int_val1(int *a, integer s, integer e, integer b) =
    s <= e ? a[s]*power(b, e-s) + int_val1(a, s+1, e, b) : 0;

  // Integer value of a sequences of digits (array a of l elements) in base b.
  // Definition used by seq_to_int()
  logic integer int_val2(int *a, integer l, integer b) =
    l > 0 ? int_val2(a, l-1, b)*b + a[l-1] : 0;

  // Array a (indices s to e) is same at labels L1 and L2.
  predicate unchanged{L1, L2}(int *a, integer s, integer e) =
    \forall integer i; s <= i <= e ==> \at(a[i], L1) == \at(a[i], L2);

  axiomatic axm
  {
    // The below statement should preferably be specified as a Lemma and proved.
    // But could not make the provers prove the lemma, so using this as an axiom.

    axiom int_val_unchanged{L1, L2}:
      \forall int *a, integer s, e, b; unchanged{L1, L2}(a, s, e) ==>
        int_val1{L1}(a, s, e, b) == int_val1{L2}(a, s, e, b);
  }
 */

/*@
  requires n >= 0 && b >= 2 && size >= 1;
  requires \valid(a + (0..size-1));
  assigns a[0..size-1];
  ensures \result == -1 ||
          (\result >= 0 && int_val1(a, \result, size-1, b) == n &&
           \forall int i; \result <= i <= size-1 ==> 0 <= a[i] < b);
 */
int int_to_seq(int n, int b, int a[], int size)
{
    int i;

    if (n == 0)
    {
        a[size - 1] = 0;
        return size - 1;
    }

    i = size - 1;

    /*@
      loop assigns n, i, a[0..size-1];
      loop invariant -1 <= i <= size-1;
      loop invariant 0 <= n <= \at(n, LoopEntry);
      loop invariant P: n*power(b, size-1-i) + int_val1(a, i+1, size-1, b) ==
                        \at(n, LoopEntry);
      loop invariant \forall int j; i+1 <= j <= size-1 ==> 0 <= a[j] < b;
      loop variant i+1;
     */
    while (n > 0 && i >= 0)
    {
        a[i] = n % b;
        //@assert unchanged{LoopCurrent, Here}(a, i+1, size-1);

        n = n / b;

        //@assert n*b + a[i] == \at(n, LoopCurrent);
        /*@assert a[i]*power(b, size-1-i) + int_val1(a, i+1, size-1, b) ==
                  int_val1(a, i, size-1, b); */

        i = i - 1;
    }

    if (n > 0)
        return -1;

    /* Invariant P holds with n = 0 */
    return i + 1;
}

/*@
  requires size >= 1 && b >= 2;
  requires \valid(a + (0..size-1));
  requires \forall int i; 0 <= i <= size-1 ==> 0 <= a[i] < b;
  assigns \nothing;
  ensures \result == -1 || (\result >= 0 && \result == int_val2(a, size, b));
 */
int seq_to_int(int a[], int size, int b)
{
    int i, n;

    i = 0;
    n = 0;

    /*@
      loop assigns n, i;
      loop invariant 0 <= i <= size;
      loop invariant n >= 0;
      loop invariant int_val2(a, i, b) == n;
      loop variant size-i;
     */
    while (i < size)
    {
        long n1 = n;

        n1 = n1 * b + a[i];

        if (n1 > INT_MAX)
            return -1;

        n = n1;
        i = i + 1;
    }

    return n;
}