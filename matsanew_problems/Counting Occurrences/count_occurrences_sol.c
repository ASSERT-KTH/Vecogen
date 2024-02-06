/* Method occurs() counts the number of times x occurs in array a[] of n elements. */

typedef unsigned int uint;

/*@
  axiomatic axm
  {
    // Define the logical-function count() as returning the number of occurences of x
    // among first n elements of array a[].
    logic uint count(int *a, uint n, int x)
      reads a[0..n-1];

    axiom base:
      \forall int *a, x; count(a, (uint)0, x) == 0;

    axiom recursion:
      \forall int *a, x, uint n; n >= 1 ==>
      (count(a, n, x) == count(a, (uint)(n-1), x) + ((a[n-1]==x) ? 1 : 0));
  }
 */

/*@
  requires \valid(a + (0..n-1));
  assigns \nothing;
  ensures \result == count(a, n, x);
 */
uint occurs(int *a, uint n, int x)
{
    uint i, c;

    i = 0;
    c = 0;

    /*@
      loop assigns i, c;
      loop invariant c == count(a, i, x);
      loop invariant 0 <= i <= n;
      loop variant n - i;
     */
    while (i < n)
    {
        if (a[i] == x)
            c = c + 1;

        i = i + 1;
    }

    return c;
}
