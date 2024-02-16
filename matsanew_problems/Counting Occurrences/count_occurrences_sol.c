#include <stddef.h>

typedef unsigned int uint;

/*@
  axiomatic axm
  {
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
  uint count = 0;
  /*@
    loop invariant 0 <= i <= n;
    loop invariant count == count(a, i, x);
    loop assigns i, count;
    loop variant n - i;
   */
  for (uint i = 0; i < n; i++)
  {
    if (a[i] == x)
    {
      count++;
    }
  }
  return count;
}
