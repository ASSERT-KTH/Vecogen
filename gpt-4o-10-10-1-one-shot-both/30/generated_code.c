#include <limits.h>

/*In a 3D arrangement of objects (like stacking spheres in layers), the total number of objects needed to form a complete tetrahedron with n layers follows a specific pattern. Each layer is a triangular number, and the full structure builds upon the previous layers.

  Write a function that computes the number of objects required to build a tetrahedron with n layers. The input is a nonnegative integer n, and the output is the corresponding total number of objects.

  Input
  A nonnegative integer n (0 <= n).

  Output
  An integer representing the total number of objects in a tetrahedron of n layers.
*/

/*@
requires n >= 0;
  requires ((long long)n * (n + 1) * (n + 2)) / 6 <= INT_MAX;
  assigns \nothing;
  ensures \result == n*(n+1)*(n+2)/6;
@
*/

int TetrahedralNumber(int n) {
    return (n / 6) * (n + 1) * (n + 2) + (((n % 6) * (n + 1) * (n + 2)) / 6);
}
