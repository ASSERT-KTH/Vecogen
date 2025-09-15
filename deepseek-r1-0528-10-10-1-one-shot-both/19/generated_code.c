#include <limits.h>

/*In a scenario involving geometric shapes, the goal is to compute the surface area of a square pyramid. 
  This pyramid is defined by its base edge length and height, both of which must be positive values.

  Input
  - Two integers, baseEdge and height. 
  - The value of baseEdge must be greater than 0.
  - The value of height must also be greater than 0.

  Output
  - A single integer representing the surface area of the square pyramid, calculated based on the provided dimensions.
*/

/*@
requires baseEdge > 0;
  requires height > 0;
  requires (long long)baseEdge * baseEdge + 2LL * baseEdge * height <= INT_MAX;
  assigns \nothing;
  ensures \result == baseEdge * baseEdge + 2 * baseEdge * height;
@
*/

int SquarePyramidSurfaceArea(int baseEdge, int height) {
    long long b = (long long)baseEdge;
    long long h = (long long)height;
    long long result = b * b + 2LL * b * h;
    return (int)result;
}
