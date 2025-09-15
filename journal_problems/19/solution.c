/*
  In a scenario involving geometric shapes, the goal is to compute the surface area of a square pyramid. 
  This pyramid is defined by its base edge length and height, both of which must be positive values.

  Input
  - Two integers, baseEdge and height. 
  - The value of baseEdge must be greater than 0.
  - The value of height must also be greater than 0.

  Output
  - A single integer representing the surface area of the square pyramid, calculated based on the provided dimensions.
*/

#include <limits.h>

/*@
  requires baseEdge > 0;
  requires height > 0;
  requires (long long)baseEdge * baseEdge + 2LL * baseEdge * height <= INT_MAX;
  assigns \nothing;
  ensures \result == baseEdge * baseEdge + 2 * baseEdge * height;
@*/
int SquarePyramidSurfaceArea(int baseEdge, int height) {
    long long area_ll = (long long)baseEdge * baseEdge + 2LL * baseEdge * height;
    return (int)area_ll;
}