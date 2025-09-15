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
    if (baseEdge <= 0 || height <= 0) {
        return -1;
    }

    double baseEdgeSquared = (double)baseEdge * baseEdge;
    double slantHeight = sqrt((baseEdge * 0.5) * (baseEdge * 0.5) + (double)height * height);
    double lateralArea = 2.0 * baseEdge * slantHeight;

    double totalArea = baseEdgeSquared + lateralArea;
    if (totalArea > (double)INT_MAX) {
        return -1;
    }

    return (int)totalArea;
}
