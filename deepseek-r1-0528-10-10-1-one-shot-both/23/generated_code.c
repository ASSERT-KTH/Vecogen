#include <limits.h>  // For INT_MAX

#include <stddef.h>  /* For NULL, if needed */

/*In a certain geometrical context, the goal is to calculate a specific surface area associated with a three-dimensional shape based on a provided dimension.

  Input
      The input consists of a single integer variable named 'size'. This variable represents a dimension of the shape and must be greater than 0 and less than or equal to 23170.

  Output
      The output of the function is an integer that represents the lateral surface area of the shape, computed based on the input 'size'. The result will be four times the square of the input size.
*/


/*For NULL, if needed
*/

/*@
requires size > 0 && size <= 23170;
  assigns \nothing;
  ensures \result == 4 * size * size;
@
*/

int LateralSurfaceArea(int size) {
    return 4 * size * size;
}
