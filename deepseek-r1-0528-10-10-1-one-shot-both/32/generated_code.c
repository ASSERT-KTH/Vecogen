#include <stdint.h>

#include <limits.h>

/*A centered hexagonal number represents a count of points arranged in a hexagonal pattern with a single central point and surrounding hexagonal layers. The sequence begins with 1 and grows as new layers are added around the center. Write a function that returns the total number of points in the hexagonal arrangement at the n-th stage, where n is a non-negative integer indicating how many layers (including the center) are present.

    Input
    A non-negative integer n.

    Output
    An integer representing the total number of points in a centered hexagonal pattern with n layers.
*/

/*@
requires 3u * n * (n - 1) <= UINT32_MAX - 1u;
    assigns \nothing;
    ensures \result == 3u * n * (n - 1) + 1u;
*/

uint32_t CenteredHexagonalNumber(uint32_t n) {
    return 3u * n * (n - 1u) + 1u;
}
