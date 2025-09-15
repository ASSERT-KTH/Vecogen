#include <stdbool.h>

/*In a scenario where you are given three distinct integer values, the goal is to determine the median value among them.  The median is defined as the middle value when the three numbers are sorted in order.

    Input
    Three integers, a, b, and c, each of which can take any value within the range of typical integer limits.

    Output
    The output will be the median value of the three integers, which will also be an integer that falls within the range
    defined by the smallest and largest of the three input integers.
*/

/*@
requires \true;
  assigns \nothing;
  ensures \result == a || \result == b || \result == c;
  ensures (\result >= a && \result <= b)
        || (\result >= b && \result <= a)
        || (\result >= a && \result <= c)
        || (\result >= c && \result <= a)
        || (\result >= b && \result <= c)
        || (\result >= c && \result <= b);
*/

int medianOfThree(int a, int b, int c) {
    if (a < b) {
        if (b < c) {
            return b;
        } else {
            if (a < c) {
                return c;
            } else {
                return a;
            }
        }
    } else {
        if (a < c) {
            return a;
        } else {
            if (b < c) {
                return c;
            } else {
                return b;
            }
        }
    }
}
