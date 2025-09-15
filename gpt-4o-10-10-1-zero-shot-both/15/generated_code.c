#include <stdbool.h>

/*The task involves determining the number of equal integers among three given integers. The integers can represent various values, and the goal is to identify how many of them are the same.

    Input
    Three integers, denoted as a, b, and c. Each integer can take any value within the range of standard integer limits.

    Output
    The output is an integer that indicates the count of equal numbers among the three inputs. The result will be a value between 1 and 3, where:
    - A result of 3 indicates that all three integers are equal.
    - A result of 2 indicates that exactly two of the integers are equal.
    - A result of 1 indicates that all three integers are distinct.
*/

/*@
requires \true;
    assigns \nothing;
    ensures 1 <= \result <= 3;
    ensures (\result == 3) ==> a == b && b == c;
    ensures (\result == 2) ==> (a == b || b == c || a == c) && !(a == b && b == c);
    ensures (\result == 1) ==> a != b && b != c && a != c;
@
*/

int CountEqualNumbers(int a, int b, int c) {
    if (a == b && b == c) {
        return 3;
    } else if (a == b || b == c || a == c) {
        return 2;
    } else {
        return 1;
    }
}
