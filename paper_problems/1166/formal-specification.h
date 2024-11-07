/*@ logic integer amountOfDifferentNumbers(integer a, integer b, integer c, integer d) =
    1 + (int) (a != b) + (int) (a != c && b != c) + (int) (a != d && b != d && c != d);
 */

/*@ predicate IsValidSolution(integer a, integer b, integer c, integer d, integer out) =
    out + amountOfDifferentNumbers(a, b, c, d) >= 4;
*/

/*@ predicate ExistsSmallerSolution(integer a, integer b, integer c, integer d, integer out) =
    \exists integer unique_colors;
    0 <= unique_colors && unique_colors + amountOfDifferentNumbers(a, b, c, d) >= 4 &&
        unique_colors < out;
*/

/*@
    requires \valid(out);
    requires 1 <= a <= 1000000000;
    requires 1 <= b <= 1000000000;
    requires 1 <= c <= 1000000000;
    requires 1 <= d <= 1000000000;
    assigns *out;
    ensures IsValidSolution(a, b, c, d, *out);
    ensures !ExistsSmallerSolution(a, b, c, d, *out);
*/