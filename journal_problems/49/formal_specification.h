/*@
predicate evenRouteSolution(int n, int a, int out) =
    \exists integer moves_right, moves_left;
    0 <= moves_right <= n &&
    0 <= moves_left <= n &&
    a == n - 2 * moves_right + 2 * moves_left && // Ensure that the solution ends at a
    1 + moves_right + moves_left == out;
*/

/*@
predicate smallerEvenRouteSolution(int n, int a, int out) =
    \exists integer moves_right, moves_left;
    0 <= moves_right <= n &&
    0 <= moves_left <= n &&
    a == n - 2 * moves_right + 2 * moves_left && // Ensure that the solution ends at a
    1 + moves_right + moves_left < out;
*/

/*@
predicate oddRouteSolution(int n, int a, int out) =
    \exists integer moves_right, moves_left;
    0 <= moves_right <= n &&
    0 <= moves_left <= n &&
    a == 1 + 2 * moves_right - 2 * moves_left && // Ensure that the solution ends at a
    1 + moves_right + moves_left == out;
*/

/*@
predicate smallerOddRouteSolution(int n, int a, int out) =
    \exists integer moves_right, moves_left;
    0 <= moves_right <= n &&
    0 <= moves_left <= n &&
    a == 1 + 2 * moves_right - 2 * moves_left && // Ensure that the solution ends at a
    1 + moves_right + moves_left < out;
*/

/*@
requires 1 <= a <= n <= 100000;
    requires n % 2 == 0;
    assigns \nothing;
    behavior a_is_even:
        assumes a % 2 == 0;
        ensures evenRouteSolution(n, a, \result);
        ensures !smallerEvenRouteSolution(n, a, \result);
    behavior a_is_odd:
        assumes a % 2 == 1;
        ensures oddRouteSolution(n, a, \result);
        ensures !smallerOddRouteSolution(n, a, \result);
    complete behaviors;
    disjoint behaviors;
*/

