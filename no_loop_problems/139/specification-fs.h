// This predicate ensures that if the house is an even number that it is reached
/*@ predicate evenRouteSolution(int n, int a, int out) =
    \exists integer moves_right, moves_left;
    0 <= moves_right <= n &&
    0 <= moves_left <= n &&
    a == n - 2 * moves_right + 2 * moves_left && // Ensure that the solution ends at a
    1 + moves_right + moves_left == out;
*/

/*@ predicate smallerEvenRouteSolution(int n, int a, int out) =
    \exists integer moves_right, moves_left;
    0 <= moves_right <= n &&
    0 <= moves_left <= n &&
    a == n - 2 * moves_right + 2 * moves_left && // Ensure that the solution ends at a
    1 + moves_right + moves_left < out;
*/

// This predicate ensures that if the house is an odd number that it is reached
/*@ predicate oddRouteSolution(int n, int a, int out) =
    \exists integer moves_right, moves_left;
    0 <= moves_right <= n &&
    0 <= moves_left <= n &&
    a == 1 + 2 * moves_right - 2 * moves_left && // Ensure that the solution ends at a
    1 + moves_right + moves_left == out;
*/

/*@ predicate smallerOddRouteSolution(int n, int a, int out) =
    \exists integer moves_right, moves_left;
    0 <= moves_right <= n &&
    0 <= moves_left <= n &&
    a == 1 + 2 * moves_right - 2 * moves_left && // Ensure that the solution ends at a
    1 + moves_right + moves_left < out;
*/

/*@
    requires \valid(out);
    requires 1 <= a <= n <= 100000;
    requires n % 2 == 0;
    assigns *out;
    behavior a_is_even:
        assumes a % 2 == 0;
        ensures evenRouteSolution(n, a, *out);
        ensures !smallerEvenRouteSolution(n, a, *out);
    behavior a_is_odd:
        assumes a % 2 == 1;
        ensures oddRouteSolution(n, a, *out);
        ensures !smallerOddRouteSolution(n, a, *out);
    complete behaviors;
    disjoint behaviors;
*/
void calculateMinimumTimeToHouse(int n, int a, int *out);