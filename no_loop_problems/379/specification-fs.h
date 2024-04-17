/*@ predicate isValidSolution(integer a, integer b, integer c, integer out) =
    \exists integer a_used, b_used, c_used;
    0 <= a_used <= a &&
    0 <= b_used <= b &&
    0 <= c_used <= c &&
    4 * a_used == 2 * b_used == c_used &&
    a_used + b_used + c_used == out;
*/

/*@ predicate existsLargerSolution(integer a, integer b, integer c, integer out) =
    \exists integer a_used, b_used, c_used;
    0 <= a_used <= a &&
    0 <= b_used <= b &&
    0 <= c_used <= c &&
    4 * a_used == 2 * b_used == c_used &&
    a_used + b_used + c_used > out;
*/

/*@
    requires \valid(out);
    requires 1 <= a <= 1000;
    requires 1 <= b <= 1000;
    requires 1 <= c <= 1000;
    assigns *out;
    ensures isValidSolution(a, b, c, *out);
    ensures !existsLargerSolution(a, b, c, *out);
*/
void calculateMaxFruitsForCompote(int a, int b, int c, int *out);