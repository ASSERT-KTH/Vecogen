//@ logic integer length_of_month(integer m) = (m == 2) ? 28 : 30 + (m + (m / 8)) % 2;

/*@ predicate isValidSolution(integer m, integer d, integer out) =
    \exists integer full_weeks, remainder_before, remainder_after;
    remainder_before == (8 - d) &&
    0 <= remainder_after <= 6 &&
    length_of_month(m) == remainder_before + 7 * full_weeks + remainder_after &&
    out == 1 + full_weeks + (remainder_after > 0 ? 1 : 0);
*/

/*@ predicate existsLargerSolution(integer m, integer d, integer out) =
    \exists integer full_weeks, remainder_before, remainder_after, solution;
    remainder_before == (8 - d) &&
    0 <= remainder_after <= 6 &&
    length_of_month(m) == remainder_before + 7 * full_weeks + remainder_after &&
    solution == 1 + full_weeks + (remainder_after > 0 ? 1 : 0) &&
    solution > out;
*/

/*@
    requires \valid(out);
    requires 1 <= m <= 12;
    requires 1 <= d <= 7;
    assigns *out;
    ensures isValidSolution(m, d, *out);
    ensures !existsLargerSolution(m, d, *out);
*/
void calculateNumberOfCalendarColumns(int m, int d, int *out);