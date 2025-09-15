/*Petr wants to make a calendar for current month. For this purpose he draws a table in which columns correspond to weeks (a week is seven consequent days from Monday to Sunday), rows correspond to weekdays, and cells contain dates. For example, a calendar for January 2017 should look like on the picture: Petr wants to know how many columns his table should have given the month and the weekday of the first date of that month? Assume that the year is non-leap.

    Input
    The input contains two integers m and d (1 <= m <= 12, 1 <= d <= 7) — the number of month (January is the first month, December is the twelfth) and the weekday of the first date of this month (1 is Monday, 7 is Sunday).

    Output
    Output a single integer: the number of columns the table should have.
*/

//@ logic integer length_of_month(integer m) = (m == 2) ? 28 : 30 + (m + (m / 8)) % 2;

/*@
predicate isValidSolution(integer m, integer d, integer out) =
    \exists integer full_weeks, remainder_before, remainder_after;
    remainder_before == (8 - d) &&
    0 <= remainder_after <= 6 &&
    length_of_month(m) == remainder_before + 7 * full_weeks + remainder_after &&
    out == 1 + full_weeks + (remainder_after > 0 ? 1 : 0);
*/

/*@
predicate existsLargerSolution(integer m, integer d, integer out) =
    \exists integer full_weeks, remainder_before, remainder_after, solution;
    remainder_before == (8 - d) &&
    0 <= remainder_after <= 6 &&
    length_of_month(m) == remainder_before + 7 * full_weeks + remainder_after &&
    solution == 1 + full_weeks + (remainder_after > 0 ? 1 : 0) &&
    solution > out;
*/

/*@
requires 1 <= m <= 12;
    requires 1 <= d <= 7;
    assigns \nothing;
    ensures isValidSolution(m, d, \result);
    ensures !existsLargerSolution(m, d, \result);
*/

int calculateNumberOfCalendarColumns(int m, int d) {
    int length_of_month = (m == 2) ? 28 : 30 + (m + (m / 8)) % 2;
    int remainder_before = 8 - d;
    int days_remaining = length_of_month - remainder_before;
    int full_weeks = days_remaining / 7;
    int remainder_after = days_remaining % 7;
    return 1 + full_weeks + (remainder_after > 0 ? 1 : 0);
}
