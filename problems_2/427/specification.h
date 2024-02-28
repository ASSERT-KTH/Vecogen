/*  Petr and a calendar
    Petr wants to make a calendar for current month. For this purpose he draws a table in which columns correspond to weeks (a week is seven consequent days from Monday to Sunday), rows correspond to weekdays, and cells contain dates. For example, a calendar for January 2017 should look like on the picture: Petr wants to know how many columns his table should have given the month and the weekday of the first date of that month? Assume that the year is non-leap.
*/

/*@
    requires \valid(out);
    requires 1 <= m <= 12 && 1 <= d <= 7;
    assigns
        \nothing;
    ensures
        \result == 5 || \result == 6;
*/
int calendar(int m, int d, int *out);