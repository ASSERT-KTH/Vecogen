/*
    Petr wants to make a calendar for current month. For this purpose he draws a table in which columns correspond to weeks (a week is seven consequent days from Monday to Sunday), rows correspond to weekdays, and cells contain dates. For example, a calendar for January 2017 should look like on the picture: Petr wants to know how many columns his table should have given the month and the weekday of the first date of that month? Assume that the year is non-leap.

    Input
    The input contains two integers m and d (1 ≤ m ≤ 12, 1 ≤ d ≤ 7) — the number of month (January is the first month, December is the twelfth) and the weekday of the first date of this month (1 is Monday, 7 is Sunday).

    Output
    Output a single integer: the number of columns the table should have.
*/
void calculateNumberOfCalendarColumns(int m, int d, int *out);