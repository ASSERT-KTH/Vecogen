/*
    Petr wants to make a calendar for current month. For this purpose he draws a table in which columns correspond to weeks (a week is seven consequent days from Monday to Sunday), rows correspond to weekdays, and cells contain dates. For example, a calendar for January 2017 should look like on the picture: Petr wants to know how many columns his table should have given the month and the weekday of the first date of that month? Assume that the year is non-leap.
*/

//@ logic integer length_of_month(integer m) = (m == 2) ? 28 : 30 + (m + (m / 8)) % 2;

/*@
    requires \valid(out);
    requires 1 <= m <= 12 && 1 <= d <= 7;
    assigns *out;
    ensures *out == (length_of_month(m) + d - 1 ) / 7 + ((length_of_month(m) - 8 + d) % 7 != 0 ? 1 : 0);
*/
void calculateNumberOfCalendarColumns(int m, int d, int *out)
{
    int dm[12] = {31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};
    m--;
    d--;
    dm[m] = dm[m] - (7 - d);
    if (dm[m] % 7 == 0)
    {
        *out = dm[m] / 7 + 1;
    }
    else
    {
        *out = dm[m] / 7 + 2;
    }
}
