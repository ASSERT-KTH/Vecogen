/*  Petr and a calendar
    Petr wants to make a calendar for current month. For this purpose he draws a table in which columns correspond to weeks (a week is seven consequent days from Monday to Sunday), rows correspond to weekdays, and cells contain dates. For example, a calendar for January 2017 should look like on the picture: Petr wants to know how many columns his table should have given the month and the weekday of the first date of that month? Assume that the year is non-leap.
*/

/*@
    requires \valid(out);
    requires 1 <= m <= 12 && 1 <= d <= 7;
    assigns
        \nothing;
    ensures *out == (\old(dm[m - 1]) - (7 - (d - 1))) % 7 == 0 ? (\old(dm[m - 1]) / 7 + 1) : (\old(dm[m - 1]) / 7 + 2);
*/

/*@
  requires 1 <= m && m <= 12;
  requires 1 <= d && d <= 7;
  requires \valid(out);
  ensures *out ==
    (
      // Calculate the number of days in the month minus the given day, plus one for inclusive counting
      ((m == 2 ? 28 : (m == 4 || m == 6 || m == 9 || m == 11 ? 30 : 31)) - d + 1) % 7 == 0
        ?
        // If the remainder is 0, calculate the full weeks
        ((m == 2 ? 28 : (m == 4 || m == 6 || m == 9 || m == 11 ? 30 : 31)) - d + 1) / 7
        :
        // If the remainder is not 0, add an extra week to account for the partial week
        ((m == 2 ? 28 : (m == 4 || m == 6 || m == 9 || m == 11 ? 30 : 31)) - d + 1) / 7 + 1
    );
*/
void calendar(int m, int d, int *out)
{
    int dm[12] = {31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};

    dm[m - 1] = dm[m - 1] - (7 - (d - 1));
    if (dm[m - 1] % 7 == 0)
    {
        *out = "%d\\n", dm[m - 1] / 7 + 1;
    }
    else
    {
        *out = "%d\\n", dm[m - 1] / 7 + 2;
    }
}
