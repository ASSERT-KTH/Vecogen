//@ logic integer length_of_month(integer m) = (m == 2) ? 28 : 30 + (m + (m / 8)) % 2;

/*@
    requires \valid(out);
    requires 1 <= m <= 12 && 1 <= d <= 7;
    assigns *out;
    ensures *out == (length_of_month(m) + d - 1 ) / 7 + ((length_of_month(m) - 8 + d) % 7 != 0 ? 1 : 0);
*/
void calculateNumberOfCalendarColumns(int m, int d, int *out);