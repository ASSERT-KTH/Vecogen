#include <limits.h>

/*
    In a scenario where you need to analyze the calendar months, the goal is to determine the number of months that contain 30 days. The task involves evaluating the months in order starting from January; the numerical representation ranges from 1 to 12 and repeats cyclically when the count exceeds 12.

    Input
    The input consists of a single integer variable representing the number of months to consider, which must be within the range of 0 to INT_MAX, inclusive.

    Output
    The output is a single integer value that indicates the count of months, from January up to the specified number of months, that have exactly 30 days. The result will be a non-negative integer.
*/

/*@ logic integer MonthTable(integer m) =
      m == 1  ? 31 :
      m == 2  ? 28 :
      m == 3  ? 31 :
      m == 4  ? 30 :
      m == 5  ? 31 :
      m == 6  ? 30 :
      m == 7  ? 31 :
      m == 8  ? 31 :
      m == 9  ? 30 :
      m == 10 ? 31 :
      m == 11 ? 30 :
      m == 12 ? 31 :
      0;
*/

/*@ // # of 30-day months in the first n months of a year (0<=n<=12).
    logic integer Count30_prefix(integer n) =
        (n>0  && MonthTable(1)  ==30 ? 1:0) +
        (n>1  && MonthTable(2)  ==30 ? 1:0) +
        (n>2  && MonthTable(3)  ==30 ? 1:0) +
        (n>3  && MonthTable(4)  ==30 ? 1:0) +
        (n>4  && MonthTable(5)  ==30 ? 1:0) +
        (n>5  && MonthTable(6)  ==30 ? 1:0) +
        (n>6  && MonthTable(7)  ==30 ? 1:0) +
        (n>7  && MonthTable(8)  ==30 ? 1:0) +
        (n>8  && MonthTable(9)  ==30 ? 1:0) +
        (n>9  && MonthTable(10) ==30 ? 1:0) +
        (n>10 && MonthTable(11) ==30 ? 1:0) +
        (n>11 && MonthTable(12) ==30 ? 1:0);
*/

/*@ // Total # of 30-day months among the first n months from January.
    logic integer Count30_total(integer n) =
      (n/12) * Count30_prefix(12) + Count30_prefix(n % 12);
*/

/*@ requires 0 <= month <= INT_MAX;
    assigns \nothing;
    ensures \result == Count30_total(month);
*/

int CountMonthsWith30Days(int month) {
    if (month == 0) return 0;

    int full_cycles = month / 12;
    int remaining_months = month % 12;

    int count_in_cycle = 4; // There are always 4 months with 30 days in Jan-Dec
    int count_remaining = 0;

    if (remaining_months >= 4) count_remaining++;
    if (remaining_months >= 6) count_remaining++;
    if (remaining_months >= 9) count_remaining++;
    if (remaining_months >= 11) count_remaining++;

    return full_cycles * count_in_cycle + count_remaining;
}
