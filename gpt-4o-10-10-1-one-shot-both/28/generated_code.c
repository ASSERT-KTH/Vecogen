#include <limits.h>

/*
    Analyze calendar months to count how many have 31 days. Months are evaluated
    in order starting from January; numbering is 1–12 and repeats cyclically when
    the count exceeds 12.

    Input
    A single integer variable representing the number of months to consider,
    within 0 to INT_MAX inclusive.

    Output
    A single integer: the count of 31-day months from January up to the specified
    number of months. The result is non-negative.
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

/*@ // # of 31-day months in the first n months of a year (0<=n<=12).
    logic integer Count31_prefix(integer n) =
        (n>0  && MonthTable(1)  ==31 ? 1:0) +
        (n>1  && MonthTable(2)  ==31 ? 1:0) +
        (n>2  && MonthTable(3)  ==31 ? 1:0) +
        (n>3  && MonthTable(4)  ==31 ? 1:0) +
        (n>4  && MonthTable(5)  ==31 ? 1:0) +
        (n>5  && MonthTable(6)  ==31 ? 1:0) +
        (n>6  && MonthTable(7)  ==31 ? 1:0) +
        (n>7  && MonthTable(8)  ==31 ? 1:0) +
        (n>8  && MonthTable(9)  ==31 ? 1:0) +
        (n>9  && MonthTable(10) ==31 ? 1:0) +
        (n>10 && MonthTable(11) ==31 ? 1:0) +
        (n>11 && MonthTable(12) ==31 ? 1:0);
*/

/*@ // Total # of 31-day months among the first n months from January.
    logic integer Count31_total(integer n) =
      (n/12) * Count31_prefix(12) + Count31_prefix(n % 12);
*/

/*@ requires 0 <= month <= INT_MAX;
    assigns \nothing;
    ensures \result == Count31_total(month);
*/

int CountMonthsWith31Days(int month) {
    int completeYears = month / 12;
    int remainderMonths = month % 12;

    // Total number of 31-day months in a year is 7
    int countInCompleteYears = completeYears * 7;

    // Calculate the number of 31-day months in the remainder months
    int countInRemainderMonths = 0;

    if (remainderMonths >= 1) countInRemainderMonths += 1;
    if (remainderMonths >= 3) countInRemainderMonths += 1;
    if (remainderMonths >= 5) countInRemainderMonths += 1;
    if (remainderMonths >= 7) countInRemainderMonths += 1;
    if (remainderMonths >= 8) countInRemainderMonths += 1;
    if (remainderMonths >= 10) countInRemainderMonths += 1;
    if (remainderMonths >= 12) countInRemainderMonths += 1;

    return countInCompleteYears + countInRemainderMonths;
}
