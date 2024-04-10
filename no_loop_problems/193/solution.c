/*
    On the planet Mars a year lasts exactly n days (there are no leap years on Mars). But Martians have the same weeks as earthlings — 5 work days and then 2 days off. Your task is to determine the minimum possible and the maximum possible number of days off per year on Mars.
*/

/*@ predicate isPossibleStartingDate(integer n, integer out1, integer out2) =
    \exists integer weekDay, weekendDay, startingDay;
    1 <= startingDay <= 7 &&
    0 <= weekDay <= n &&
    0 <= weekendDay <= n &&
    n == weekendDay + weekDay &&
    // Depending on the starting day we have different number of week days
    // For each tuple of 7 we have 5 week days and 2 weekend days
    // Of the remaining days (0 through 6) we have 0 to 5 week days and 0 to 2 weekend days
    startingDay == 1 ==> weekDay == 5 * (n / 7) + \min(5, n % 7) && weekendDay == 5 * (n / 7) + \min(2, n % 7) &&
    startingDay == 2 ==> weekDay == 5 * (n / 7) + \min(4, n % 7) && weekendDay == 5 * (n / 7) + \min(2, n % 7 + 1) &&
    startingDay == 3 ==> weekDay == 5 * (n / 7) + \min(3, n % 7) && weekendDay == 5 * (n / 7) + \min(2, n % 7 + 2) &&
    startingDay == 4 ==> weekDay == 5 * (n / 7) + \min(2, n % 7) && weekendDay == 5 * (n / 7) + \min(2, n % 7 + 3) &&
    startingDay == 5 ==> weekDay == 5 * (n / 7) + \min(1, n % 7) && weekendDay == 5 * (n / 7) + \min(2, n % 7 + 4) &&
    startingDay == 6 ==> weekDay == 5 * (n / 7) + \min(0, n % 7) && weekendDay == 5 * (n / 7) + \min(2, n % 7 + 5) &&
    startingDay == 7 ==> weekDay == 5 * (n / 7) + \min(0, n % 7 + 1) && weekendDay == 5 * (n / 7) + \min(2, n % 7 + 6);
*/

/*@
    requires \valid(out1) && \valid(out2) && \separated(out1, out2);
    requires 1 <= n <= 1000000;
    assigns *out1, *out2;
    ensures *out1 == (n / 7) * 2 + \max(0, n % 7 - 5);
    ensures *out2 == (n / 7) * 2 + \min(2, n % 7);
*/
void calculateMartianDaysOffRange(int n, int *out1, int *out2)
{
    *out1 = (n / 7) * 2 + (n % 7 - 5 > 0 ? n % 7 - 5 : 0);
    *out2 = (n / 7) * 2 + (n % 7 < 2 ? n % 7 : 2);
}
