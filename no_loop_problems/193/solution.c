/*
    On the planet Mars a year lasts exactly n days (there are no leap years on Mars). But Martians have the same weeks as earthlings — 5 work days and then 2 days off. Your task is to determine the minimum possible and the maximum possible number of days off per year on Mars.
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
