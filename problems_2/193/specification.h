/*  A. Holidays
    On the planet Mars a year lasts exactly n days (there are no leap years on Mars). But Martians have the same weeks as earthlings — 5 work days and then 2 days off. Your task is to determine the minimum possible and the maximum possible number of days off per year on Mars.*/

/*@
    requires \valid(out1) && \valid(out2) && \separated(out1, out2);
    requires 1 <= n <= 1000000;
    assigns *out1, *out2;
    behavior remainder_0_after_mod:
        assumes n % 7 == 0;
        ensures *out1 == n / 7 * 2 && *out2 == n / 7 * 2;
    behavior remainder_1_after_mod:
        assumes n % 7 == 1;
        ensures *out1 == n / 7 * 2 && *out2 == n / 7 * 2 + 1;
    behavior remainder_6_after_mod:
        assumes n % 7 == 6;
        ensures *out1 == n / 7 * 2 + 1 && *out2 == n / 7 * 2 + 2;
    behavior remainder_rest_after_mod:
        assumes n % 7 > 1 && n % 7 < 6;
        ensures *out1 == n / 7 * 2 && *out2 == n / 7 * 2 + 2;
*/
void problem(int n, int *out1, int *out2);