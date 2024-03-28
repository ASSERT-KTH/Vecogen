/*@
    requires \valid(out);
    requires 1 <= n <= 1000000000;
    assigns *out;
    ensures *out == (2 * n + 1) / 3;
*/
void calculateMaximumPresentGivingTimes(int n, int *out);
