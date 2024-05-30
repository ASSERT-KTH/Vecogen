/*@
    requires \valid(out1) && \valid(out2) && \separated(out1, out2);
    requires 1 <= n <= 1000000;
    assigns *out1, *out2;
    ensures *out1 == (n / 7) * 2 + \max(0, n % 7 - 5);
    ensures *out2 == (n / 7) * 2 + \min(2, n % 7);
*/
void calculateMartianDaysOffRange(int n, int *out1, int *out2);