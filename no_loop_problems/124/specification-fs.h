/*@
    requires \valid(out);
    requires 2 <= n <= 2 * 1000000000000000000;
    assigns *out;
    ensures *out % 100 == (long) \pow(5, 2) % 100;
*/
void calculateLastTwoDigitsOfPowerOfFive(long n, int *out);