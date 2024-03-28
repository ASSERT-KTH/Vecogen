/*@
    requires \valid(out);
    requires 2 <= n <= 2 * 1000000000000000000;
    assigns *out;
    ensures *out == 25;
*/
void calculateLastTwoDigitsOfPowerOfFive(long n, int *out);