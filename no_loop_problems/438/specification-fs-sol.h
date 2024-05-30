/*@
    requires \valid(out);
    requires 1 <= n <= 1000000000;
    requires 1 <= m <= 1000000000;
    requires 1 <= a <= 1000000000;
    assigns *out;
    ensures *out == ((n+a-1)/a) * ((m+a-1)/a);
*/
void calculateMinimumFlagstonesNeeded(int n, int m, long a, long *out);