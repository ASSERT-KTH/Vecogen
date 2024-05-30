/*@
    requires \valid(out);
    requires 3 <= n <= 54321;
    assigns *out;
    ensures *out == (n-2)*(n-2);
*/
void calculateMinimumSquirrelJumps(int n, long *out);
