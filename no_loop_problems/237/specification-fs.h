/*@
    requires \valid(out);
    requires 1 <= N <= 1000000000;
    assigns *out;
    ensures *out == ((N + 1) / 2);
*/
void calculateMinimumBrainsForStrategy(int N, int *out);
