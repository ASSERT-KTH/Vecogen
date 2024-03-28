/*@
    requires \valid(out);
    requires 0 <= n <= 100;
    requires 0 <= a < n;
    requires 0 <= b < n;
    assigns *out;
    behavior a_plus_b_less_than_n:
        assumes a + b < n;
        ensures *out == b + 1;
    behavior a_plus_b_greater_than_n:
        assumes a + b >= n;
        ensures *out == n - a;
    complete behaviors;
    disjoint behaviors;
*/
void calculatePossiblePositionsForPetr(int n, int a, int b, int *out);