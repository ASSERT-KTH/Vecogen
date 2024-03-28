/*@
    requires \valid(out);
    requires  1 <= n <= 50;
    requires  1 <= k <= 250;
    requires 3 * n <= k <= 5 * n ;
    assigns *out;
    ensures *out == \max(0, 3 * n- k);
*/
void calculateMinimumExamsToResitForGivenSum(int n, int k, int *out);