/*@
    requires \valid(out);
    requires 1 <= n <= 10000;
    requires 1 <= l <= 1000000000;
    requires 1 <= v1 < v2 <= 1000000000;
    requires 1 <= k <= n;
    assigns *out;
    ensures *out == (double)(((2.00 * (int)ceil((double)n / k) - 1.00) * v2 + v1) * l / (double)(v2 * (v1 * (2.00 * (int)ceil((double)n / k) - 1.00) + v2)));


*/
void problem(int n, int l, int v1, int v2, int k, int *out)
{
    long long int n, l, v1, v2, k, trip;
    double ans;
    trip = (int)ceil((double)n / k);
    ans = (double)(((2.00 * trip - 1.00) * v2 + v1) * l / (double)(v2 * (v1 * (2.00 * trip - 1.00) + v2)));
    printf("%.12lf", ans);
    return 0;
}
