/*@
    requires \valid(out);
    requires 1 <= n <= 100000;
    requires 1 <= k <= 100000;
    assigns *out;
    behavior k_larger_or_equal_n_divided_by_two:
        assumes k >= n / 2;
        ensures *out == (n * (n - 1)) / 2;
    behavior k_smaller_than_n_divided_by_two:
        assumes k < n / 2;
        ensures *out ==  k * (2 * n - 1 - 2 * k);
    complete behaviors;
    disjoint behaviors;
*/
void calculateMaximumMessiness(long n, int k, long *out);