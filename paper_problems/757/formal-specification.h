/*@
    requires \valid(out);
    requires 1 <= n <= 1000;
    requires 1 <= k <= 1000;
    requires 1 <= l <= 1000;
    requires 1 <= c <= 1000;
    requires 1 <= d <= 1000;
    requires 1 <= p <= 1000;
    requires 1 <= nl <= 1000;
    requires 1 <= np <= 1000;
    assigns *out;
    ensures *out >= 0;
    ensures limes_are_enough: c * d >= *out * n;
    ensures drinks_are_enough: k * l >= *out * n * nl;
    ensures salts_are_enough: p >= *out * n * np;
    ensures largest_solution: (\forall integer x; x > *out ==> c * d < x * n || k * l < x * n * nl || p < x * n * np);
*/