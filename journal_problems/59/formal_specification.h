/*@
requires 1 <= n <= 1000;
    requires 1 <= k <= 1000;
    requires 1 <= l <= 1000;
    requires 1 <= c <= 1000;
    requires 1 <= d <= 1000;
    requires 1 <= p <= 1000;
    requires 1 <= nl <= 1000;
    requires 1 <= np <= 1000;
    assigns \nothing;
    ensures \result >= 0;
    ensures limes_are_enough: c * d >= \result * n;
    ensures drinks_are_enough: k * l >= \result * n * nl;
    ensures salts_are_enough: p >= \result * n * np;
    ensures largest_solution: (\forall integer x; x > \result ==> c * d < x * n || k * l < x * n * nl || p < x * n * np);
*/

