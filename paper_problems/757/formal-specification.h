/*@ predicate validSolution(integer n, integer k, integer l, integer c, integer d, integer p, integer nl, integer np, integer out) =
    c * d >= out * n &&
    k * l >= out * n * nl &&
    p >= out * n * np;
*/

/*@ predicate existLargerSolution(integer n, integer k, integer l, integer c, integer d, integer p, integer nl, integer np, integer out) =
    \exists integer x;
    c * d >= x * n &&
    k * l >= x * n * nl &&
    p >= x * n * np &&
    x > out;
*/

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
    ensures validSolution(n, k, l, c, d, p, nl, np, *out);
    ensures !existLargerSolution(n, k, l, c, d, p, nl, np, *out);
*/