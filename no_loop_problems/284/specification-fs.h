/*@ predicate isValidSolution(long l1, long r1, long l2, long r2, long k, long out) =
    \max(0, \min(r1, r2) - \max(l1, l2) + (\max(l1, l2) <= k <= \min(r1, r2) ? 0 : 1)) == out;
*/

/*@
    requires \valid(out);
    requires 1 <= l1 <= 1000000000000000000;
    requires 1 <= r1 <= 1000000000000000000;
    requires 1 <= l2 <= 1000000000000000000;
    requires 1 <= r2 <= 1000000000000000000;
    requires 1 <= k <= 1000000000000000000;
    requires r1 <= r2;
    requires l2 <= r2;
    assigns *out;
    ensures isValidSolution(l1, r1, l2, r2, k, *out);
*/
void calculateSharedTime(long l1, long r1, long l2, long r2, long k, long *out);