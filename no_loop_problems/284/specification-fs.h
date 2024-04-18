/*@
    requires \valid(out);
    requires 1 <= l1 <= 1000000000000000000;
    requires 1 <= r1 <= 1000000000000000000;
    requires 1 <= l2 <= 1000000000000000000;
    requires 1 <= r2 <= 1000000000000000000;
    requires 1 <= k <= 1000000000000000000;
    requires l1 <= r1 <= r2;
    requires l1 <= l2 <= r2;
    assigns *out;
    behavior r1_smaller_l2_or_l1_larger_r2:
        assumes r1 < l2 || l1 > r2;
        ensures *out == 0;
    behavior remainder:
        assumes !(r1 < l2 || l1 > r2);
        ensures *out == \min(r1, r2) - \max(l1, l2) + (\max(l1, l2) <= k <= \min(r1, r2) ? 0 : 1);
    complete behaviors;
    disjoint behaviors;
    */
void calculateSharedTime(long l1, long r1, long l2, long r2, long k, long *out);