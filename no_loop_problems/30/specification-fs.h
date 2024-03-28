/*@
    requires \valid(out);
    requires 1 <= l <= 1000;
    requires 1 <= p <= 500;
    requires 1 <= q <= 500;
    assigns *out;
    ensures \abs(((l / (p + q)) * p) - *out)/(\max(1, (l / (p + q)) * p)) <= 0.0001;
*/
void calculateSecondSpellCollisionDistance(int l, int p, int q, int *out);