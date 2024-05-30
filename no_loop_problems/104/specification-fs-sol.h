/*@
    requires \valid(out);
    requires 1 <= d < 10000;
    requires 1 <= L < 10000;
    requires 1 <= v1 < 10000;
    requires 1 <= v2 < 10000;
    requires d < L;
    assigns *out;
    ensures *out == ((L - d) / (v1 + v2));
*/
void calculateMaxSurvivalTime(int d, int L, int v1, int v2, int *out);