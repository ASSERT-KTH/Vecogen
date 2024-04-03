/*@
    logic variable
    requires \valid(out_1) && \valid(out_2) && \separated(out_1, out_2);
    requires 1 <= a <= 100;
    requires 1 <= b <= 100;
    assigns *out_1, *out_2;
    ensures 2 * n_aa + n_ab = a;
    ensures 2 * n_bb + n_ab = b;

*/
void calculateHipsterSockDays(int a, int b, int *out_1, int *out_2);