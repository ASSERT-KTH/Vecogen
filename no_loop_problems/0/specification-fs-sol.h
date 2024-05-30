/*@
    requires \valid(out1) && \valid(out2) && \separated(out1, out2);
    requires 1 <= a <= 100;
    requires 1 <= b <= 100;
    assigns *out1, *out2;
    behavior has_more_red:
        assumes a > b;
        ensures *out1 == b && *out2 == (a - b) / 2;
    behavior has_more_blue:
        assumes b > a;
        ensures *out1 == a && *out2 == (b - a) / 2;
    behavior equal_socks:
        assumes a == b;
        ensures *out1 == a && *out2 == 0;
    complete behaviors;
    disjoint behaviors;
*/
void calculateHipsterSockDays(int a, int b, int *out1, int *out2);