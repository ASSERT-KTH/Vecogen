/*@
    requires \valid(out_1) && \valid(out_2) && \separated(out_1, out_2);
    requires 1 <= a <= 100;
    requires 1 <= b <= 100;
    assigns *out_1, *out_2;
    behavior has_more_red:
        assumes a > b;
        ensures *out_1 == b && *out_2 == (a - b) / 2;
    behavior has_more_blue:
        assumes b > a;
        ensures *out_1 == a && *out_2 == (b - a) / 2;
    behavior equal_socks:
        assumes a == b;
        ensures *out_1 == a && *out_2 == 0;
    complete behaviors;
    disjoint behaviors;
*/
void calculateHipsterSockDays(int a, int b, int *out_1, int *out_2);