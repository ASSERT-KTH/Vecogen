/*@
    requires \valid(out_1) && \valid(out_2) && \separated(out_1, out_2);
    requires 1 <= n <= 10000;
    assigns *out_1, *out_2;
    behavior feet_rounded_up:
        assumes n % 3 == 2;
        ensures *out_1 == ((n / 3) + 1) / 12;
        ensures *out_2 == ((n / 3) + 1) % 12;
    behavior feet_rounded_down:
        assumes n % 3 != 2;
        ensures *out_1 == (n / 3) / 12;
        ensures *out_2 == (n / 3) % 12;
    complete behaviors;
    disjoint behaviors;
*/
void convertCentimetersToFeetAndInches(int n, int *out_1, int *out_2);