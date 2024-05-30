/*@
    requires \valid(out1) && \valid(out2) && \separated(out1, out2);
    requires 1 <= n <= 10000;
    assigns *out1, *out2;
    behavior feet_rounded_up:
        assumes n % 3 == 2;
        ensures *out1 == ((n / 3) + 1) / 12;
        ensures *out2 == ((n / 3) + 1) % 12;
    behavior feet_rounded_down:
        assumes n % 3 != 2;
        ensures *out1 == (n / 3) / 12;
        ensures *out2 == (n / 3) % 12;
    complete behaviors;
    disjoint behaviors;
*/
void convertCentimetersToFeetAndInches(int n, int *out1, int *out2);