/*@
    requires \valid(out);
    requires 1 <= a <= n <= 100000;
    requires n % 2 == 0;
    assigns *out;
    behavior a_is_even:
        assumes a % 2 == 0;
        ensures *out == 1 + (n - a) / 2;
    behavior a_is_odd:
        assumes a % 2 == 1;
        ensures *out == (a + 1) / 2 ;
    complete behaviors;
    disjoint behaviors;
*/
void calculateMinimumTimeToHouse(int n, int a, int *out);