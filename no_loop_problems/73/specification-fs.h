/*@
    requires \valid(out);
    requires mode == 0 || mode == 1;
    requires (mode == 0 ==> x >= 1 && x <= 7) && (mode == 1 ==> x >= 1 && x <= 31);
    assigns *out;
    behavior week:
        assumes mode == 0;
        ensures *out == 52 + ((x == 5 || x == 6) ? 1 : 0);
    behavior month:
        assumes mode == 1;
        ensures *out == 12 - ((x > 29) ? 1 : 0) - 4 * ((x > 30) ? 1 : 0);
    complete behaviors;
    disjoint behaviors;

*/
void calculateCandiesSaved(int x, int mode, int *out);