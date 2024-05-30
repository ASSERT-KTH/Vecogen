/*@
    requires \valid(out);
    requires 1 <= x <= 10000;
    requires 1 <= y <= 10000;
    requires 1 <= n <= 10000;
    requires  x <= n;
    assigns *out;
    behavior zero_clones:
        assumes (n * y + 99) / 100 - x <= 0;
        ensures *out == 0;
    behavior positive_clones:
        assumes (n * y + 99) / 100 - x > 0;
        ensures *out == (n * y + 99) / 100 - x;
    complete behaviors;
    disjoint behaviors;
*/
void calculateMinimumClonesForDemonstrationPercentage(int n, int x, int y, int *out);