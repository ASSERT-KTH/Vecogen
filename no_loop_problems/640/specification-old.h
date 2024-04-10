/*
    Petr stands in line of n people, but he doesn't know exactly which position he occupies. He can say that there are no less than a people standing in front of him and no more than b people standing behind him. Find the number of different positions Petr can occupy.
*/

/*@
    requires \valid(out);
    requires 0 <= n <= 100;
    requires 0 <= a < n;
    requires 0 <= b < n;
    assigns *out;
    behavior a_plus_b_less_than_n:
        assumes a + b < n;
        ensures *out == b + 1;
    behavior a_plus_b_greater_than_n:
        assumes a + b >= n;
        ensures *out == n - a;
    complete behaviors;
    disjoint behaviors;
*/
void calculatePossiblePositionsForPetr(int n, int a, int b, int *out);