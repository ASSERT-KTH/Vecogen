/*  The number of positions
    Petr stands in line of n people, but he doesn't know exactly which position he occupies. He can say that there are no less than a people standing in front of him and no more than b people standing behind him. Find the number of different positions Petr can occupy.
*/

/*@
    requires 0 <= n <= 100;
    requires 0 <= a < n;
    requires 0 <= b < n;
    assigns \nothing;
    behavior a_plus_b_less_than_n:
        assumes a + b < n;
        ensures \result == b + 1;
    behavior a_plus_b_greater_than_n:
        assumes a + b >= n;
        ensures \result == n - a;
*/

int problem(int n, int a, int b);