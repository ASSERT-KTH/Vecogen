/*@
    requires \valid(out);
    requires 1 <= n <= 100;
    requires 1 <= a <= n;
    requires -100 <= b <= 100;
    assigns *out;
    ensures 1 <= *out <= n;
    behavior a_plus_b_mod_n_equals_0:
        assumes ((a + ((b % n) + n) % n) % n) == 0;
        ensures *out == n;
    behavior a_plus_b_mod_n_not_equals_0:
        assumes ((a + ((b % n) + n) % n) % n) != 0;
        ensures *out == (a + ((b % n) + n) % n) % n;
    complete behaviors;
    disjoint behaviors;
*/
void findVasyasFinalEntrance(int n, int a, int b, int *out);
