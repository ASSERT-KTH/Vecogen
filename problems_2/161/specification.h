/*  A. Round House
    Vasya lives in a round building, whose entrances are numbered sequentially by integers from 1 to n . Entrance n and entrance 1 are adjacent. Today Vasya got bored and decided to take a walk in the yard. Vasya lives in entrance a and he decided that during his walk he will move around the house b entrances in the direction of increasing numbers (in this order entrance n should be followed by entrance 1 ). The negative value of b corresponds to moving | b | entrances in the order of decreasing numbers (in this order entrance 1 is followed by entrance n ). If b = 0 , then Vasya prefers to walk beside his entrance. Illustration for n = 6 , a = 2 , b = - 5 . Help Vasya to determine the number of the entrance, near which he will be at the end of his walk.
*/

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
*/
void problem(int n, int a, int b, int *out);
