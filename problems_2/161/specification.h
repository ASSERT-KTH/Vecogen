/*  A. Round House
    Vasya lives in a round building, whose entrances are numbered sequentially by integers from 1 to n . Entrance n and entrance 1 are adjacent. Today Vasya got bored and decided to take a walk in the yard. Vasya lives in entrance a and he decided that during his walk he will move around the house b entrances in the direction of increasing numbers (in this order entrance n should be followed by entrance 1 ). The negative value of b corresponds to moving | b | entrances in the order of decreasing numbers (in this order entrance 1 is followed by entrance n ). If b = 0 , then Vasya prefers to walk beside his entrance. Illustration for n = 6 , a = 2 , b = - 5 . Help Vasya to determine the number of the entrance, near which he will be at the end of his walk.
*/

/*@
    requires 1 <= n <= 100;
    requires 1 <= a <= n;
    requires -100 <= b <= 100;
    assigns \nothing;
    behavior b_greater_than_0:
        assumes b > 0;
        ensures \result == (a + b - 1) % n + 1;
    behavior b_less_than_0:
        assumes b < 0;
        ensures \result == (a + n + b - 1) % n + 1;
*/
int problem(int n, int a, int b);
