/*Vasya lives in a round building, whose entrances are numbered sequentially by integers from 1 to n . Entrance n and entrance 1 are adjacent. Today Vasya got bored and decided to take a walk in the yard. Vasya lives in entrance a and he decided that during his walk he will move around the house b entrances in the direction of increasing numbers (in this order entrance n should be followed by entrance 1 ). The negative value of b corresponds to moving | b | entrances in the order of decreasing numbers (in this order entrance 1 is followed by entrance n ). If b = 0 , then Vasya prefers to walk beside his entrance. Illustration for n = 6 , a = 2 , b = - 5 . Help Vasya to determine the number of the entrance, near which he will be at the end of his walk.

    Input
    The input contains three integers n, a and b (1 <= n <= 100, 1 <= a <= n , - 100 <= b <= 100) — the number of entrances at Vasya's place, the number of his entrance and the length of his walk, respectively.

    Output
    Output a single integer k (1 <= k <= n) — the number of the entrance where Vasya will be at the end of his walk.
*/


/*Take the largest possible steps for verification performance
*/

/*@
logic integer round_walk(integer n, integer curr, integer b) =
    (b == 0) ? curr :
    (b >= n) ? round_walk(n, ((curr - 1 + n) % n) + 1, b % n) :
    round_walk(n, ((curr - 1 + b) % n) + 1, 0);
*/

/*@
requires 1 <= n <= 100;
  requires 1 <= a <= n;
  requires -100 <= b <= 100;
  assigns \nothing;
  ensures round_walk(n, a, ((b % n) + n) % n) ==  \result;
*/

int findVasyasFinalEntrance(int n, int a, int b) {
    int result = (a + b % n) % n;
    if (result <= 0) {
        result += n;
    }
    return result;
}
