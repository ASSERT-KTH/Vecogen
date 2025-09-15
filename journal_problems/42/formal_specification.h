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

