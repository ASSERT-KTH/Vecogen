/*
    Petr stands in line of n people, but he doesn't know exactly which position he occupies. He can say that there are no less than a people standing in front of him and no more than b people standing behind him. Find the number of different positions Petr can occupy.
*/

// Predicate to see if the position is valid
/*@ predicate valid_position(integer n, integer a, integer b, integer position) =
    a <= position < n &&
    n - 1 - position <= b;
*/

/*@ logic integer valid_position_value(integer n, integer a, integer b, integer position) =
    valid_position(n, a, b, position) ? 1 : 0;
*/

/*@
  axiomatic axm
  {
    // Define the logical-function count() as returning the number of number of
    // possible positions for Petr
    logic integer count(integer n, integer a, integer b, integer min, integer max)
        reads n, a, b, max, min;

    axiom base:
        \forall integer n, a, b, max, min;
        min <= max &&
        min >= 0 &&
        max < n &&
        min == max ==> count(n, a, b, min, max) == valid_position_value(n, a, b, min);

    axiom recursion:
      \forall integer *a, x, n; n >= 1 ==>
      (count(a, n, x) == count(a, n - 1, x) + ((a[n - 1] == x) ? 1 : 0));
  }
 */

/*@
    requires \valid(out);
    requires 0 <= n <= 100;
    requires 0 <= a < n;
    requires 0 <= b < n;
    assigns *out;
    ensures  \sum(0, n-1, \lambda integer k; t(n, a, b, k));
*/
void calculatePossiblePositionsForPetr(int n, int a, int b, int *out)
{
    *out = n - a <= b ? n - a : b + 1;
}
