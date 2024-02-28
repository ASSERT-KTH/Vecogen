/*  The New Year: Meeting Friends
    There are three friend living on the straight line Ox in Lineland. The first friend lives at the point x 1 , the second friend lives at the point x 2 , and the third friend lives at the point x 3 . They plan to celebrate the New Year together, so they need to meet at one point. What is the minimum total distance they have to travel in order to meet at some point and celebrate the New Year? It's guaranteed that the optimal answer is always integer.
*/

/*@ predicate abs_value(int x, int result) =
      (x >= 0 ==> result == x) &&
      (x < 0 ==> result == -x);
  @*/

/*@
    requires \valid(out);
    requires 1 <= x1 <= 100;
    requires 1 <= x2 <= 100;
    requires 1 <= x3 <= 100;
    assigns *out;
    behavior at_x2:
        assumes (x1 < x2 && x1 > x3) || (x1 < x3 && x1 > x2);
        ensures *out == abs_value(x1 - x2) + abs_value(x1 - x3);
    behavior at_x1:
        assumes (x2 < x1 && x2 > x3) || (x2 < x3 && x2 > x1);
        ensures *out == abs_value(x2 - x1) + abs_value(x2 - x3);
    behavior at_x3:
        assumes (x3 < x1 && x3 > x2) || (x3 < x2 && x3 > x1);
        ensures *out == abs_value(x3 - x1) + abs_value(x3 - x2);
    */

void problem(long x1, long x2, long x3, long *out)
{
    if ((x1 < x2 && x1 > x3) || (x1 < x3 && x1 > x1))
    {
        *out = abs(x1 - x2) + abs(x1 - x3);
    }
    else if ((x2 < x1 && x2 > x3) || (x2 < x3 && x2 > x1))
    {
        *out = abs(x2 - x1) + abs(x2 - x3);
    }
    else if ((x3 < x1 && x3 > x2) || (x3 < x2 && x3 > x1))
    {
        *out = abs(x3 - x1) + abs(x3 - x2);
    }
}
