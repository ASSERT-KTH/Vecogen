/*
    There are three friend living on the straight line Ox in Lineland. The first friend lives at the point x1 , the second friend lives at the point x2 , and the third friend lives at the point x3 . They plan to celebrate the New Year together, so they need to meet at one point. What is the minimum total distance they have to travel in order to meet at some point and celebrate the New Year? It's guaranteed that the optimal answer is always integer.

    Input
    The input contains three distinct integers x 1 , x 2 and x 3 ( 1 ≤ x1 , x2 , x3 ≤ 100 ) — the coordinates of the houses of the first, the second and the third friends respectively.

    Output
    Output one integer — the minimum total distance the friends need to travel in order to meet together
*/

/*@
    requires \valid(out);
    requires 1 <= x1 <= 100;
    requires 1 <= x2 <= 100;
    requires 1 <= x3 <= 100;
    assigns *out;
    ensures *out == 2 * (\max(x1, \max(x2, x3)) - \min(x1, \min(x2, x3)));
    */
void calculateOptimalMeetingPointDistance(int x1, int x2, int x3, int *out);
