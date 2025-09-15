/*There are three friend living on the straight line Ox in Lineland. The first friend lives at the point x1 , the second friend lives at the point x2 , and the third friend lives at the point x3 . They plan to celebrate the New Year together, so they need to meet at one point. What is the minimum total distance they have to travel in order to meet at some point and celebrate the New Year? It's guaranteed that the optimal answer is always integer.

    Input
    The input contains three distinct integers x1 , x2 and x3 (1 <= x1 , x2 , x3 <= 100) — the coordinates of the houses of the first, the second and the third friends respectively.

    Output
    Output one integer — the minimum total distance the friends need to travel in order to meet together
*/

/*@
predicate IsValidSolution(int x1, int x2, int x3, int result) =
    \exists int point;
    0 <= point &&
    \abs(point - x1) + \abs(point - x2) + \abs(point - x3) == result;
*/

/*@
predicate ExistsSmallerSolution(int x1, int x2, int x3, int result) =
    \exists int smaller_solution;
    IsValidSolution(x1, x2, x3, smaller_solution) &&
    smaller_solution < result;
*/

/*@
requires 1 <= x1 <= 100;
    requires 1 <= x2 <= 100;
    requires 1 <= x3 <= 100;
    requires \exists int result; IsValidSolution(x1, x2, x3, result);
    assigns \nothing;
    ensures IsValidSolution(x1, x2, x3, \result);
    ensures !ExistsSmallerSolution(x1, x2, x3, \result);
*/

int calculateOptimalMeetingPointDistance(int x1, int x2, int x3) {
    int mid;
    if ((x1 <= x2 && x2 <= x3) || (x3 <= x2 && x2 <= x1)) {
        mid = x2;
    } else if ((x2 <= x1 && x1 <= x3) || (x3 <= x1 && x1 <= x2)) {
        mid = x1;
    } else {
        mid = x3;
    }
    return (mid - x1 < 0 ? -(mid - x1) : mid - x1) + (mid - x2 < 0 ? -(mid - x2) : mid - x2) + (mid - x3 < 0 ? -(mid - x3) : mid - x3);
}
