/*
    There are three friend living on the straight line Ox in Lineland. The first friend lives at the point x1 , the second friend lives at the point x2 , and the third friend lives at the point x3 . They plan to celebrate the New Year together, so they need to meet at one point. What is the minimum total distance they have to travel in order to meet at some point and celebrate the New Year? It's guaranteed that the optimal answer is always integer.

    Input
    The input contains three distinct integers x 1 , x 2 and x 3 ( 1 ≤ x1 , x2 , x3 ≤ 100 ) — the coordinates of the houses of the first, the second and the third friends respectively.

    Output
    Output one integer — the minimum total distance the friends need to travel in order to meet together
*/
/*@ predicate IsValidSolution(int x1, int x2, int x3, int result) =
    \exists int point;
    0 <= point &&
    \abs(point - x1) + \abs(point - x2) + \abs(point - x3) == result;
*/

/*@ predicate ExistsSmallerSolution(int x1, int x2, int x3, int result) =
    \exists int smaller_solution;
    IsValidSolution(x1, x2, x3, smaller_solution) &&
    smaller_solution < result;
*/

/*@
    requires \valid(out);
    requires 1 <= x1 <= 100;
    requires 1 <= x2 <= 100;
    requires 1 <= x3 <= 100;
    requires \exists int result; IsValidSolution(x1, x2, x3, result);
    assigns *out;
    ensures IsValidSolution(x1, x2, x3, *out);
    ensures !ExistsSmallerSolution(x1, x2, x3, *out);
*/
void calculateOptimalMeetingPointDistance(int x1, int x2, int x3, int *out) {
    int distance1, distance2, distance3;

    // Sort the points using comparisons (since only three points)
    if (x1 > x2) {
        int temp = x1;
        x1 = x2;
        x2 = temp;
    }
    if (x2 > x3) {
        int temp = x2;
        x2 = x3;
        x3 = temp;
    }
    if (x1 > x2) {
        int temp = x1;
        x1 = x2;
        x2 = temp;
    }

    // After sorting the points, meeting at point x2 gives the minimal distance
    distance1 = x2 - x1;
    distance2 = x3 - x2;
    *out = distance1 + distance2;
}
