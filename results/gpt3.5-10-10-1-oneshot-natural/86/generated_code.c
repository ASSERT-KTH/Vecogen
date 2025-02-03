/*
    An elephant decided to visit his friend. It turned out that the elephant's house is located at point 0 and his friend's house is located at point x (x > 0) of the coordinate line. In one step the elephant can move 1, 2, 3, 4 or 5 positions forward. Determine, what is the minimum number of steps he need to make in order to get to his friend's house.

    Input
    The first input contains an integer x (1 ≤ x ≤ 1000000) — The coordinate of the friend's house.

    Output
    The minimum number of steps that elephant needs to make to get from point 0 to point x.
*/
/*@ predicate IsPossibleConfiguration(integer x, integer result) =
    \exists integer n1, n2, n3, n4, n5;
    n1 >= 0 &&
    n2 >= 0 &&
    n3 >= 0 &&
    n4 >= 0 &&
    n5 >= 0 &&
    x == n1 + 2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 &&
    result == n1 + n2 + n3 + n4 + n5;
*/

/*@ predicate ExistsSmallerSolution(integer x, integer result) =
    \exists integer n1, n2, n3, n4, n5;
    n1 >= 0 &&
    n2 >= 0 &&
    n3 >= 0 &&
    n4 >= 0 &&
    n5 >= 0 &&
    x == n1 + 2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 &&
    n1 + n2 + n3 + n4 + n5 < result;
*/

/*@
    requires \valid(out);
    requires 1 <=  x <= 1000000;
    assigns *out;
    ensures IsPossibleConfiguration(x, *out);
    ensures !ExistsSmallerSolution(x, *out);
*/
void calculateMinimumElephantSteps(int x, int *out) {
    int steps = (x + 4) / 5; // Ceiling division to get the minimum steps needed
    *out = steps;
}
