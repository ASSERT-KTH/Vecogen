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

