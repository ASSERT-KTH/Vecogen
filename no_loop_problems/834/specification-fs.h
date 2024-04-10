/*@ predicate IsValidSolution(integer n, integer x, integer y, integer result) =
    x >= 0 &&
    ((real)(result + x) / n) >= ((real) y / 100);
*/

/*@ predicate existsSmallerSolution(integer n, integer x, integer y, integer result) =
    \exists integer z;
    z >= 0 &&
    ((real)(z + x) /  n) >= ((real) (y) / 100) &&
    z < result;
*/

/*@
    requires \valid(out);
    requires 1 <= x <= 10000;
    requires 1 <= y <= 10000;
    requires 1 <= n <= 10000;
    requires  x <= n;
    assigns *out;
    ensures IsValidSolution(n, x, y, *out);
    ensures !existsSmallerSolution(n, x, y, *out);
*/
void calculateMinimumClonesForDemonstrationPercentage(int n, int x, int y, int *out);