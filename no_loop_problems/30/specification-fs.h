// Predicate that checks if the solution is within the margin
/*@ predicate IsWithinMargin(integer l, integer p, integer q, real out) =
    \exists integer margin, jury_solution;
    -0.0001 <= margin <= 0.0001 &&
    jury_solution == ((l * p) / (p + q)) &&
    \abs(jury_solution - out) / \max(1, jury_solution) <= margin;
*/

/*@
    requires \valid(out);
    requires 1 <= l <= 1000;
    requires 1 <= p <= 500;
    requires 1 <= q <= 500;
    assigns *out;
    ensures IsWithinMargin(l, p, q, *out);
*/
void calculateSecondSpellCollisionDistance(int l, int p, int q, int *out);