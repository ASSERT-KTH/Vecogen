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