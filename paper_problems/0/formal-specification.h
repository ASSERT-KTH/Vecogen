// Predicate that looks if the solution is valid
/*@ predicate IsPossibleConfiguration(integer a, integer b, integer result_1, integer result_2) =
    \exists integer naa, nab, nbb, a_rem, b_rem;
    0 <= naa <= a / 2 &&
    0 <= nab <= (a + b) / 2 &&
    0 <= nbb <= b / 2 &&
    0 <= a_rem <= 1 &&
    0 <= b_rem <= 1 &&
    2 * naa + nab + a_rem == a &&
    2 * nbb + nab + b_rem == b &&
    a_rem + b_rem <= 1 &&
    result_1 == nab && result_2 == naa + nbb;
*/

// Predicate that shows that there does not exist a solution with a higher value
/*@ predicate ExistsBiggerSolution(integer a, integer b, integer result_1, integer result_2) =
    \exists integer naa, nab, nbb, a_rem, b_rem;
    0 <= naa <= a / 2 &&
    0 <= nab <= (a + b) / 2 &&
    0 <= nbb <= b / 2 &&
    0 <= a_rem <= 1 &&
    0 <= b_rem <= 1 &&
    2 * naa + nab + a_rem == a &&
    2 * nbb + nab + b_rem == b &&
    nab > result_1 && result_2 == naa + nbb;
*/

/*@
    requires \valid(out1) && \valid(out2) && \separated(out1, out2);
    requires 1 <= a <= 100;
    requires 1 <= b <= 100;
    assigns *out1, *out2;
    ensures IsPossibleConfiguration(a, b, *out1, *out2);
    ensures !ExistsBiggerSolution(a, b, *out1, *out2);
*/