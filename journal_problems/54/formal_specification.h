/*@
predicate IsPossibleConfiguration(integer a, integer b, integer result_1, integer result_2) =
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

/*@
predicate ExistsBiggerSolution(integer a, integer b, integer result_1, integer result_2) =
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
requires 1 <= a <= 100;
    requires 1 <= b <= 100;
    assigns \nothing;
    ensures IsPossibleConfiguration(a, b, \result.different_days, \result.same_days);
    ensures !ExistsBiggerSolution(a, b, \result.different_days, \result.same_days);
*/

