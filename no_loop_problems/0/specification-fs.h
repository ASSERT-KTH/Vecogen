/*@ predicate IsValidConfiguration(integer a, integer b, integer naa, integer nab, integer nbb, integer a_rem, integer b_rem) =
    0 <= naa <= a / 2 &&
    0 <= nab <= (a + b) / 2 &&
    0 <= nbb <= b / 2 &&
    0 <= a_rem <= 1 &&
    0 <= b_rem <= 1 &&
    (naa == 0 || nbb == 0) &&
    2 * naa + nab + a_rem == a &&
    2 * nbb + nab + b_rem == b &&
    a_rem + b_rem <= 1;
*/

// Predicate that looks if the solution is valid
/*@ predicate IsPossibleConfiguration(integer a, integer b, integer result_1, integer result_2) =
    \exists integer naa, nab, nbb, a_rem, b_rem;
    IsValidConfiguration(a, b, naa, nab, nbb, a_rem, b_rem) ==>
    result_1 == nab && result_2 == naa + nbb;
*/

// Predicate that shows that there does not exist a solution with a higher value
/*@ predicate ExistsBiggerSolution(integer a, integer b, integer result_1, integer result_2) =
    \exists integer naa, nab, nbb, a_rem, b_rem;
    IsValidConfiguration(a, b, naa, nab, nbb, a_rem, b_rem) &&
    nab > result_1 && result_2 == naa + nbb;
*/

/*@
    requires \valid(out_1) && \valid(out_2) && \separated(out_1, out_2);
    requires 1 <= a <= 100;
    requires 1 <= b <= 100;
    assigns *out_1, *out_2;
    ensures IsPossibleConfiguration(a, b, *out_1, *out_2);
    ensures !ExistsBiggerSolution(a, b, *out_1, *out_2);
*/
void calculateHipsterSockDays(int a, int b, int *out_1, int *out_2);