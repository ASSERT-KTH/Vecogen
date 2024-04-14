/*
    Little Artem got n stones on his birthday and now wants to give some of them to Masha. He knows that Masha cares more about the fact of receiving the present, rather than the value of that present, so he wants to give her stones as many times as possible. However, Masha remembers the last present she received, so Artem can't give her the same number of stones twice in a row. For example, he can give her 3 stones, then 1 stone, then again 3 stones, but he can't give her 3 stones and then again 3 stones right after that. How many times can Artem give presents to Masha?
*/

/*@ predicate isValidSolution(int n, int *out) =
    \exists integer  n_1, n_2, n_geq3;
    0 <= n_1 <= n &&
    0 <= n_2 <= n &&
    3 <= n_geq3 <= n &&
    n == n_1 + 2 * n_2 + n_geq3 &&
    n == *out;
*/

/*@ predicate existsBiggerSolution(int n, int *out) =
    \exists integer  n_1, n_2, n_geq3;
    0 <= n_1 <= n &&
    0 <= n_2 <= n &&
    0 <= n_geq3 <= n &&
    n == n_1 + 2 * n_2 + 3 * n_geq3 &&
    n_1 + n_2 + n_geq3 > *out;
*/

/*@
    requires \valid(out);
    requires 1 <= n <= 1000000000;
    assigns *out;
*/
void calculateMaximumPresentGivingTimes(int n, int *out)
{
    *out = (2 * n + 1) / 3;
}
