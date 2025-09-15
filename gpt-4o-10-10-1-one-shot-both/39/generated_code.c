/*One day the Codeforces round author sat exams. He had n exams and he needed to get an integer from 2 to 5 for each exam. He will have to re-sit each failed exam, i.e. the exam that gets mark 2 . The author would need to spend too much time and effort to make the sum of his marks strictly more than k . That could have spoilt the Codeforces round. On the other hand, if the sum of his marks is strictly less than k , the author's mum won't be pleased at all. The Codeforces authors are very smart and they always get the mark they choose themselves. Also, the Codeforces authors just hate re-sitting exams. Help the author and find the minimum number of exams he will have to re-sit if he passes the exams in the way that makes the sum of marks for all n exams equal exactly k .

    Input
    The input contains space-separated integers n and k (1 ≤ n ≤ 50, 1 ≤ k ≤ 250) — the number of exams and the required sum of marks. It is guaranteed that there exists a way to pass n exams in the way that makes the sum of marks equal exactly k .

    Output
    Output the single number — the minimum number of exams that the author will get a 2 for, considering that the sum of marks for all exams must equal k.
*/

/*@
predicate IsPossibleConfiguration(integer n, integer k, integer result) =
    \exists integer n2, n3, n4, n5;
    0 <= n2 <= n &&
    0 <= n3 <= n &&
    0 <= n4 <= n &&
    0 <= n5 <= n &&
    2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 == k &&
    n2 + n3 + n4 + n5 == n &&
    result == n2;
*/

/*@
predicate ExistsSmallerAmountOfResits(integer n, integer k, integer result) =
    \exists integer n2, n3, n4, n5;
    0 <= n2 <= n &&
    0 <= n3 <= n &&
    0 <= n4 <= n &&
    0 <= n5 <= n &&
    2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 == k &&
    n2 + n3 + n4 + n5 == n &&
    n2 < result;
*/

/*@
predicate ExistsPossibleConfiguration(integer n, integer k) =
    \exists integer n2, n3, n4, n5;
    0 <= n2 <= n &&
    0 <= n3 <= n &&
    0 <= n4 <= n &&
    0 <= n5 <= n &&
    2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 == k &&
    n2 + n3 + n4 + n5 == n;
*/

/*@
requires  1 <= n <= 50;
    requires  1 <= k <= 250;
    requires ExistsPossibleConfiguration(n, k);
    assigns \nothing;
    ensures IsPossibleConfiguration(n, k, \result);
    ensures !ExistsSmallerAmountOfResits(n, k, \result);
*/

int calculateMinimumExamsToResitForGivenSum(int n, int k) {
    if (n == 1) return k == 2 ? 1 : 0;

    int n5 = (k - 4 * n) / 1;
    if(n5 < 0) n5 = 0;

    int k_new = k - n5 * 5;
    int n_left = n - n5;
    int n4 = (k_new - 3 * n_left) / 1;
    if(n4 < 0) n4 = 0;

    k_new = k_new - n4 * 4;
    n_left = n_left - n4;
    int n3 = (k_new - 2 * n_left) / 1;
    if(n3 < 0) n3 = 0;

    k_new = k_new - n3 * 3;
    n_left = n_left - n3;
    int n2 = n_left;

    return n2;
}
