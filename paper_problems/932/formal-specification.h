/*@ predicate IsPossibleConfiguration(integer n, integer k, integer result) =
    \exists integer n2, n3, n4, n5;
    0 <= n2 <= n &&
    0 <= n3 <= n &&
    0 <= n4 <= n &&
    0 <= n5 <= n &&
    2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 == k &&
    n2 + n3 + n4 + n5 == n &&
    result == n2;
*/

/*@ predicate ExistsSmallerAmountOfResits(integer n, integer k, integer result) =
    \exists integer n2, n3, n4, n5;
    0 <= n2 <= n &&
    0 <= n3 <= n &&
    0 <= n4 <= n &&
    0 <= n5 <= n &&
    2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 == k &&
    n2 + n3 + n4 + n5 == n &&
    n2 < result;
*/

/*@ predicate ExistsPossibleConfiguration(integer n, integer k) =
    \exists integer n2, n3, n4, n5;
    0 <= n2 <= n &&
    0 <= n3 <= n &&
    0 <= n4 <= n &&
    0 <= n5 <= n &&
    2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 == k &&
    n2 + n3 + n4 + n5 == n;
*/

/*@
    requires \valid(out);
    requires  1 <= n <= 50;
    requires  1 <= k <= 250;
    requires ExistsPossibleConfiguration(n, k);
    assigns *out;
    ensures IsPossibleConfiguration(n, k, *out);
    ensures !ExistsSmallerAmountOfResits(n, k, *out);
*/