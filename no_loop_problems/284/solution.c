/*
    Today an outstanding event is going to happen in the forest — hedgehog Filya will come to his old fried Sonya! Sonya is an owl and she sleeps during the day and stay awake from minute l1 to minute r1 inclusive. Also, during the minute k she prinks and is unavailable for Filya. Filya works a lot and he plans to visit Sonya from minute l2 to minute r2 inclusive. Calculate the number of minutes they will be able to spend together.

    Input
    The only line of the input contains integers l1 , r1 , l2 , r2 and k (1 ≤ l1 , r1 , l2 , r2 , k ≤ 10^18 , l 1 ≤ r 1 , l 2 ≤ r 2 ), providing the segments of time for Sonya and Filya and the moment of time when Sonya prinks.

    Output
    Print one integer — the number of minutes Sonya and Filya will be able to spend together.
*/

/*@ predicate isValidSolution(long l1, long r1, long l2, long r2, long k, long out) =
    \max(0, \min(r1, r2) - \max(l1, l2) + (\max(l1, l2) <= k <= \min(r1, r2) ? 0 : 1)) == out;
*/

/*@
    requires \valid(out);
    requires 1 <= l1 <= 1000000000000000000;
    requires 1 <= r1 <= 1000000000000000000;
    requires 1 <= l2 <= 1000000000000000000;
    requires 1 <= r2 <= 1000000000000000000;
    requires 1 <= k <= 1000000000000000000;
    requires l1 <= r1 <= r2;
    requires l1 <= l2 <= r2;
    assigns *out;
    ensures isValidSolution(l1, r1, l2, r2, k, *out);
    */
void calculateSharedTime(long l1, long r1, long l2, long r2, long k, long *out)
{
    long long int t, l, r;
    if (l1 > l2)
        l = l1;
    else
        l = l2;
    if (r1 < r2)
        r = r1;
    else
        r = r2;
    if (k >= l && k <= r)
        t = r - l;
    else
        t = r - l + 1;
    if (t < 0)
        t = 0;
    *out = t;
}
