/*
    This winter is so cold in Nvodsk! A group of n friends decided to buy k bottles of a soft drink called "Take-It-Light" to warm up a bit. Each bottle has l milliliters of the drink. Also they bought c limes and cut each of them into d slices. After that they found p grams of salt. To make a toast, each friend needs nl milliliters of the drink, a slice of lime and np grams of salt. The friends want to make as many toasts as they can, provided they all drink the same amount. How many toasts can each friend make?
*/

/*@ predicate validSolution(integer n, integer k, integer l, integer c, integer d, integer p, integer nl, integer np, integer out) =
    c * d >= out * n &&
    k * l >= out * n * nl &&
    p >= out * n * np;
*/

/*@ predicate existLargerSolution(integer n, integer k, integer l, integer c, integer d, integer p, integer nl, integer np, integer out) =
    \exists integer x;
    c * d >= x * n &&
    k * l >= x * n * nl &&
    p >= x * n * np &&
    x > out;
*/

/*@
    requires \valid(out);
    requires 1 <= n <= 1000;
    requires 1 <= k <= 1000;
    requires 1 <= l <= 1000;
    requires 1 <= c <= 1000;
    requires 1 <= d <= 1000;
    requires 1 <= p <= 1000;
    requires 1 <= nl <= 1000;
    requires 1 <= np <= 1000;
    assigns *out;
    ensures validSolution(n, k, l, c, d, p, nl, np, *out);
    ensures !existLargerSolution(n, k, l, c, d, p, nl, np, *out);
*/
void calculateMaximumToastsPerFriend(int n, int k, int l, int c, int d, int p, int nl, int np, int *out)
{
    int x = ((k * l) / nl);
    int y = c * d;
    int z = p / np;
    int min_value;
    if (x <= y && x <= z)
    {
        min_value = x;
    }
    else if (y <= x && y <= z)
    {
        min_value = y;
    }
    else
    {
        min_value = z;
    }

    *out = min_value / n;
}
