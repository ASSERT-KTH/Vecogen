/*@
    requires 1 <= n <= 1000;
    requires 1 <= k <= 1000;
    requires 1 <= l <= 1000;
    requires 1 <= c <= 1000;
    requires 1 <= d <= 1000;
    requires 1 <= p <= 1000;
    requires 1 <= nl <= 1000;
    requires 1 <= np <= 1000;
    behavior too_few_drinks:
        assumes
            (((k * l) / nl) < (c * d)) && (((k * l) / nl) < (p / np));
        ensures
            \result == (((k * l) / nl) / n);
    behavior too_few_slices:
        assumes
            ((c * d) < ((k * l) / nl)) && ((c * d) < (p / np));
        ensures
            \result == (c * d) / n;
    behavior too_few_salt:
        assumes
            ((p / np) < ((k * l) / nl)) && ((p / np) < (c * d));
        ensures
            \result == ((p / np) / n);
*/
int problem(int n, int k, int l, int c, int d, int p, int nl, int np)
{
    int x = ((k * l) / nl); // The number of drinks that can be used for the toast
    int y = c * d;          // The number of slices that can be used for the toast
    int z = p / np;         // The amount of salt that can be used for the toast
    // We have not enough drinks, so divide the drinks by the number of friends
    if (x < y && x < z)
        return (x / n); // Divide the amount of drinks by the number of friends
    // We have not enough slices, so divide the slices by the number of friends
    else if (y < x && y < z)
        return y / n; // Divide the amount of slices by the number of friends
    // We have not enough salt, so divide the salt by the number of friends
    else
        return z / n; // Divide the amount of salt by the number of friends
}
