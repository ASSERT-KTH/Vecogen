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
    behavior too_few_drinks:
        assumes
            (((k * l) / nl) < (c * d)) && (((k * l) / nl) < (p / np));
        ensures
            *out == (((k * l) / nl) / n);
    behavior too_few_slices:
        assumes
            ((c * d) < ((k * l) / nl)) && ((c * d) < (p / np));
        ensures
            *out == (c * d) / n;
    behavior too_few_salt:
        assumes
            ((p / np) < ((k * l) / nl)) && ((p / np) < (c * d));
        ensures
            *out == ((p / np) / n);
*/
void problem(int n, int k, int l, int c, int d, int p, int nl, int np, int *out)
{
    int x = ((k * l) / nl);
    int y = c * d;
    int z = p / np;
    // We have not enough drinks, so divide the drinks by the number of friends
    if (x < y && x < z)
        *out = (x / n);
    // We have not enough slices, so divide the slices by the number of friends
    else if (y < x && y < z)
        *out = y / n;
    // We have not enough salt, so divide the salt by the number of friends
    else
        *out = z / n;
}
