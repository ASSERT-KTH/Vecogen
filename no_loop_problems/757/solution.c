/*  Soft Drinking
    This winter is so cold in Nvodsk! A group of n friends decided to buy k bottles of a soft drink called "Take-It-Light" to warm up a bit. Each bottle has l milliliters of the drink. Also they bought c limes and cut each of them into d slices. After that they found p grams of salt. To make a toast, each friend needs nl milliliters of the drink, a slice of lime and np grams of salt. The friends want to make as many toasts as they can, provided they all drink the same amount. How many toasts can each friend make?*/

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
    ensures *out == \min((k * l) / nl, \min(c * d, p / np)) / n;
    ensures *out >= 0;
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
    else if (z < x && z < y)
        *out = z / n;
    // All are equal, so divide the drinks by the number of friends
    else if (x == y && x == z)
        *out = x / n;
    // Drinks and slices are equal, so divide the drinks by the number of friends
    else if (x == y && x < z)
        *out = x / n;
    // Drinks and salt are equal, so divide the drinks by the number of friends
    else if (x == z && x < y)
        *out = x / n;
    // Slices and salt are equal, so divide the slices by the number of friends
    else if (y == z && y < x)
        *out = y / n;
    // Drinks are less than slices and salt, so divide the drinks by the number of friends
    else if (x < y && x == z)
        *out = x / n;
    // Slices are less than drinks and salt, so divide the slices by the number of friends
    else if (y < x && y == z)
        *out = y / n;
    // Salt is less than drinks and slices, so divide the salt by the number of friends
    else if (z < x && z == y)
        *out = z / n;
    else
        *out = 0;
}
