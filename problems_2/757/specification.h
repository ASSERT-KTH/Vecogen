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
int problem(int n, int k, int l, int c, int d, int p, int nl, int np);