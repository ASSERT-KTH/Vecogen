/*
    This winter is so cold in Nvodsk! A group of n friends decided to buy k bottles of a soft drink called "Take-It-Light" to warm up a bit. Each bottle has l milliliters of the drink. Also they bought c limes and cut each of them into d slices. After that they found p grams of salt. To make a toast, each friend needs nl milliliters of the drink, a slice of lime and np grams of salt. The friends want to make as many toasts as they can, provided they all drink the same amount. How many toasts can each friend make?

    Input
    The input contains positive integers n, k, l, c, d, p, nl, np, not exceeding 1000 and no less than 1 . The numbers are separated by exactly one space.

    Output
    Output a single integer — the number of toasts each friend can make.
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
    ensures *out >= 0;
    ensures limes_are_enough: c * d >= *out * n;
    ensures drinks_are_enough: k * l >= *out * n * nl;
    ensures salts_are_enough: p >= *out * n * np;
    ensures largest_solution: (\forall integer x; x > *out ==> c * d < x * n || k * l < x * n * nl || p < x * n * np);
*/
void calculateMaximumToastsPerFriend(int n, int k, int l, int c, int d, int p, int nl, int np, int *out) {
    int total_drink_volume = k * l;
    int total_lime_slices = c * d;
    int max_toasts_with_drink = total_drink_volume / (n * nl);
    int max_toasts_with_limes = total_lime_slices / n;
    int max_toasts_with_salt = p / (n * np);

    int max_toasts = max_toasts_with_drink;
    if (max_toasts > max_toasts_with_limes) {
        max_toasts = max_toasts_with_limes;
    }
    if (max_toasts > max_toasts_with_salt) {
        max_toasts = max_toasts_with_salt;
    }

    *out = max_toasts;
}
