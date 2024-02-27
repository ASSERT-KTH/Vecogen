/*  B. Mischievous Mess Makers
    It is a balmy spring afternoon, and Farmer John's n cows are ruminating about link-cut cacti in their stalls. The cows, labeled 1 through n , are arranged so that the i -th cow occupies the i -th stall from the left. However, Elsie, after realizing that she will forever live in the shadows beyond Bessie's limelight, has formed the Mischievous Mess Makers and is plotting to disrupt this beautiful pastoral rhythm. While Farmer John takes his k minute long nap, Elsie and the Mess Makers plan to repeatedly choose two distinct stalls and swap the cows occupying those stalls, making no more than one swap each minute. Being the meticulous pranksters that they are, the Mischievous Mess Makers would like to know the maximum messiness attainable in the k minutes that they have. We denote as p i the label of the cow in the i -th stall. The messiness of an arrangement of cows is defined as the number of pairs ( i , j ) such that i < j and p i > p j .
*/

/*@
    requires \valid(out);
    requires 1 <= n <= 100000;
    requires 1 <= k <= 100000;
    assigns *out;
    behavior k_larger_or_equal_n_divided_by_two:
        assumes k >= n / 2;
        ensures *out == (n * (n - 1)) / 2;
    behavior k_smaller_than_n_divided_by_two:
        assumes k < n / 2;
        ensures *out ==  k * (2 * n - 1 - 2 * k);
*/
void problem(long n, int k, long *out);