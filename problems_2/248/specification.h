/*  As Fast As Possible time
    On vacations n pupils decided to go on excursion and gather all together. They need to overcome the path with the length l meters. Each of the pupils will go with the speed equal to v 1 . To get to the excursion quickly, it was decided to rent a bus, which has seats for k people (it means that it can't fit more than k people at the same time) and the speed equal to v 2 . In order to avoid seasick, each of the pupils want to get into the bus no more than once . Determine the minimum time required for all n pupils to reach the place of excursion. Consider that the embarkation and disembarkation of passengers, as well as the reversal of the bus, take place immediately and this time can be neglected.
*/

/*@
    requires \valid(out);
    requires 1 <= n <= 10000;
    requires 1 <= l <= 1000000000;
    requires 1 <= v1 < v2 <= 1000000000;
    requires 1 <= k <= n;
    assigns *out;
    ensures *out >= 0;

*/
void problem(int n, int l, int v1, int v2, int k, int *out);
