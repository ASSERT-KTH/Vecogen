/*@
    requires \valid(out);
    requires d1 > 1 && d1 <= 100000000;
    requires d2 > 1 && d2 <= 100000000;
    requires d3 > 1 && d3 <= 100000000;
    assigns *out;
    ensures *out == \min(2 * d1 + 2 * d2, \min(d1 + d2 + d3, \min(2 * d1 + 2 * d3, 2 * d2 + 2 * d3)));
*/
void calculateMinimumDistanceForShopping(int d1, int d2, int d3, int *out);