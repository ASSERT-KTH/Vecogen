/*@
    requires \valid(out);
    requires 1 <= a <= 1000;
    requires 1 <= b <= 1000;
    requires 1 <= c <= 1000;
    assigns *out;
    ensures *out == 7 * \min(a / 1, \min(b / 2, c / 4));
*/
void calculateMaxFruitsForCompote(int a, int b, int c, int *out);