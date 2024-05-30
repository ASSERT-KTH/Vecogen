/*@
    requires \valid(out);
    requires 1 <= a <= 1000000000;
    requires 1 <= b <= 1000000000;
    requires 1 <= c <= 1000000000;
    requires 1 <= d <= 1000000000;
    assigns *out;
    ensures *out == 3 - (int) (a != b) - (int) (a != c && b != c) - (int) (a != d && b != d && c != d);
*/

void minimumHorseshoesNeeded(int a, int b, int c, int d, int *out);