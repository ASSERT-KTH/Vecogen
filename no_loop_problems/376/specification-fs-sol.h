/*@
    requires \valid(out);
    requires 0 <= n <= 1000000000;
    assigns *out;
    behavior zero:
        ensures n == 0 ==> *out == 1;
    behavior one:
        ensures n % 4 == 1 ==> *out == 8;
    behavior two:
        ensures n % 4 == 2 ==> *out == 4;
    behavior three:
        ensures n % 4 == 3 ==> *out == 2;
    behavior four:
        ensures n % 4 == 0 && n != 0  ==> *out == 6;
*/
void findLastDigitOfPower(int n, int *out);