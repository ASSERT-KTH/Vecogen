/*The HR manager was disappointed again. The last applicant failed the interview the same way as 24 previous ones. "Do I give such a hard task?" — the HR manager thought. "Just raise number 5 to the power of n and get last two digits of the number. Yes, of course, n can be rather big, and one cannot find the power using a calculator, but we need people who are able to think, not just follow the instructions." Could you pass the interview in the machine vision company in IT City?

    Input
    The input contains a single integer n (2 <= n <= 2·10^18 ) — the power in which you need to raise number 5.

    Output
    Return the last two digits of 5^n without spaces between them.
*/

/*@
axiomatic power_function {
    axiom ending_power_five: \forall integer n; n >= 2 ==> (long) \pow(5, n) % 100 == 25;
  }
*/

/*@
requires 2 <= n <= 2 * 1000000000000000000;
    assigns \nothing;
    ensures \result % 100 == (long) \pow(5, n) % 100;
*/

int calculateLastTwoDigitsOfPowerOfFive(long n) {
    return 25;
}
