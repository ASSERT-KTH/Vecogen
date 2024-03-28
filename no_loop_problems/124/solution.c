/*
    The HR manager was disappointed again. The last applicant failed the interview the same way as 24 previous ones. "Do I give such a hard task?" — the HR manager thought. "Just raise number 5 to the power of n and get last two digits of the number. Yes, of course, n can be rather big, and one cannot find the power using a calculator, but we need people who are able to think, not just follow the instructions." Could you pass the interview in the machine vision company in IT City?
 */

/*@
    requires \valid(out);
    requires 2 <= n <= 2 * 1000000000000000000;
    assigns *out;
    ensures *out == 25;
*/
void calculateLastTwoDigitsOfPowerOfFive(long n, int *out)
{
    *out = 25;
}