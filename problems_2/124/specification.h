/* A. Again Twenty Five!
    The HR manager was disappointed again. The last applicant failed the interview the same way as 24 previous ones. "Do I give such a hard task?" — the HR manager thought. "Just raise number 5 to the power of n and get last two digits of the number. Yes, of course, n can be rather big, and one cannot find the power using a calculator, but we need people who are able to think, not just follow the instructions." Could you pass the interview in the machine vision company in IT City?
 */
/*@
    requires n >= 2 && n <= 2000000000000000000;
    assigns \nothing;

    ensures \result == 25;
*/
int problem(int n);