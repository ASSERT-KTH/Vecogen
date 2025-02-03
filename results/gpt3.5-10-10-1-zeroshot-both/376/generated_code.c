/*
    There exists an island called Arpa’s land, some beautiful girls live there, as ugly ones do. Mehrdad wants to become minister of Arpa’s land. Arpa has prepared an exam. Exam has only one question, given n , print the last digit of 1378^n . Mehrdad has become quite confused and wants you to help him. Please help, although it's a naive cheat.

    Input
    The input contains one integer n ( 0 ≤ n ≤ 10^9 ).

    Output
    Output single integer — the last digit of 1378^n .
*/
/*@ axiomatic power_function {
    axiom power_zero: \forall integer n; n == 0 ==> (long) \pow(1378, n) % 10 == 1;
    axiom power_mod_one: \forall integer n; n % 4 == 1 ==> (long) \pow(1378, n) % 10 == 8;
    axiom power_mod_two: \forall integer n; n % 4 == 2 ==> (long) \pow(1378, n) % 10 == 4;
    axiom power_mod_three: \forall integer n; n % 4 == 3 ==> (long) \pow(1378, n) % 10 == 2;
    axiom power_mod_zero: \forall integer n; n % 4 == 0 && n != 0 ==> (long) \pow(1378, n) % 10 == 6;
  }
*/

/*@
    requires \valid(out);
    requires 0 <= n <= 1000000000;
    assigns *out;
    ensures *out == (long) \pow(1378, n) % 10;
*/
void findLastDigitOfPower(int n, int *out)
{
    if (n == 0)
    {
        *out = 1;
    }
    else if (n % 4 == 1)
    {
        *out = 8;
    }
    else if (n % 4 == 2)
    {
        *out = 4;
    }
    else if (n % 4 == 3)
    {
        *out = 2;
    }
    else
    {
        *out = 6;
    }
}
