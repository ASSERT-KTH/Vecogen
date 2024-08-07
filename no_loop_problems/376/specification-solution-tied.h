/*
    There exists an island called Arpa’s land, some beautiful girls live there, as ugly ones do. Mehrdad wants to become minister of Arpa’s land. Arpa has prepared an exam. Exam has only one question, given n , print the last digit of 1378^n . Mehrdad has become quite confused and wants you to help him. Please help, although it's a naive cheat.

    Input
    The input contains one integer n ( 0 ≤ n ≤ 10^9 ).

    Output
    Output single integer — the last digit of 1378^n .
*/

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