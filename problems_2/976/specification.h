#include <stdio.h>
/*  A. Hexadecimal's theorem
    Recently, a chaotic virus Hexadecimal advanced a new theorem which will shake the Universe. She thinks that each Fibonacci number can be represented as sum of three not necessary different Fibonacci numbers. Let's remember how Fibonacci numbers can be calculated. F 0 = 0 , F 1 = 1 , and all the next numbers are F i = F i - 2 + F i - 1 . So, Fibonacci numbers make a sequence of numbers: 0 , 1 , 1 , 2 , 3 , 5 , 8 , 13 , ... If you haven't run away from the PC in fear, you have to help the virus. Your task is to divide given Fibonacci number n by three not necessary different Fibonacci numbers or say that it is impossible.
*/

/*@
    requires 0 <= n <= 1000000000;
    assigns \nothing;
    ensures \result == 1;
*/

int output_1(int n);

/*@
    requires 0 <= n <= 1000000000;
    assigns \nothing;
    ensures \result == 1;
*/
int output_2(int n);

/*@
    requires 0 <= n <= 1000000000;
    assigns \nothing;
    ensures \result == 1;
*/
int output_3(int n);
