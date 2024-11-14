/*
    Recently, a chaotic virus Hexadecimal advanced a new theorem which will shake the Universe. She thinks that each Fibonacci number can be represented as sum of three not necessary different Fibonacci numbers. Let's remember how Fibonacci numbers can be calculated. F0 = 0 , F1 = 1 , and all the next numbers are Fi = Fi-2 + Fi-1 . So, Fibonacci numbers make a sequence of numbers: 0, 1, 1, 2, 3, 5, 8, 13, ... If you haven't run away from the PC in fear, you have to help the virus. Your task is to divide given Fibonacci number n by three not necessary different Fibonacci numbers or say that it is impossible.

    Input
    The input contains a single integer n (0 ≤ n < 10^9 ) — the number that should be represented by the rules described above. It is guaranteed that n is a Fibonacci number.

    Output
    Output consists of three required numbers: a, b and c . If there is no answer for the test you have to print " I'm too stupid to solve this problem " without the quotes. If there are multiple answers, print any of them. Examples
*/

/*@ predicate is_perfect_square(integer x) = \exists integer n; n*n == x; @*/
/*@ predicate is_fibonacci(integer n) =
      is_perfect_square(5*n*n + 4) || is_perfect_square(5*n*n - 4) || n == 0; @*/

/*@
    requires \valid(out1) && \valid(out2) && \valid(out3) && \separated(out1, out2) && \separated(out1, out3) && \separated(out2, out3);
    requires 0 <= n <= 1000000000;
    requires is_fibonacci(n);
    assigns *out1, *out2, *out3;
    ensures *out1 + *out2 + *out3 == n;
    ensures is_fibonacci(*out1) && is_fibonacci(*out2) && is_fibonacci(*out3);
*/
void divideFibonacciNumberByThreeFibonacciNumbers(int n, int *out1, int *out2, int *out3)
{
    *out1 = 0;
    *out2 = 0;
    *out3 = n;
}
