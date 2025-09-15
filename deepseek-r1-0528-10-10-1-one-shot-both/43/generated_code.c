typedef struct {
    int a;
    int b;
    int c;
} fibonacci_triple;

/*Recently, a chaotic virus Hexadecimal advanced a new theorem which will shake the Universe. She thinks that each Fibonacci number can be represented as sum of three not necessary different Fibonacci numbers. Let's remember how Fibonacci numbers can be calculated. F0 = 0 , F1 = 1 , and all the next numbers are Fi = Fi-2 + Fi-1 . So, Fibonacci numbers make a sequence of numbers: 0, 1, 1, 2, 3, 5, 8, 13, ... If you haven't run away from the PC in fear, you have to help the virus. Your task is to divide given Fibonacci number n by three not necessary different Fibonacci numbers or say that it is impossible.

    Input
    The input contains a single integer n (0 <= n < 10^9 ) — the number that should be represented by the rules described above. It is guaranteed that n is a Fibonacci number.

    Output
    Output consists of three required numbers: a, b and c . If there is no answer output -1 in each variable. If there are multiple answers, print any of them.
*/

/*@
predicate is_perfect_square(integer x) = \exists integer n; n*n == x; @
*/

/*@
predicate is_fibonacci(integer n) =
      is_perfect_square(5*n*n + 4) || is_perfect_square(5*n*n - 4) || n == 0; @
*/

/*@
requires 0 <= n <= 1000000000;
    requires is_fibonacci(n);
    assigns \nothing;
    ensures \result.a + \result.b + \result.c == n;
    ensures is_fibonacci(\result.a) && is_fibonacci(\result.b) && is_fibonacci(\result.c);
@
*/

fibonacci_triple divideFibonacciNumberByThreeFibonacciNumbers(int n) {
    fibonacci_triple result;
    result.a = n;
    result.b = 0;
    result.c = 0;
    return result;
}
