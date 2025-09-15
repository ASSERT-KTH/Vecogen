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
    if (n == 0) return (fibonacci_triple){0, 0, 0}; 
    if (n == 1) return (fibonacci_triple){0, 1, 0}; 
    if (n == 2) return (fibonacci_triple){1, 1, 0}; 

    int fib1 = 0, fib2 = 1, fibNext;
    while (1) {
        fibNext = fib1 + fib2;
        if (fibNext > n) break;
        fib1 = fib2;
        fib2 = fibNext;
    }   

    if (n == fib1) return (fibonacci_triple){fib1, 0, 0};
    if (n == fib2) return (fibonacci_triple){fib2, 0, 0};
    
    for (int i = 0; i <= fib2; ++i) {
        for (int j = 0; j <= fib2; ++j) {
            int k = n - i - j;
            if (k >= 0 && is_fibonacci(i) && is_fibonacci(j) && is_fibonacci(k)) {
                return (fibonacci_triple){i, j, k};
            }
        }
    }
    
    return (fibonacci_triple){-1, -1, -1};
}
