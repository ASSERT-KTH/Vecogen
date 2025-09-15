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
    if (x < 0) return false;
    int s = (int)sqrt((double)x);
    return s * s == x;
}

bool isFibonacci(int n) {
    return isPerfectSquare(5 * n * n + 4) || isPerfectSquare(5 * n * n - 4) || n == 0;
}

fibonacci_triple search(int n, int i, int f1, int f2, int f3) {
    if (i < 0) return (fibonacci_triple) {-1, -1, -1};
    if (f1 + f2 + f3 == n) return (fibonacci_triple) {f1, f2, f3};
    
    if (f1 + f2 + f3 < n) {
        int f_next = f2 + f3;
        return search(n, i - 1, f2, f3, f_next);
    }

    if (f1 + f2 + f3 > n) {
        if (f3 > 0) return search(n, i, f1, f2, f3 - 1);
        else if (f2 > 0) return search(n, i, f1, f2 - 1, f3);
        else return search(n, i, f1 - 1, f2, f3);
    }

    return (fibonacci_triple) {-1, -1, -1};
}

fibonacci_triple divideFibonacciNumberByThreeFibonacciNumbers(int n) {
    if (n == 0) return (fibonacci_triple) {0, 0, 0};
    if (n == 1) return (fibonacci_triple) {0, 0, 1};

    return search(n, 44, 0, 0, 1); // Fibonacci sequence doesn't go beyond 44 for numbers < 10^9
}
