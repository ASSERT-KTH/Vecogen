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
    fibonacci_triple result = {-1, -1, -1};
    int fibs[45] = {0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987,
                    1597, 2584, 4181, 6765, 10946, 17711, 28657, 46368, 75025, 121393,
                    196418, 317811, 514229, 832040, 1346269, 2178309, 3524578, 5702887,
                    9227465, 14930352, 24157817, 39088169, 63245986, 102334155, 165580141,
                    267914296, 433494437, 701408733};

    int helper(int a, int b, int c) {
        if (a >= 45) return 0;
        if (b >= 45) return helper(a + 1, a + 1, a + 1);
        if (c >= 45) return helper(a, b + 1, b + 1);
        if (fibs[a] + fibs[b] + fibs[c] == n) {
            result.a = fibs[a];
            result.b = fibs[b];
            result.c = fibs[c];
            return 1;
        }
        return helper(a, b, c + 1);
    }

    if (n == 0) {
        result.a = 0;
        result.b = 0;
        result.c = 0;
    } else {
        helper(0, 0, 0);
    }

    return result;
}
