/*@ predicate is_perfect_square(integer x) = \exists integer n; n*n == x; @*/
/*@ predicate is_fibonacci(integer n) =
      is_perfect_square(5*n*n + 4) || is_perfect_square(5*n*n - 4) || n == 0; @*/

/*@
    requires \valid(out_1) && \valid(out_2) && \valid(out_3) && \separated(out_1, out_2) && \separated(out_1, out_3) && \separated(out_2, out_3);
    requires 0 <= n <= 1000000000;
    requires is_fibonacci(n);
    assigns *out_1, *out_2, *out_3;
    ensures *out_1 + *out_2 + *out_3 == n;
    ensures is_fibonacci(*out_1) && is_fibonacci(*out_2) && is_fibonacci(*out_3);
*/
void divideFibonacciNumberByThreeFibonacciNumbers(int n, int *out_1, int *out_2, int *out_3);
