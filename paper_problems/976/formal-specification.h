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