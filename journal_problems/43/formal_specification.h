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

