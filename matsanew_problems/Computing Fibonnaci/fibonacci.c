#include "fibonnaci.h"

/* Recursive implementation of Fibonacci function */
/*@
  requires 1 <= n <= 93;
  assigns \nothing;
  ensures fib_def(n, \result);
 */
ulong fib_recur(int n) {
    if (n == 1 || n == 2)
        return 1;
    else
        return fib_recur(n - 1) + fib_recur(n - 2);
}

/* Iterative implementation of Fibonacci function */
/*@
  requires 1 <= n <= 93;
  assigns \nothing;
  ensures fib_def(n, \result);
 */
ulong fib_iter(int n) {
    ulong a = 0, b = 1, next;
    for (int i = 1; i <= n; ++i) {
        next = a + b;
        a = b;
        b = next;
    }
    return a;
}
