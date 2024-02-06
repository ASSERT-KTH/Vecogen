#include "fibonnaci.h"

/* Recursive implementation of Fibonacci function */
/*@
  requires 1 <= n <= 93;
  assigns \nothing;
  ensures fib_def(n, \result);
 */
ulong fib_recur(int n) {
    if (n <= 2)
        return 1;
    else
        return fib_recur_helper(n, 1, 1, 1);
}

/* Helper function for recursive implementation */
/*@
  requires 2 <= n <= 93;
  requires 1 <= i <= n;
  assigns \nothing;
  ensures fib_def(i, \result);
 */
ulong fib_recur_helper(int n, int i, ulong a, ulong b) {
    //@ assert 1 <= i <= n;
    if (i == n)
        return b;
    else {
        //@ assert 1 <= i < n;
        //@ assert fib_def(i, a);
        //@ assert fib_def(i+1, b);
        return fib_recur_helper(n, i + 1, b, a + b);
    }
}

/* Iterative implementation of Fibonacci function */
/*@
  requires 1 <= n <= 93;
  assigns \nothing;
  ensures fib_def(n, \result);
 */
ulong fib_iter(int n) {
    ulong a = 0, b = 1, next;
    /*@ loop invariant 1 <= i <= n;
        loop invariant fib_def(i, a);
        loop invariant fib_def(i+1, b);
        loop assigns i, a, b, next;
        loop variant n - i;
    */
    for (int i = 1; i < n; ++i) {
        next = a + b;
        a = b;
        b = next;
    }
    return b;
}
