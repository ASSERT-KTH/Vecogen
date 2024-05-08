#include <stdio.h>

typedef unsigned long ulong;

/*@
  // Inductive definition of Fibonacci numbers
  inductive fib_def(integer n, ulong f)
  {
    case base1:
      fib_def(1, (ulong)1);

    case base2:
      fib_def(2, (ulong)1);

    case recursion:
      \forall integer i, ulong fi, fim1; (i >= 2 && fib_def(i-1, fim1) &&
      fib_def(i, fi)) ==> fib_def(i+1, (ulong)(fim1+fi));
  }
 */

/* Recursive Fibonacci with an emphasis on formal specification for termination */
/*@
  requires 1 <= n <= 93;
  assigns \nothing;
  ensures fib_def(n, \result);
  decreases n; // This clause is part of the ACSL specification for Frama-C to ensure termination
 */
ulong fib_recur(int n)
{
    // Base cases
    if (n == 1 || n == 2)
        return 1;
    // Recursive step. The 'decreases n;' clause in the specification ensures this call progresses towards termination.
    return fib_recur(n - 1) + fib_recur(n - 2);
}

/* Iterative Fibonacci */
/*@
  requires 1 <= n <= 93;
  assigns \nothing;
  ensures fib_def(n, \result);
 */
ulong fib_iter(int n)
{
    ulong a = 0, b = 1, c;
    if (n == 1)
        return b; // Handle n == 1 case upfront to simplify loop invariants
    /*@
      loop invariant 2 <= i <= n + 1;
      loop invariant fib_def(i - 1, b) && fib_def(i - 2, a);
      loop invariant a + b == c || i == 2;
      loop assigns a, b, c, i;
      loop variant n - i;
     */
    for (int i = 2; i <= n; i++)
    {
        c = a + b;
        a = b;
        b = c;
    }
    return b; // b holds the last calculated Fibonacci number
}