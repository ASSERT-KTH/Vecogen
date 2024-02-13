/* Method fib_recur() computes the n-th Fibonacci number F(n) using recursive calls,
   which is an inefficent approach.
   Method fib_iter() computes F(n) by iteratively computing all Fibonacci numbers
   till the n-th one.
   It is assumed that ulong has 64-bits; so the highest F(n) it can hold is F(93).
 */

typedef unsigned long ulong;

/*@
  // Inductive definition of Fibonacci numbers
  inductive fib_def(integer n, ulong f)
  {
    case base1:
      fib_def(1, (ulong)1);

    case base2:
      fib_def(2, (ulong)1);

    // read "fim1" as "F i minus 1".
    case recursion:
      \forall integer i, ulong fi, fim1; (i >= 2 && fib_def(i-1, fim1) &&
      fib_def(i, fi)) ==> fib_def(i+1, (ulong)(fim1+fi));
  }
 */

/*@
  requires 1 <= n <= 93;
  assigns \nothing;
  ensures fib_def(n, \result);
 */
ulong fib_recur(int n);

/*@
  requires 1 <= n <= 93;
  assigns \nothing;
  ensures fib_def(n, \result);
 */
ulong fib_iter(int n);