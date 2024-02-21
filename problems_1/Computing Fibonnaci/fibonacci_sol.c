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
ulong fib_recur(int n)
{
    if (n == 1 || n == 2)
        return 1;

    return fib_recur(n - 2) + fib_recur(n - 1);
}

/*@
  requires 1 <= n <= 93;
  assigns \nothing;
  ensures fib_def(n, \result);
 */
ulong fib_iter(int n)
{
    int i;
    ulong fi, fim1; /* read "fim1" as "F i minus 1" */

    if (n == 1 || n == 2)
        return 1;

    i = 2;
    fim1 = 1;
    fi = 1;

    /*@
      loop assigns i, fi, fim1;
      loop invariant 2 <= i <= n;
      loop invariant fib_def(i, fi) && fib_def(i-1, fim1);
      loop variant n - i;
     */
    while (i < n)
    {
        ulong newfi = fim1 + fi;
        fim1 = fi;
        fi = newfi;
        i = i + 1;
    }

    return fi;
}
