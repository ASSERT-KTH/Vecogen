/*@
logic integer SumTrue(bool *a, int n) =
    (n == 0 ? 0
             : SumTrue(a, (int)(n - 1)) + (a[n - 1] ? 1 : 0));
*/

/*@
requires \valid(a + (0 .. n-1));
  requires 0 <= n;
  decreases n;
  assigns \nothing;
  ensures \result == SumTrue(a, n);
  ensures n == 0 ==> \result == 0;
  ensures n > 0 ==> \result == SumTrue(a, (int)(n - 1)) + (a[n - 1] ? 1 : 0);
  ensures \result  <= n;
*/

