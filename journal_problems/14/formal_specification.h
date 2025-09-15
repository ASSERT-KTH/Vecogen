/*@
logic integer SumTo{L}(int *a, integer n) = 
    (n <= 0) ? 0 : SumTo{L}(a, n - 1) + a[n - 1];
*/

/*@
requires a != \null;
  requires n >= 0;
  requires \valid_read(a + (0 .. n-1));
  requires \forall integer i; 0 <= i < n ==> 0 <= a[i] <= INT_MAX;
  requires SumTo(a, n) <= LLONG_MAX;
  decreases n;
  assigns \nothing;
  ensures \result == SumTo(a, n);
*/

