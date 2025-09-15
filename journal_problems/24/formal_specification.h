/*@ predicate InRange(int *a, integer len, integer lo, integer hi) =
      0 <= lo <= hi <= len &&
      (len == 0 || \valid(a + (0 .. len-1)));
*/

/*@ logic integer sum_interval(int *a, integer lo, integer hi) =
      (hi <= lo) ? 0 : sum_interval(a, lo, hi - 1) + a[hi - 1];
*/

/*@
  requires 0 <= len;
  requires 0 <= start <= end <= len;
  requires InRange(a, len, start, end);
  requires \forall integer x; 0 <= x < len ==> 0 <= a[x] <= 100;
  requires sum_interval(a, (int) 0, (int) (len)) <= INT_MAX;
  requires end - start <= INT_MAX / 100;
  decreases end - start;
  assigns \nothing;
  ensures \result == sum_interval(a, start, end);
  ensures (start == end) ==> (\result == 0);
  ensures start < end  
    ==> \result == sum_interval(a, start, (int)(end - 1)) + a[(int)(end - 1)];
  ensures 0 <= \result <= 100 * (end - start);
*/