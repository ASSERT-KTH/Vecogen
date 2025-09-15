/*@
requires baseEdge > 0;
  requires height > 0;
  requires (long long)baseEdge * baseEdge + 2LL * baseEdge * height <= INT_MAX;
  assigns \nothing;
  ensures \result == baseEdge * baseEdge + 2 * baseEdge * height;
@
*/

