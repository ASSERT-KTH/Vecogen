/*@
requires n >= 0;
  // Ensure that the computation does not overflow the int range.
  // (2LL * n - 1LL) is computed in long long arithmetic.
  requires (long long)n * (2LL * n - 1LL) <= INT_MAX;
  
  assigns \nothing;
  
  ensures \result == n * (2 * n - 1);
*/

