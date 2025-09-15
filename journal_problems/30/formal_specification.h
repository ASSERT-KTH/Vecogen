/*@
requires n >= 0;
  requires ((long long)n * (n + 1) * (n + 2)) / 6 <= INT_MAX;
  assigns \nothing;
  ensures \result == n*(n+1)*(n+2)/6;
@
*/

