/*@
requires INT_MIN  <= a <= INT_MAX;
  requires INT_MIN  <= b <= INT_MAX;
  requires INT_MIN  <= c <= INT_MAX;
  requires LLONG_MIN <= 1LL*b*b <= LLONG_MAX;
  requires LLONG_MIN <= 4LL*a*c <= LLONG_MAX;
  assigns \nothing;
  ensures \result == ((1LL*b*b - 4LL*a*c) < 0);
*/