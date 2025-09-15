/*@
requires base > 0;
  requires height > 0;
  requires length > 0;
  // Ensure that the product does not exceed the range representable in a long long,
  // and that the final result is within int range.
  requires (long long)base * height * length <= 2LL * INT_MAX;
  assigns \nothing;
  ensures \result == (base * height * length) / 2;
@
*/

