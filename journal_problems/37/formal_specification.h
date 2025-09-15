/*@
requires len > 0;
  requires n >= 0;
  requires index >= 0 && index < len;
  requires \valid(l + (0 .. len-1));
  assigns \nothing;
  ensures \result == l[(index - (n % len) + len) % len];
@
*/

