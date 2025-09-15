/*@
requires 0 <= c <= 127;
  assigns \nothing;
  ensures 0 <= \result <= 127;
  ensures \result == (((c - 32) + 128) % 128);
*/

