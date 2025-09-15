/*@
requires \valid_read(arr + (0 .. len - 1));
  requires 1 <= k <= len;
  assigns \nothing;
  ensures \result == arr[k - 1];
@
*/

