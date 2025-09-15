/*@
requires n > 0;
  requires \valid(a + (0 .. n-1));
  decreases n;
  assigns \nothing;
  ensures \forall size_t k; 0 <= k < n ==> \result <= a[k];
  ensures \exists size_t k; 0 <= k < n && a[k] == \result;
*/

